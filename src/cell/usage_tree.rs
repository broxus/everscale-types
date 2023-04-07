use std::marker::PhantomData;
use std::rc::{self, Rc};
use std::sync::{self, Arc, Mutex};

use super::cell_impl::VirtualCellWrapper;
use super::rc::{RcCell, RcCellFamily};
use super::sync::{ArcCell, ArcCellFamily};
use super::{Cell, CellContainer, CellDescriptor, CellFamily, CellHash};
use crate::util::TryAsMut;

#[cfg(feature = "stats")]
use super::CellTreeStats;

/// Rule for including cells in the usage tree.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum UsageTreeMode {
    /// Include cell on load.
    OnLoad,
    /// Include cell only when accessing references or data.
    OnDataAccess,
}

/// Usage tree for a family of cells.
pub struct UsageTree<C: CellFamily + Trackable> {
    state: C::SharedState,
}

impl<C: CellFamily + Trackable> UsageTree<C> {
    /// Creates a usage tree with the specified tracking mode.
    pub fn new(mode: UsageTreeMode) -> Self {
        Self {
            state: C::new_usage_tree_state(mode),
        }
    }

    /// Wraps the specified cell in a usage cell to keep track
    /// of the data or links being accessed.
    pub fn track(&self, cell: &CellContainer<C>) -> CellContainer<C> {
        self.state.as_ref().insert(cell, UsageTreeMode::OnLoad);
        <C as UsageTreeImpl>::wrap_cell(&self.state, cell.clone())
    }

    /// Returns `true` if the cell with the specified representation hash
    /// is present in this usage tree.
    pub fn contains(&self, repr_hash: &CellHash) -> bool {
        self.state.as_ref().contains(repr_hash)
    }
}

/// Cell family which can be used with [`UsageTree`].
pub trait Trackable: CellFamily + UsageTreeImpl {}

pub struct VisitedCell<C: CellFamily> {
    include: bool,
    _cell: CellContainer<C>,
}

pub struct UsageTreeState<C: UsageTreeImpl> {
    mode: UsageTreeMode,
    visited: C::VisitedCells,
    _cell_type: PhantomData<C>,
}

impl<C: UsageTreeImpl> UsageTreeState<C> {
    #[inline]
    fn insert(&self, cell: &CellContainer<C>, ctx: UsageTreeMode) {
        <C as UsageTreeImpl>::insert(&self.visited, cell, self.mode == ctx);
    }

    #[inline]
    fn contains(&self, repr_hash: &CellHash) -> bool {
        <C as UsageTreeImpl>::contains(&self.visited, repr_hash)
    }
}

pub trait UsageTreeImpl: CellFamily {
    type SharedState: AsRef<UsageTreeState<Self>> + Clone;
    type VisitedCells;

    fn new_usage_tree_state(mode: UsageTreeMode) -> Self::SharedState;

    fn wrap_cell(state: &Self::SharedState, cell: CellContainer<Self>) -> CellContainer<Self>;

    fn insert(visited: &Self::VisitedCells, cell: &CellContainer<Self>, include: bool);

    fn contains(visited: &Self::VisitedCells, repr_hash: &CellHash) -> bool;
}

impl Trackable for ArcCellFamily {}
impl UsageTreeImpl for ArcCellFamily {
    type SharedState = Arc<UsageTreeState<Self>>;
    type VisitedCells = Mutex<ahash::HashMap<CellHash, VisitedCell<Self>>>;

    fn new_usage_tree_state(mode: UsageTreeMode) -> Self::SharedState {
        Arc::new(UsageTreeState {
            mode,
            visited: Default::default(),
            _cell_type: PhantomData,
        })
    }

    fn wrap_cell(state: &Self::SharedState, cell: CellContainer<Self>) -> CellContainer<Self> {
        Arc::new(ArcUsageCell {
            cell,
            usage_tree: Arc::downgrade(state),
            children: [(); 4].map(|_| Default::default()),
        })
    }

    fn insert(visited: &Self::VisitedCells, cell: &CellContainer<Self>, include: bool) {
        let repr_hash = cell.repr_hash();

        let mut visited = visited.lock().expect("lock failed");

        if let Some(visited) = visited.get_mut(repr_hash) {
            visited.include |= include;
        } else {
            visited.insert(
                *repr_hash,
                VisitedCell {
                    include,
                    _cell: cell.clone(),
                },
            );
        }
    }

    fn contains(visited: &Self::VisitedCells, repr_hash: &CellHash) -> bool {
        let visited = visited.lock().expect("lock failed");
        if let Some(cell) = visited.get(repr_hash) {
            cell.include
        } else {
            false
        }
    }
}

impl Trackable for RcCellFamily {}
impl UsageTreeImpl for RcCellFamily {
    type SharedState = Rc<UsageTreeState<Self>>;
    type VisitedCells = std::cell::RefCell<ahash::HashMap<CellHash, VisitedCell<Self>>>;

    fn new_usage_tree_state(mode: UsageTreeMode) -> Self::SharedState {
        Rc::new(UsageTreeState {
            mode,
            visited: Default::default(),
            _cell_type: PhantomData,
        })
    }

    fn wrap_cell(state: &Self::SharedState, cell: CellContainer<Self>) -> CellContainer<Self> {
        Rc::new(RcUsageCell {
            cell,
            usage_tree: Rc::downgrade(state),
            children: Default::default(),
        })
    }

    fn insert(visited: &Self::VisitedCells, cell: &CellContainer<Self>, include: bool) {
        let repr_hash = cell.repr_hash();
        let mut visited = visited.borrow_mut();

        if let Some(visited) = visited.get_mut(repr_hash) {
            visited.include |= include;
        } else {
            visited.insert(
                *repr_hash,
                VisitedCell {
                    include,
                    _cell: cell.clone(),
                },
            );
        }
    }

    fn contains(visited: &Self::VisitedCells, repr_hash: &CellHash) -> bool {
        if let Some(cell) = visited.borrow().get(repr_hash) {
            cell.include
        } else {
            false
        }
    }
}

struct ArcUsageCell {
    cell: ArcCell,
    usage_tree: sync::Weak<UsageTreeState<ArcCellFamily>>,
    children: [once_cell::sync::OnceCell<Option<Arc<Self>>>; 4],
}

impl ArcUsageCell {
    fn load_reference(&self, index: u8) -> Option<&Arc<Self>> {
        if index < 4 {
            self.children[index as usize]
                .get_or_init(|| {
                    let child = self.cell.as_ref().reference_cloned(index)?;
                    if let Some(usage_tree) = self.usage_tree.upgrade() {
                        usage_tree.insert(&child, UsageTreeMode::OnLoad);
                    }

                    Some(Arc::new(ArcUsageCell {
                        cell: child.clone(),
                        usage_tree: self.usage_tree.clone(),
                        children: Default::default(),
                    }))
                })
                .as_ref()
        } else {
            None
        }
    }
}

impl Cell<ArcCellFamily> for ArcUsageCell {
    fn descriptor(&self) -> CellDescriptor {
        self.cell.as_ref().descriptor()
    }

    fn data(&self) -> &[u8] {
        if let Some(usage_tree) = self.usage_tree.upgrade() {
            usage_tree.insert(&self.cell, UsageTreeMode::OnDataAccess);
        }
        self.cell.as_ref().data()
    }

    fn bit_len(&self) -> u16 {
        self.cell.as_ref().bit_len()
    }

    fn reference(&self, index: u8) -> Option<&dyn Cell<ArcCellFamily>> {
        Some(self.load_reference(index)?.as_ref())
    }

    fn reference_cloned(&self, index: u8) -> Option<ArcCell> {
        Some(self.load_reference(index)?.clone())
    }

    fn virtualize(&self) -> &dyn Cell<ArcCellFamily> {
        VirtualCellWrapper::wrap(self)
    }

    fn hash(&self, level: u8) -> &CellHash {
        self.cell.as_ref().hash(level)
    }

    fn depth(&self, level: u8) -> u16 {
        self.cell.as_ref().depth(level)
    }

    fn take_first_child(&mut self) -> Option<ArcCell> {
        self.cell.try_as_mut()?.take_first_child()
    }

    fn replace_first_child(&mut self, parent: ArcCell) -> Result<ArcCell, ArcCell> {
        match self.cell.try_as_mut() {
            Some(cell) => cell.replace_first_child(parent),
            None => Err(parent),
        }
    }

    fn take_next_child(&mut self) -> Option<ArcCell> {
        self.cell.try_as_mut()?.take_next_child()
    }

    #[cfg(feature = "stats")]
    fn stats(&self) -> CellTreeStats {
        self.cell.as_ref().stats()
    }
}

struct RcUsageCell {
    cell: RcCell,
    usage_tree: rc::Weak<UsageTreeState<RcCellFamily>>,
    children: std::cell::UnsafeCell<[Option<Rc<Self>>; 4]>,
}

impl RcUsageCell {
    fn load_reference(&self, index: u8) -> Option<&Rc<Self>> {
        if index < 4 {
            let children = unsafe { &mut *self.children.get() };
            Some(match &mut children[index as usize] {
                Some(value) => value,
                slot @ None => {
                    let child = self.cell.as_ref().reference_cloned(index)?;
                    if let Some(usage_tree) = self.usage_tree.upgrade() {
                        usage_tree.insert(&child, UsageTreeMode::OnLoad);
                    }

                    slot.insert(Rc::new(RcUsageCell {
                        cell: child.clone(),
                        usage_tree: self.usage_tree.clone(),
                        children: Default::default(),
                    }))
                }
            })
        } else {
            None
        }
    }
}

impl Cell<RcCellFamily> for RcUsageCell {
    fn descriptor(&self) -> CellDescriptor {
        self.cell.as_ref().descriptor()
    }

    fn data(&self) -> &[u8] {
        if let Some(usage_tree) = self.usage_tree.upgrade() {
            usage_tree.insert(&self.cell, UsageTreeMode::OnDataAccess);
        }
        self.cell.as_ref().data()
    }

    fn bit_len(&self) -> u16 {
        self.cell.as_ref().bit_len()
    }

    fn reference(&self, index: u8) -> Option<&dyn Cell<RcCellFamily>> {
        Some(self.load_reference(index)?.as_ref())
    }

    fn reference_cloned(&self, index: u8) -> Option<RcCell> {
        Some(self.load_reference(index)?.clone())
    }

    fn virtualize(&self) -> &dyn Cell<RcCellFamily> {
        VirtualCellWrapper::wrap(self)
    }

    fn hash(&self, level: u8) -> &CellHash {
        self.cell.as_ref().hash(level)
    }

    fn depth(&self, level: u8) -> u16 {
        self.cell.as_ref().depth(level)
    }

    fn take_first_child(&mut self) -> Option<RcCell> {
        self.cell.try_as_mut()?.take_first_child()
    }

    fn replace_first_child(&mut self, parent: RcCell) -> Result<RcCell, RcCell> {
        match self.cell.try_as_mut() {
            Some(cell) => cell.replace_first_child(parent),
            None => Err(parent),
        }
    }

    fn take_next_child(&mut self) -> Option<RcCell> {
        self.cell.try_as_mut()?.take_next_child()
    }

    #[cfg(feature = "stats")]
    fn stats(&self) -> CellTreeStats {
        self.cell.as_ref().stats()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        println!("SIZE RC: {}", std::mem::size_of::<RcUsageCell>());
        println!("SIZE ARC: {}", std::mem::size_of::<ArcUsageCell>());
    }
}
