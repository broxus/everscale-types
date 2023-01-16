use std::rc::{Rc, Weak};

use super::cell_impl::VirtualCellWrapper;
use super::rc::{RcCell, RcCellFamily};
use super::{Cell, CellDescriptor, CellHash};

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

/// Usage tree for the `Rc` family of cells.
pub struct RcUsageTree {
    state: Rc<RcUsageTreeState>,
}

impl RcUsageTree {
    /// Creates a usage tree with the specified tracking mode.
    pub fn new(mode: UsageTreeMode) -> Self {
        RcUsageTree {
            state: Rc::new(RcUsageTreeState {
                mode,
                visited: Default::default(),
            }),
        }
    }

    /// Wraps the specified cell in a usage cell to keep track
    /// of the data or links being accessed.
    pub fn track(&self, cell: &RcCell) -> RcCell {
        self.state.insert(cell, UsageTreeMode::OnLoad);
        Rc::new(RcUsageCell {
            cell: cell.clone(),
            usage_tree: Rc::downgrade(&self.state),
            children: Default::default(),
        })
    }

    /// Returns `true` if the cell with the specified representation hash
    /// is present in this usage tree.
    pub fn contains(&self, repr_hash: &CellHash) -> bool {
        if let Some(cell) = self.state.visited.borrow().get(repr_hash) {
            cell.include
        } else {
            false
        }
    }
}

struct RcUsageTreeState {
    mode: UsageTreeMode,
    visited: std::cell::RefCell<ahash::HashMap<CellHash, VisitedCell>>,
}

impl RcUsageTreeState {
    fn insert(self: &Rc<Self>, cell: &RcCell, ctx: UsageTreeMode) {
        let repr_hash = cell.repr_hash();
        let mut visited = self.visited.borrow_mut();

        if let Some(visited) = visited.get_mut(repr_hash) {
            visited.include |= self.mode == ctx;
        } else {
            visited.insert(
                *repr_hash,
                VisitedCell {
                    include: self.mode == ctx,
                    _cell: cell.clone(),
                },
            );
        }
    }
}

struct VisitedCell {
    include: bool,
    _cell: RcCell,
}

struct RcUsageCell {
    cell: RcCell,
    usage_tree: Weak<RcUsageTreeState>,
    children: std::cell::UnsafeCell<[Option<Rc<RcUsageCell>>; 4]>,
}

impl RcUsageCell {
    fn load_reference(&self, index: u8) -> Option<&Rc<RcUsageCell>> {
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
        println!("SIZE: {}", std::mem::size_of::<RcUsageCell>());
    }
}
