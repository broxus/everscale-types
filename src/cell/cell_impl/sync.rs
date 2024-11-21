use std::alloc::Layout;
use std::borrow::Borrow;
use std::mem::offset_of;
use std::sync::atomic::AtomicUsize;
use std::sync::{Arc, OnceLock, Weak};

use super::{
    ordinary, pruned, EmptyOrdinaryCell, FullOrdinaryCellHeader, HeaderWithData, LibraryReference,
    OrdinaryCell, OrdinaryCellHeader, PrunedBranch, PrunedBranchHeader, VirtualCell, ALL_ONES_CELL,
    ALL_ZEROS_CELL,
};
use crate::cell::cell_context::{CellContext, CellParts, LoadMode};
use crate::cell::{CellFamily, CellImpl, CellType, DynCell, HashBytes};
use crate::error::Error;
use crate::util::{ArrayVec, TryAsMut};

/// Thread-safe cell.
#[derive(Clone, Eq)]
#[repr(transparent)]
pub struct Cell(pub(crate) CellInner);

/// Inner representation of the cell.
pub type CellInner<T = DynCell> = Arc<T>;

impl Cell {
    /// Unwraps the root cell from the usage tracking.
    #[inline]
    pub fn untrack(self) -> Self {
        self.0.untrack()
    }

    /// Creates a new [`WeakCell`] reference to this cell.
    pub fn downgrade(this: &Cell) -> WeakCell {
        WeakCell(Arc::downgrade(&this.0))
    }
}

impl Default for Cell {
    #[inline]
    fn default() -> Self {
        Cell::empty_cell()
    }
}

impl std::ops::Deref for Cell {
    type Target = DynCell;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl AsRef<DynCell> for Cell {
    #[inline]
    fn as_ref(&self) -> &DynCell {
        self.0.as_ref()
    }
}

impl Borrow<DynCell> for Cell {
    #[inline]
    fn borrow(&self) -> &DynCell {
        self.0.borrow()
    }
}

impl std::fmt::Debug for Cell {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self.0.as_ref(), f)
    }
}

impl PartialEq for Cell {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ref() == other.0.as_ref()
    }
}

impl From<Cell> for CellInner {
    #[inline]
    fn from(value: Cell) -> Self {
        value.0
    }
}

impl From<CellInner> for Cell {
    #[inline]
    fn from(value: CellInner) -> Self {
        Self(value)
    }
}

impl<T: CellImpl + Send + Sync + 'static> From<CellInner<T>> for Cell {
    #[inline]
    fn from(value: CellInner<T>) -> Self {
        Self(value as CellInner)
    }
}

impl CellFamily for Cell {
    type EmptyCellContext = EmptyCellContext;

    fn empty_cell() -> Cell {
        static EMPTY_CELL: OnceLock<Cell> = OnceLock::new();
        EMPTY_CELL
            .get_or_init(|| Cell(Arc::new(EmptyOrdinaryCell)))
            .clone()
    }

    #[inline]
    fn empty_cell_ref() -> &'static DynCell {
        &EmptyOrdinaryCell
    }

    #[inline]
    fn empty_context() -> Self::EmptyCellContext {
        EmptyCellContext
    }

    #[inline]
    fn all_zeros_ref() -> &'static DynCell {
        &ALL_ZEROS_CELL
    }

    #[inline]
    fn all_ones_ref() -> &'static DynCell {
        &ALL_ONES_CELL
    }

    fn virtualize(cell: Cell) -> Cell {
        let descriptor = cell.as_ref().descriptor();
        if descriptor.level_mask().is_empty() {
            cell
        } else {
            Cell(Arc::new(VirtualCell(cell)))
        }
    }
}

impl<T: ?Sized> TryAsMut<T> for Arc<T> {
    #[inline]
    fn try_as_mut(&mut self) -> Option<&mut T> {
        Arc::get_mut(self)
    }
}

impl TryAsMut<DynCell> for Cell {
    #[inline]
    fn try_as_mut(&mut self) -> Option<&mut DynCell> {
        Arc::get_mut(&mut self.0)
    }
}

/// A non-owning reference to a [`Cell`].
#[derive(Clone)]
#[repr(transparent)]
pub struct WeakCell(Weak<DynCell>);

impl WeakCell {
    /// Attempts to upgrade the `WeakCell` to a [`Cell`],
    /// extending the lifetime of the data.
    ///
    /// Returns [`None`] if the inner value has since been dropped.
    #[inline]
    pub fn upgrade(&self) -> Option<Cell> {
        self.0.upgrade().map(Cell)
    }
}

/// Empty context for thread-safe cells.
#[derive(Debug, Default, Clone, Copy)]
pub struct EmptyCellContext;

impl CellContext for EmptyCellContext {
    fn finalize_cell(&mut self, ctx: CellParts) -> Result<Cell, Error> {
        let hashes = ok!(ctx.compute_hashes());
        // SAFETY: ctx now represents a well-formed cell
        Ok(unsafe { make_cell(ctx, hashes) })
    }

    #[inline]
    fn load_cell(&mut self, cell: Cell, _: LoadMode) -> Result<Cell, Error> {
        Ok(cell)
    }

    #[inline]
    fn load_dyn_cell<'a>(&mut self, cell: &'a DynCell, _: LoadMode) -> Result<&'a DynCell, Error> {
        Ok(cell)
    }
}

unsafe fn make_cell(ctx: CellParts, hashes: ArrayVec<(HashBytes, u16), 4>) -> Cell {
    match ctx.descriptor.cell_type() {
        CellType::PrunedBranch => {
            debug_assert!(hashes.len() == 1);
            let repr = hashes.get_unchecked(0);

            make_pruned_branch(
                PrunedBranchHeader {
                    repr_hash: repr.0,
                    level: ctx.descriptor.level_mask().level(),
                    descriptor: ctx.descriptor,
                },
                ctx.data,
            )
        }
        CellType::LibraryReference => {
            debug_assert!(hashes.len() == 1);
            let repr = hashes.get_unchecked(0);

            debug_assert!(ctx.descriptor.byte_len() == 33);
            debug_assert!(ctx.data.len() == 33);

            Cell(Arc::new(LibraryReference {
                repr_hash: repr.0,
                descriptor: ctx.descriptor,
                data: *(ctx.data.as_ptr() as *const [u8; 33]),
            }))
        }
        CellType::Ordinary if ctx.descriptor.d1 == 0 && ctx.descriptor.d2 == 0 => {
            Cell(Arc::new(EmptyOrdinaryCell))
        }
        _ => {
            let len = hashes.len();

            let base = OrdinaryCellHeader {
                bit_len: ctx.bit_len,
                #[cfg(feature = "stats")]
                stats: ctx.stats,
                descriptor: ctx.descriptor,
                references: ctx.references.into_inner(),
                without_first: false,
            };

            match len {
                1 => make_ordinary_cell::<1>(base.into_full(hashes), ctx.data),
                2 => make_ordinary_cell::<2>(base.into_full(hashes), ctx.data),
                3 => make_ordinary_cell::<3>(base.into_full(hashes), ctx.data),
                4 => make_ordinary_cell::<4>(base.into_full(hashes), ctx.data),
                _ => unreachable!(),
            }
        }
    }
}

/// Constructs an `ArcCell` from well-formed cell header and data.
///
/// # Safety
///
/// The following must be true:
/// - Header references array must be consistent with the descriptor.
/// - Data length in bytes must be in range 0..=128.
unsafe fn make_ordinary_cell<const H: usize>(
    header: FullOrdinaryCellHeader<H>,
    data: &[u8],
) -> Cell {
    // Clamp data to 0..=128 bytes range
    let raw_data_len = data.len();
    debug_assert!(raw_data_len <= 128);

    // Compute nearest target data length and vtable
    let (target_data_len, vtable) = if raw_data_len == 0 {
        (0, const { ordinary::VTABLES[H - 1][0] })
    } else {
        let len = std::cmp::max(raw_data_len, 8).next_power_of_two();
        let vtable =
            *const { ordinary::VTABLES[H - 1] }.get_unchecked(1 + len.trailing_zeros() as usize);
        (len, vtable)
    };
    debug_assert!(raw_data_len <= target_data_len);

    // Compute object layout
    let arc_data_offset = const {
        type EmptyCell<const H: usize> = OrdinaryCell<H, 0>;

        offset_of!(ArcInner<usize, EmptyCell<H>>, obj) + offset_of!(EmptyCell<H>, data)
    };

    let align = const {
        type InnerOrdinaryCell<const H: usize, const N: usize> =
            ArcInner<AtomicUsize, OrdinaryCell<H, N>>;

        let align = std::mem::align_of::<InnerOrdinaryCell<H, 0>>();
        assert!(
            align == std::mem::align_of::<InnerOrdinaryCell<H, 8>>()
                && align == std::mem::align_of::<InnerOrdinaryCell<H, 16>>()
                && align == std::mem::align_of::<InnerOrdinaryCell<H, 32>>()
                && align == std::mem::align_of::<InnerOrdinaryCell<H, 64>>()
                && align == std::mem::align_of::<InnerOrdinaryCell<H, 128>>()
        );

        align
    };

    let size = (arc_data_offset + target_data_len + align - 1) & !(align - 1);
    let layout = Layout::from_size_align_unchecked(size, align).pad_to_align();

    // Make ArcCell
    make_arc_cell::<_, 0>(layout, header, data.as_ptr(), raw_data_len, vtable)
}

unsafe fn make_pruned_branch(header: PrunedBranchHeader, data: &[u8]) -> Cell {
    type EmptyCell = PrunedBranch<{ pruned::LENGTHS[0] }>;

    // Compute nearest target data length and vtable
    let data_len = PrunedBranchHeader::cell_data_len(header.level as usize);
    debug_assert!((1..=3).contains(&header.level));
    debug_assert_eq!(data_len, data.len());
    debug_assert_eq!(data_len, header.descriptor.byte_len() as usize);

    let vtable = *pruned::VTABLES.get_unchecked((header.level - 1) as usize);

    // Compute object layout
    type InnerPrunedBranch<const N: usize> = ArcInner<AtomicUsize, PrunedBranch<N>>;

    const ALIGN: usize = std::mem::align_of::<InnerPrunedBranch<{ pruned::LENGTHS[0] }>>();
    const _: () = assert!(
        ALIGN == std::mem::align_of::<InnerPrunedBranch<{ pruned::LENGTHS[1] }>>()
            && ALIGN == std::mem::align_of::<InnerPrunedBranch<{ pruned::LENGTHS[2] }>>()
    );

    const ARC_DATA_OFFSET: usize =
        offset_of!(ArcInner<usize, EmptyCell>, obj) + offset_of!(EmptyCell, data);

    let size = (ARC_DATA_OFFSET + data_len + ALIGN - 1) & !(ALIGN - 1);
    let layout = Layout::from_size_align_unchecked(size, ALIGN).pad_to_align();

    // Make ArcCell
    make_arc_cell::<PrunedBranchHeader, { pruned::LENGTHS[0] }>(
        layout,
        header,
        data.as_ptr(),
        data_len,
        vtable,
    )
}

#[inline]
unsafe fn make_arc_cell<H, const N: usize>(
    layout: Layout,
    header: H,
    data_ptr: *const u8,
    data_len: usize,
    vtable: *const (),
) -> Cell
where
    HeaderWithData<H, N>: CellImpl,
{
    // Allocate memory for the object
    let buffer = std::alloc::alloc(layout);
    if buffer.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    // Initialize object data
    let ptr = buffer as *mut ArcInner<AtomicUsize, HeaderWithData<H, N>>;
    std::ptr::write(std::ptr::addr_of_mut!((*ptr).strong), AtomicUsize::new(1));
    std::ptr::write(std::ptr::addr_of_mut!((*ptr).weak), AtomicUsize::new(1));
    std::ptr::write(std::ptr::addr_of_mut!((*ptr).obj.header), header);
    std::ptr::copy_nonoverlapping(
        data_ptr,
        std::ptr::addr_of_mut!((*ptr).obj.data) as *mut u8,
        data_len,
    );

    // Construct fat pointer with vtable info
    let data = std::ptr::addr_of!((*ptr).obj) as *const ();
    let ptr: *const DynCell = std::mem::transmute([data, vtable]);

    // Construct Arc
    Cell(Arc::from_raw(ptr))
}

/// Internal Arc representation.
#[repr(C)]
struct ArcInner<A, T: ?Sized> {
    strong: A,
    weak: A,
    obj: T,
}
