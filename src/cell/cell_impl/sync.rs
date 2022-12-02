use std::alloc::Layout;
use std::sync::atomic::AtomicUsize;
use std::sync::Arc;

use super::{
    EmptyOrdinaryCell, HeaderWithData, LibraryReference, OrdinaryCell, OrdinaryCellHeader,
    PrunedBranch, PrunedBranchHeader,
};
use crate::cell::finalizer::{Finalizer, PartialCell};
use crate::cell::{Cell, CellContainer, CellFamily, CellHash, CellType};

/// Thread-safe cell family
pub struct ArcCellFamily;

impl CellFamily for ArcCellFamily {
    type Container<T: ?Sized> = Arc<T>;
    type DefaultFinalizer = ArcCellFinalizer;

    fn empty_cell() -> CellContainer<Self> {
        Arc::new(EmptyOrdinaryCell)
    }

    fn default_finalizer() -> Self::DefaultFinalizer {
        ArcCellFinalizer
    }
}

/// Thread-safe cell
pub type ArcCell = CellContainer<ArcCellFamily>;

/// Thread-safe cell finalizer
#[derive(Clone, Copy)]
pub struct ArcCellFinalizer;

impl Finalizer<ArcCellFamily> for ArcCellFinalizer {
    fn finalize_cell(&mut self, ctx: PartialCell<ArcCellFamily>) -> Option<ArcCell> {
        let hashes = ctx.compute_hashes()?;
        // SAFETY: ctx now represents a well-formed cell
        unsafe { make_cell(ctx, hashes) }
    }
}

unsafe fn make_cell(
    ctx: PartialCell<ArcCellFamily>,
    hashes: Vec<(CellHash, u16)>,
) -> Option<ArcCell> {
    match ctx.descriptor.cell_type() {
        CellType::PrunedBranch => {
            debug_assert!(hashes.len() == 1);
            let repr = hashes.get_unchecked(0);

            Some(make_pruned_branch(
                PrunedBranchHeader {
                    repr_hash: repr.0,
                    repr_depth: repr.1,
                    level: ctx.descriptor.level_mask().level(),
                    descriptor: ctx.descriptor,
                },
                ctx.data,
            ))
        }
        CellType::LibraryReference => {
            debug_assert!(hashes.len() == 1);
            let repr = hashes.get_unchecked(0);

            debug_assert!(ctx.descriptor.byte_len() == 33);
            debug_assert!(ctx.data.len() == 33);

            Some(Arc::new(LibraryReference {
                repr_hash: repr.0,
                repr_depth: repr.1,
                descriptor: ctx.descriptor,
                data: *(ctx.data.as_ptr() as *const [u8; 33]),
            }))
        }
        CellType::Ordinary if ctx.descriptor.d1 == 0 && ctx.descriptor.d2 == 0 => {
            Some(Arc::new(EmptyOrdinaryCell))
        }
        _ => Some(make_ordinary_cell(
            OrdinaryCellHeader {
                bit_len: ctx.bit_len,
                stats: ctx.stats,
                hashes,
                descriptor: ctx.descriptor,
                references: ctx.references.into_inner(),
            },
            ctx.data,
        )),
    }
}

/// Constructs an `ArcCell` from well-formed cell header and data
///
/// # Safety
///
/// The following must be true:
/// - Header references array must be consistent with the descriptor.
/// - Data length in bytes must be in range 0..=128.
unsafe fn make_ordinary_cell(header: OrdinaryCellHeader<ArcCellFamily>, data: &[u8]) -> ArcCell {
    define_gen_vtable_ptr!((ArcCellFamily, const N: usize) => OrdinaryCell<ArcCellFamily, N>);

    const VTABLES: [*const (); 9] = [
        gen_vtable_ptr::<0>(),
        gen_vtable_ptr::<8>(), // 1, aligned to 8
        gen_vtable_ptr::<8>(), // 2, aligned to 8
        gen_vtable_ptr::<8>(), // 4, aligned to 8
        gen_vtable_ptr::<8>(),
        gen_vtable_ptr::<16>(),
        gen_vtable_ptr::<32>(),
        gen_vtable_ptr::<64>(),
        gen_vtable_ptr::<128>(),
    ];

    type EmptyCell = OrdinaryCell<ArcCellFamily, 0>;

    // Clamp data to 0..=128 bytes range
    let raw_data_len = data.len();
    debug_assert!(raw_data_len <= 128);

    // Compute nearest target data length and vtable
    let (target_data_len, vtable) = if raw_data_len == 0 {
        (0, VTABLES[0])
    } else {
        let len = std::cmp::max(raw_data_len, 8).next_power_of_two();
        let vtable = *VTABLES.get_unchecked(1 + len.trailing_zeros() as usize);
        (len, vtable)
    };
    debug_assert!(raw_data_len <= target_data_len);

    // Compute object layout
    type InnerOrdinaryCell<const N: usize> = ArcInner<AtomicUsize, OrdinaryCell<ArcCellFamily, N>>;

    const ALIGN: usize = std::mem::align_of::<InnerOrdinaryCell<0>>();
    const _: () = assert!(
        ALIGN == std::mem::align_of::<InnerOrdinaryCell<8>>()
            && ALIGN == std::mem::align_of::<InnerOrdinaryCell<16>>()
            && ALIGN == std::mem::align_of::<InnerOrdinaryCell<32>>()
            && ALIGN == std::mem::align_of::<InnerOrdinaryCell<64>>()
            && ALIGN == std::mem::align_of::<InnerOrdinaryCell<128>>()
    );

    const ARC_DATA_OFFSET: usize =
        offset_of!(ArcInner<usize, EmptyCell>, obj) + offset_of!(EmptyCell, data);

    let size = (ARC_DATA_OFFSET + target_data_len + ALIGN - 1) & !(ALIGN - 1);
    let layout = Layout::from_size_align_unchecked(size, ALIGN).pad_to_align();

    // Make ArcCell
    make_arc_cell::<OrdinaryCellHeader<ArcCellFamily>, 0>(
        layout,
        header,
        data.as_ptr(),
        raw_data_len,
        vtable,
    )
}

unsafe fn make_pruned_branch(header: PrunedBranchHeader, data: &[u8]) -> ArcCell {
    define_gen_vtable_ptr!((ArcCellFamily, const N: usize) => PrunedBranch<N>);

    const LENGTHS: [usize; 3] = [
        PrunedBranchHeader::cell_data_len(1),
        PrunedBranchHeader::cell_data_len(2),
        PrunedBranchHeader::cell_data_len(3),
    ];

    const VTABLES: [*const (); 3] = [
        gen_vtable_ptr::<{ LENGTHS[0] }>(),
        gen_vtable_ptr::<{ LENGTHS[1] }>(),
        gen_vtable_ptr::<{ LENGTHS[2] }>(),
    ];

    type EmptyCell = PrunedBranch<{ LENGTHS[0] }>;

    // Compute nearest target data length and vtable
    let data_len = PrunedBranchHeader::cell_data_len(header.level as usize);
    debug_assert!((1..=3).contains(&header.level));
    debug_assert_eq!(data_len, data.len());
    debug_assert_eq!(data_len, header.descriptor.byte_len() as usize);

    let vtable = *VTABLES.get_unchecked((header.level - 1) as usize);

    // Compute object layout
    type InnerPrunedBranch<const N: usize> = ArcInner<AtomicUsize, PrunedBranch<N>>;

    const ALIGN: usize = std::mem::align_of::<InnerPrunedBranch<{ LENGTHS[0] }>>();
    const _: () = assert!(
        ALIGN == std::mem::align_of::<InnerPrunedBranch<{ LENGTHS[1] }>>()
            && ALIGN == std::mem::align_of::<InnerPrunedBranch<{ LENGTHS[2] }>>()
    );

    const ARC_DATA_OFFSET: usize =
        offset_of!(ArcInner<usize, EmptyCell>, obj) + offset_of!(EmptyCell, data);

    let size = (ARC_DATA_OFFSET + data_len + ALIGN - 1) & !(ALIGN - 1);
    let layout = Layout::from_size_align_unchecked(size, ALIGN).pad_to_align();

    // Make ArcCell
    make_arc_cell::<PrunedBranchHeader, { LENGTHS[0] }>(
        layout,
        header,
        data.as_ptr(),
        data_len,
        vtable,
    )
}

#[inline]
unsafe fn make_arc_cell<H, const N: usize>(
    layout: std::alloc::Layout,
    header: H,
    data_ptr: *const u8,
    data_len: usize,
    vtable: *const (),
) -> ArcCell
where
    HeaderWithData<H, N>: Cell<ArcCellFamily>,
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
    let ptr: *const dyn Cell<ArcCellFamily> = std::mem::transmute([data, vtable]);

    // Construct Arc
    Arc::from_raw(ptr)
}

/// Internal Arc representation
#[repr(C)]
struct ArcInner<A, T: ?Sized> {
    strong: A,
    weak: A,
    obj: T,
}
