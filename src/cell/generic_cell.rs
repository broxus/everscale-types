use std::alloc::Layout;
use std::mem::MaybeUninit;
use std::sync::atomic::AtomicUsize;
use std::sync::Arc;

use super::finalizer::{Finalizer, PartialCell};
use super::{ArcCell, Cell, CellDescriptor, CellHash, CellTreeStats, CellType};

macro_rules! define_gen_vtable_ptr {
    (($($param:tt)*) => $($type:tt)*) => {
        const fn gen_vtable_ptr<$($param)*>() -> *const () {
            let uninit = std::mem::MaybeUninit::<$($type)*>::uninit();
            let fat_ptr = uninit.as_ptr() as *const dyn Cell;
            // SAFETY: "fat" pointer consists of two "slim" pointers
            let [_, vtable] = unsafe { std::mem::transmute::<_, [*const (); 2]>(fat_ptr) };
            vtable
        }
    };
}

#[derive(Clone, Copy)]
pub struct GenericCellFinalizer;

impl Finalizer<ArcCell> for GenericCellFinalizer {
    fn finalize_cell(&mut self, ctx: PartialCell<ArcCell>) -> Option<ArcCell> {
        let hashes = ctx.compute_hashes()?;

        match ctx.descriptor.cell_type() {
            CellType::PrunedBranch => {
                // SAFETY: references will be dropped with the header
                let header = unsafe {
                    let repr = hashes.get_unchecked(0);

                    PrunedBranchHeader {
                        repr_hash: repr.0,
                        repr_depth: repr.1,
                        level: ctx.descriptor.level_mask().level(),
                        descriptor: ctx.descriptor,
                    }
                };

                // SAFETY: `compute_hashes` ensures that data and references are well-formed
                Some(unsafe { make_pruned_branch(header, ctx.data) })
            }
            CellType::LibraryReference => {
                let repr = unsafe { hashes.get_unchecked(0) };

                Some(Arc::new(LibraryReference {
                    repr_hash: repr.0,
                    repr_depth: repr.1,
                    descriptor: ctx.descriptor,
                    data: unsafe { *(ctx.data.as_ptr() as *const [u8; 33]) },
                }))
            }
            _ => {
                // SAFETY: references will be dropped with the header
                let header = unsafe {
                    OrdinaryCellHeader {
                        bit_len: ctx.bit_len,
                        stats: ctx.stats,
                        hashes,
                        descriptor: ctx.descriptor,
                        references: ctx.references.into_inner(),
                    }
                };

                // SAFETY: `compute_hashes` ensures that data and references are well-formed
                Some(unsafe { make_ordinary_cell(header, ctx.data) })
            }
        }
    }
}

/// Constructs an `ArcCell` from well-formed cell header and data
///
/// # Safety
///
/// The following must be true:
/// - Header references array must be consistent with the descriptor.
/// - Data length in bytes must be in range 0..=128.
unsafe fn make_ordinary_cell(header: OrdinaryCellHeader<ArcCell>, data: &[u8]) -> ArcCell {
    define_gen_vtable_ptr!((const N: usize) => OrdinaryCell<[u8; N], ArcCell>);

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

    type EmptyCell = OrdinaryCell<[u8; 0], ArcCell>;

    // Clamp data to 0..=128 bytes range
    let raw_data_len = std::cmp::min(data.len(), 128) as u8;

    // Compute nearest target data length and vtable
    let (target_data_len, vtable) = if raw_data_len == 0 {
        (0, VTABLES[0])
    } else {
        let len = std::cmp::max(raw_data_len, 8).next_power_of_two() as usize;
        let vtable = *VTABLES.get_unchecked(1 + len.trailing_zeros() as usize);
        (len, vtable)
    };

    // Compute object layout
    const ALIGN: usize = std::mem::align_of::<ArcInner<AtomicUsize, EmptyCell>>();

    const ARC_DATA_OFFSET: usize =
        offset_of!(ArcInner<usize, EmptyCell>, obj) + offset_of!(EmptyCell, data);

    let size = (ARC_DATA_OFFSET + target_data_len + ALIGN - 1) & !(ALIGN - 1);
    let layout = Layout::from_size_align_unchecked(size, ALIGN).pad_to_align();

    // Make ArcCell
    make_arc_cell::<OrdinaryCellHeader<ArcCell>, [u8; 0]>(
        layout,
        header,
        data.as_ptr(),
        raw_data_len as usize,
        vtable,
    )
}

type OrdinaryCell<T, R> = HeaderWithData<OrdinaryCellHeader<R>, T>;

// TODO: merge VTables for different data array sizes
impl<const N: usize> Cell for OrdinaryCell<[u8; N], ArcCell> {
    fn descriptor(&self) -> CellDescriptor {
        self.header.descriptor
    }

    fn data(&self) -> &[u8] {
        let data_ptr = std::ptr::addr_of!(self.data) as *const u8;
        let data_len = self.header.descriptor.byte_len() as usize;
        // SAFETY: header is initialized
        unsafe { std::slice::from_raw_parts(data_ptr, data_len) }
    }

    fn bit_len(&self) -> u16 {
        self.header.bit_len
    }

    fn reference(&self, index: u8) -> Option<&dyn Cell> {
        Some(self.header.reference(index)?.as_ref())
    }

    fn reference_cloned(&self, index: u8) -> Option<ArcCell> {
        Some(self.header.reference(index)?.clone())
    }

    fn hash(&self, level: u8) -> CellHash {
        self.header.level_descr(level).0
    }

    fn depth(&self, level: u8) -> u16 {
        self.header.level_descr(level).1
    }

    fn stats(&self) -> CellTreeStats {
        self.header.stats
    }
}

struct OrdinaryCellHeader<R> {
    bit_len: u16,
    stats: CellTreeStats,
    hashes: Vec<(CellHash, u16)>,
    descriptor: CellDescriptor,
    references: [MaybeUninit<R>; 4],
}

impl<R> OrdinaryCellHeader<R> {
    fn level_descr(&self, level: u8) -> &(CellHash, u16) {
        let hash_index = hash_index(self.descriptor, level);
        // SAFETY: hash index is in range 0..=3
        unsafe { self.hashes.get_unchecked(hash_index as usize) }
    }

    fn reference(&self, i: u8) -> Option<&R> {
        if i < self.descriptor.reference_count() as u8 {
            // SAFETY: Item is initialized
            let child = unsafe { self.references.get_unchecked(i as usize).assume_init_ref() };
            Some(child)
        } else {
            None
        }
    }
}

impl<R> Drop for OrdinaryCellHeader<R> {
    fn drop(&mut self) {
        let references_ptr = self.references.as_mut_ptr() as *mut R;
        for i in 0..self.descriptor.reference_count() {
            // SAFETY: references were initialized
            unsafe { std::ptr::drop_in_place(references_ptr.add(i)) };
        }
    }
}

struct LibraryReference {
    repr_hash: CellHash,
    repr_depth: u16,
    descriptor: CellDescriptor,
    data: [u8; 33],
}

impl LibraryReference {
    const BIT_LEN: u16 = 8 + 256;
}

impl Cell for LibraryReference {
    fn descriptor(&self) -> CellDescriptor {
        self.descriptor
    }

    fn data(&self) -> &[u8] {
        self.data.as_ref()
    }

    fn bit_len(&self) -> u16 {
        LibraryReference::BIT_LEN
    }

    fn reference(&self, _: u8) -> Option<&dyn Cell> {
        None
    }

    fn reference_cloned(&self, _: u8) -> Option<ArcCell> {
        None
    }

    fn hash(&self, _: u8) -> CellHash {
        self.repr_hash
    }

    fn depth(&self, _: u8) -> u16 {
        self.repr_depth
    }

    fn stats(&self) -> CellTreeStats {
        CellTreeStats {
            bit_count: LibraryReference::BIT_LEN as u64,
            cell_count: 1,
        }
    }
}

unsafe fn make_pruned_branch(header: PrunedBranchHeader, data: &[u8]) -> ArcCell {
    define_gen_vtable_ptr!((const N: usize) => PrunedBranch<[u8; N]>);

    #[inline]
    const fn cell_data_len(level: usize) -> usize {
        2 + level * (32 + 2)
    }

    const VTABLES: [*const (); 3] = [
        gen_vtable_ptr::<{ cell_data_len(1) }>(),
        gen_vtable_ptr::<{ cell_data_len(2) }>(),
        gen_vtable_ptr::<{ cell_data_len(3) }>(),
    ];

    type BaseSlice = [u8; cell_data_len(1)];
    type EmptyCell = PrunedBranch<BaseSlice>;

    // Compute nearest target data length and vtable
    let data_len = cell_data_len(header.level as usize);
    let vtable = *VTABLES.get_unchecked((header.level - 1) as usize);

    // Compute object layout
    const ALIGN: usize = std::mem::align_of::<ArcInner<AtomicUsize, EmptyCell>>();

    const ARC_DATA_OFFSET: usize =
        offset_of!(ArcInner<usize, EmptyCell>, obj) + offset_of!(EmptyCell, data);

    let size = (ARC_DATA_OFFSET + data_len + ALIGN - 1) & !(ALIGN - 1);
    let layout = Layout::from_size_align_unchecked(size, ALIGN).pad_to_align();

    // Make ArcCell
    make_arc_cell::<PrunedBranchHeader, BaseSlice>(layout, header, data.as_ptr(), data_len, vtable)
}

type PrunedBranch<T> = HeaderWithData<PrunedBranchHeader, T>;

impl<const N: usize> Cell for PrunedBranch<[u8; N]> {
    fn descriptor(&self) -> CellDescriptor {
        self.header.descriptor
    }

    fn data(&self) -> &[u8] {
        let data_ptr = std::ptr::addr_of!(self.data) as *const u8;
        let data_len = self.header.descriptor.byte_len() as usize;
        // SAFETY: header is initialized
        unsafe { std::slice::from_raw_parts(data_ptr, data_len) }
    }

    fn bit_len(&self) -> u16 {
        // Pruned branch data is always aligned
        self.header.descriptor.byte_len() as u16 * 8
    }

    fn reference(&self, _: u8) -> Option<&dyn Cell> {
        None
    }

    fn reference_cloned(&self, _: u8) -> Option<ArcCell> {
        None
    }

    fn hash(&self, level: u8) -> CellHash {
        let hash_index = hash_index(self.header.descriptor, level);
        if hash_index == self.header.level {
            self.header.repr_hash
        } else {
            let offset = 2 + hash_index as usize * 32;
            let data_ptr = std::ptr::addr_of!(self.data) as *const u8;
            unsafe { *(data_ptr.add(offset) as *const [u8; 32]) }
        }
    }

    fn depth(&self, level: u8) -> u16 {
        let hash_index = hash_index(self.header.descriptor, level);
        if hash_index == self.header.level {
            self.header.repr_depth
        } else {
            let offset = 2 + self.header.level as usize * 32 + hash_index as usize * 2;
            let data_ptr = std::ptr::addr_of!(self.data) as *const u8;
            u16::from_be_bytes(unsafe { *(data_ptr.add(offset) as *const [u8; 2]) })
        }
    }

    fn stats(&self) -> CellTreeStats {
        aligned_leaf_stats(self.header.descriptor)
    }
}

struct PrunedBranchHeader {
    repr_hash: CellHash,
    repr_depth: u16,
    level: u8,
    descriptor: CellDescriptor,
}

fn hash_index(descriptor: CellDescriptor, level: u8) -> u8 {
    descriptor.level_mask().hash_index(level)
}

fn aligned_leaf_stats(descriptor: CellDescriptor) -> CellTreeStats {
    CellTreeStats {
        bit_count: descriptor.byte_len() as u64 * 8,
        cell_count: 1,
    }
}

/// Internal Arc representation
#[repr(C)]
struct ArcInner<A, T: ?Sized> {
    strong: A,
    weak: A,
    obj: T,
}

#[repr(C)]
struct HeaderWithData<H, T: ?Sized> {
    header: H,
    data: T,
}

#[inline]
unsafe fn make_arc_cell<H, T>(
    layout: std::alloc::Layout,
    header: H,
    data_ptr: *const u8,
    data_len: usize,
    vtable: *const (),
) -> ArcCell
where
    HeaderWithData<H, T>: Cell,
{
    // Allocate memory for the object
    let buffer = std::alloc::alloc(layout);
    if buffer.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    // Initialize object data
    let ptr = buffer as *mut ArcInner<AtomicUsize, HeaderWithData<H, T>>;
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
    let ptr: *const dyn Cell = std::mem::transmute([data, vtable]);

    // Construct Arc
    Arc::from_raw(ptr)
}
