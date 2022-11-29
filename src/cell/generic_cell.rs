use std::alloc::Layout;
use std::mem::MaybeUninit;
use std::sync::atomic::AtomicUsize;
use std::sync::Arc;

use super::finalizer::{Finalizer, PartialCell};
use super::{ArcCell, Cell, CellDescriptor, CellHash, CellTreeStats};

#[derive(Clone, Copy)]
pub struct GenericCellFinalizer;

impl Finalizer<ArcCell> for GenericCellFinalizer {
    fn finalize_cell(&mut self, ctx: PartialCell<ArcCell>) -> std::io::Result<ArcCell> {
        let hashes = ok!(ctx.compute_hashes());

        // SAFETY: references will be dropped with the header
        let header = unsafe {
            CellHeader {
                stats: ctx.stats,
                hashes,
                descriptor: ctx.descriptor,
                references: ctx.references.into_inner(),
            }
        };

        // SAFETY: `compute_hashes` ensures that data and references are well-formed
        Ok(unsafe { make_generic_cell(header, ctx.data) })
    }
}

/// Constructs an `ArcCell` from well-formed cell header and data
///
/// # Safety
///
/// The following must be true:
/// - Header references array must be consistent with the descriptor.
/// - Data length in bytes must be in range 0..=128.
unsafe fn make_generic_cell(header: CellHeader<ArcCell>, data: &[u8]) -> ArcCell {
    /// Internal Arc representation
    #[repr(C)]
    struct ArcInner<A, T: ?Sized> {
        strong: A,
        weak: A,
        obj: T,
    }

    pub fn compute_data_len(len: usize) -> (usize, usize) {
        let len = std::cmp::min(len, 128) as u8;
        let target = if len == 0 {
            0
        } else {
            std::cmp::max(len, 8).next_power_of_two() as usize
        };
        (len as usize, target)
    }

    /// # Safety
    /// `len` must be a power of two
    pub unsafe fn get_vtable(len: usize) -> *const () {
        *VTABLES.get_unchecked(if len == 0 {
            0
        } else {
            1 + len.trailing_zeros() as usize
        })
    }

    const fn gen_vtable_ptr<const N: usize>() -> *const () {
        let uninit = std::mem::MaybeUninit::<GenericCell<[u8; N], ArcCell>>::uninit();
        let fat_ptr = uninit.as_ptr() as *const dyn Cell;
        // SAFETY: "fat" pointer consists of two "slim" pointers
        let [_, vtable] = unsafe { std::mem::transmute::<_, [*const (); 2]>(fat_ptr) };
        vtable
    }

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

    type EmptyCell = GenericCell<[u8; 0], ArcCell>;

    // Compute object layout
    const _: () = assert!(std::mem::size_of::<AtomicUsize>() == std::mem::size_of::<usize>());
    const ALIGN: usize = std::mem::align_of::<ArcInner<AtomicUsize, EmptyCell>>();

    const ARC_DATA_OFFSET: usize =
        offset_of!(ArcInner<usize, EmptyCell>, obj) + offset_of!(EmptyCell, data);

    let (raw_data_len, target_data_len) = compute_data_len(data.len());
    let size = (ARC_DATA_OFFSET + target_data_len + ALIGN - 1) & !(ALIGN - 1);
    let layout = Layout::from_size_align_unchecked(size, ALIGN).pad_to_align();

    // Allocate memory for the object
    let buffer = std::alloc::alloc(layout);
    if buffer.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    // Initialize object data
    let ptr = buffer as *mut ArcInner<AtomicUsize, EmptyCell>;
    std::ptr::write(std::ptr::addr_of_mut!((*ptr).strong), AtomicUsize::new(1));
    std::ptr::write(std::ptr::addr_of_mut!((*ptr).weak), AtomicUsize::new(1));
    std::ptr::write(std::ptr::addr_of_mut!((*ptr).obj.header), header);
    std::ptr::copy_nonoverlapping(
        data.as_ptr(),
        std::ptr::addr_of_mut!((*ptr).obj.data) as *mut u8,
        raw_data_len,
    );

    // Construct fat pointer with vtable info
    let data = std::ptr::addr_of!((*ptr).obj) as *const ();
    let vtable = get_vtable(target_data_len);
    let ptr: *const dyn Cell = std::mem::transmute([data, vtable]);

    // Construct Arc
    Arc::from_raw(ptr)
}

/// Tightly packed cell representation
#[repr(C)]
struct GenericCell<T: ?Sized, R> {
    header: CellHeader<R>,
    data: T,
}

// TODO: merge VTables for different data array sizes
impl<const N: usize> Cell for GenericCell<[u8; N], ArcCell> {
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
        // TODO: use short path and use only the last byte
        compute_bit_len(self.data(), self.header.descriptor.is_aligned())
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

struct CellHeader<R> {
    stats: CellTreeStats,
    hashes: Vec<(CellHash, u16)>,
    descriptor: CellDescriptor,
    references: [MaybeUninit<R>; 4],
}

impl<R> CellHeader<R> {
    fn level_descr(&self, level: u8) -> &(CellHash, u16) {
        let hash_index = self.descriptor.level_mask().hash_index(level);
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

impl<R> Drop for CellHeader<R> {
    fn drop(&mut self) {
        let references_ptr = self.references.as_mut_ptr() as *mut R;
        for i in 0..self.descriptor.reference_count() {
            // SAFETY: references were initialized
            unsafe { std::ptr::drop_in_place(references_ptr.add(i)) };
        }
    }
}

#[inline(never)]
pub fn compute_bit_len(data: &[u8], aligned: bool) -> u16 {
    let mut length = data.len() as u16 * 8;
    if aligned {
        return length;
    }

    for x in data.iter().rev() {
        if *x == 0 {
            length -= 8;
        } else {
            length -= 1 + x.trailing_zeros() as u16;
            break;
        }
    }
    length
}
