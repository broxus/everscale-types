use std::mem::MaybeUninit;

use super::{
    Cell, CellContainer, CellDescriptor, CellFamily, CellHash, CellTreeStats, EMPTY_CELL_HASH,
};

macro_rules! define_gen_vtable_ptr {
    (($family:ty, $($param:tt)*) => $($type:tt)*) => {
        const fn gen_vtable_ptr<$($param)*>() -> *const () {
            let uninit = std::mem::MaybeUninit::<$($type)*>::uninit();
            let fat_ptr = uninit.as_ptr() as *const dyn crate::cell::Cell<$family>;
            // SAFETY: "fat" pointer consists of two "slim" pointers
            let [_, vtable] = unsafe { std::mem::transmute::<_, [*const (); 2]>(fat_ptr) };
            vtable
        }
    };
}

/// Single-threaded cell implementation
pub mod rc;
/// Thread-safe cell implementation
pub mod sync;

/// Helper struct for tightly packed cell data
#[repr(C)]
struct HeaderWithData<H, const N: usize> {
    header: H,
    data: [u8; N],
}

struct EmptyOrdinaryCell;

impl<C: CellFamily> Cell<C> for EmptyOrdinaryCell {
    fn descriptor(&self) -> CellDescriptor {
        CellDescriptor::new([0, 0])
    }

    fn data(&self) -> &[u8] {
        &[]
    }

    fn bit_len(&self) -> u16 {
        0
    }

    fn reference(&self, _: u8) -> Option<&dyn Cell<C>> {
        None
    }

    fn reference_cloned(&self, _: u8) -> Option<CellContainer<C>> {
        None
    }

    fn hash(&self, _: u8) -> CellHash {
        EMPTY_CELL_HASH
    }

    fn depth(&self, _: u8) -> u16 {
        0
    }

    fn stats(&self) -> CellTreeStats {
        CellTreeStats {
            bit_count: 0,
            cell_count: 1,
        }
    }
}

type OrdinaryCell<C, const N: usize> = HeaderWithData<OrdinaryCellHeader<C>, N>;

struct OrdinaryCellHeader<C: CellFamily> {
    bit_len: u16,
    stats: CellTreeStats,
    hashes: Vec<(CellHash, u16)>,
    descriptor: CellDescriptor,
    references: [MaybeUninit<CellContainer<C>>; 4],
}

impl<C: CellFamily> OrdinaryCellHeader<C> {
    fn level_descr(&self, level: u8) -> &(CellHash, u16) {
        let hash_index = hash_index(self.descriptor, level);
        debug_assert!((hash_index as usize) < self.hashes.len());

        // SAFETY: hash index is in range 0..=3
        unsafe { self.hashes.get_unchecked(hash_index as usize) }
    }

    fn reference(&self, i: u8) -> Option<&CellContainer<C>> {
        if i < self.descriptor.reference_count() as u8 {
            // SAFETY: Item is initialized
            let child = unsafe { self.references.get_unchecked(i as usize).assume_init_ref() };
            Some(child)
        } else {
            None
        }
    }
}

impl<C: CellFamily> Drop for OrdinaryCellHeader<C> {
    fn drop(&mut self) {
        let references_ptr = self.references.as_mut_ptr() as *mut CellContainer<C>;
        debug_assert!(self.descriptor.reference_count() <= 4);

        for i in 0..self.descriptor.reference_count() {
            // SAFETY: references were initialized
            unsafe { std::ptr::drop_in_place(references_ptr.add(i)) };
        }
    }
}

// TODO: merge VTables for different data array sizes
impl<C: CellFamily, const N: usize> Cell<C> for OrdinaryCell<C, N>
where
    CellContainer<C>: AsRef<dyn Cell<C>>,
{
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

    fn reference(&self, index: u8) -> Option<&dyn Cell<C>> {
        Some(self.header.reference(index)?.as_ref())
    }

    fn reference_cloned(&self, index: u8) -> Option<CellContainer<C>> {
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

struct LibraryReference {
    repr_hash: CellHash,
    repr_depth: u16,
    descriptor: CellDescriptor,
    data: [u8; 33],
}

impl LibraryReference {
    const BIT_LEN: u16 = 8 + 256;
}

impl<C: CellFamily> Cell<C> for LibraryReference {
    fn descriptor(&self) -> CellDescriptor {
        self.descriptor
    }

    fn data(&self) -> &[u8] {
        self.data.as_ref()
    }

    fn bit_len(&self) -> u16 {
        LibraryReference::BIT_LEN
    }

    fn reference(&self, _: u8) -> Option<&dyn Cell<C>> {
        None
    }

    fn reference_cloned(&self, _: u8) -> Option<CellContainer<C>> {
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

type PrunedBranch<const N: usize> = HeaderWithData<PrunedBranchHeader, N>;

struct PrunedBranchHeader {
    repr_hash: CellHash,
    repr_depth: u16,
    level: u8,
    descriptor: CellDescriptor,
}

impl PrunedBranchHeader {
    #[inline]
    pub const fn cell_data_len(level: usize) -> usize {
        2 + level * (32 + 2)
    }
}

impl<C: CellFamily, const N: usize> Cell<C> for PrunedBranch<N> {
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
        8 + 8 + (self.header.level as u16) * (256 + 16)
    }

    fn reference(&self, _: u8) -> Option<&dyn Cell<C>> {
        None
    }

    fn reference_cloned(&self, _: u8) -> Option<CellContainer<C>> {
        None
    }

    fn hash(&self, level: u8) -> CellHash {
        let hash_index = hash_index(self.header.descriptor, level);
        if hash_index == self.header.level {
            self.header.repr_hash
        } else {
            let offset = 2 + hash_index as usize * 32;
            debug_assert!(offset + 32 <= self.header.descriptor.byte_len() as usize);

            let data_ptr = std::ptr::addr_of!(self.data) as *const u8;

            // SAFETY: Cell was created from a well-formed parts, so data is big enough
            unsafe { *(data_ptr.add(offset) as *const [u8; 32]) }
        }
    }

    fn depth(&self, level: u8) -> u16 {
        let hash_index = hash_index(self.header.descriptor, level);
        if hash_index == self.header.level {
            self.header.repr_depth
        } else {
            let offset = 2 + self.header.level as usize * 32 + hash_index as usize * 2;
            debug_assert!(offset + 2 <= self.header.descriptor.byte_len() as usize);

            let data_ptr = std::ptr::addr_of!(self.data) as *const u8;

            // SAFETY: Cell was created from a well-formed parts, so data is big enough
            u16::from_be_bytes(unsafe { *(data_ptr.add(offset) as *const [u8; 2]) })
        }
    }

    fn stats(&self) -> CellTreeStats {
        aligned_leaf_stats(self.header.descriptor)
    }
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
