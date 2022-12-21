use std::mem::MaybeUninit;

use super::{
    Cell, CellContainer, CellDescriptor, CellFamily, CellHash, CellTreeStats, EMPTY_CELL_HASH,
    MAX_REF_COUNT,
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

macro_rules! offset_of {
    ($ty: path, $field: tt) => {{
        let $ty { $field: _, .. };

        let uninit = ::std::mem::MaybeUninit::<$ty>::uninit();
        let base_ptr = uninit.as_ptr() as *const $ty;
        unsafe {
            let field_ptr = std::ptr::addr_of!((*base_ptr).$field);
            (field_ptr as *const u8).offset_from(base_ptr as *const u8) as usize
        }
    }};
}

/// Single-threaded cell implementation.
pub mod rc;
/// Thread-safe cell implementation.
pub mod sync;

/// Helper struct for tightly packed cell data.
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

    fn virtualize(&self) -> &dyn Cell<C> {
        self
    }

    fn hash(&self, _: u8) -> &CellHash {
        &EMPTY_CELL_HASH
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

static ALL_ZEROS_CELL: AllZerosCell = AllZerosCell;

struct AllZerosCell;

impl<C: CellFamily> Cell<C> for AllZerosCell {
    fn descriptor(&self) -> CellDescriptor {
        CellDescriptor::new([0, 0xff])
    }

    fn data(&self) -> &[u8] {
        &ALL_ZEROS_CELL_DATA
    }

    fn bit_len(&self) -> u16 {
        1023
    }

    fn reference(&self, _: u8) -> Option<&dyn Cell<C>> {
        None
    }

    fn reference_cloned(&self, _: u8) -> Option<CellContainer<C>> {
        None
    }

    fn virtualize(&self) -> &dyn Cell<C> {
        self
    }

    fn hash(&self, _: u8) -> &CellHash {
        &ALL_ZEROS_CELL_HASH
    }

    fn depth(&self, _: u8) -> u16 {
        0
    }

    fn stats(&self) -> CellTreeStats {
        CellTreeStats {
            bit_count: 1023,
            cell_count: 1,
        }
    }
}

const ALL_ZEROS_CELL_DATA: [u8; 128] = [
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
];

const ALL_ZEROS_CELL_HASH: [u8; 32] = [
    0xba, 0x03, 0x8d, 0x92, 0x4d, 0xa0, 0xb4, 0x2c, 0x44, 0x76, 0x62, 0xe6, 0xb8, 0xa5, 0x3f, 0x15,
    0x88, 0x9e, 0xbd, 0xf9, 0xd3, 0xb2, 0xf0, 0x1d, 0xbf, 0x94, 0x2c, 0x29, 0xbc, 0x48, 0x98, 0x71,
];

static ALL_ONES_CELL: AllOnesCell = AllOnesCell;

struct AllOnesCell;

impl<C: CellFamily> Cell<C> for AllOnesCell {
    fn descriptor(&self) -> CellDescriptor {
        CellDescriptor::new([0, 0xff])
    }

    fn data(&self) -> &[u8] {
        &ALL_ONES_CELL_DATA
    }

    fn bit_len(&self) -> u16 {
        1023
    }

    fn reference(&self, _: u8) -> Option<&dyn Cell<C>> {
        None
    }

    fn reference_cloned(&self, _: u8) -> Option<CellContainer<C>> {
        None
    }

    fn virtualize(&self) -> &dyn Cell<C> {
        self
    }

    fn hash(&self, _: u8) -> &CellHash {
        &ALL_ONES_CELL_HASH
    }

    fn depth(&self, _: u8) -> u16 {
        0
    }

    fn stats(&self) -> CellTreeStats {
        CellTreeStats {
            bit_count: 1023,
            cell_count: 1,
        }
    }
}

const ALL_ONES_CELL_DATA: [u8; 128] = [0xff; 128];

const ALL_ONES_CELL_HASH: [u8; 32] = [
    0x82, 0x97, 0x0d, 0x46, 0x64, 0xb7, 0x68, 0x3c, 0x3d, 0x14, 0xd4, 0x9b, 0x1f, 0x9f, 0xf3, 0x49,
    0x66, 0x12, 0x81, 0x70, 0x30, 0x1a, 0x7b, 0xec, 0xc2, 0x7a, 0xf1, 0xad, 0xbe, 0x6a, 0x31, 0xc9,
];

type OrdinaryCell<C, const N: usize> = HeaderWithData<OrdinaryCellHeader<C>, N>;

struct OrdinaryCellHeader<C: CellFamily> {
    bit_len: u16,
    stats: CellTreeStats,
    hashes: Vec<(CellHash, u16)>,
    descriptor: CellDescriptor,
    references: [MaybeUninit<CellContainer<C>>; MAX_REF_COUNT],
}

impl<C: CellFamily> OrdinaryCellHeader<C> {
    fn level_descr(&self, level: u8) -> &(CellHash, u16) {
        let hash_index = hash_index(self.descriptor, level);
        debug_assert!((hash_index as usize) < self.hashes.len());

        // SAFETY: hash index is in range 0..=3
        unsafe { self.hashes.get_unchecked(hash_index as usize) }
    }

    fn reference(&self, i: u8) -> Option<&CellContainer<C>> {
        if i < self.descriptor.reference_count() {
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
        debug_assert!(self.descriptor.reference_count() <= MAX_REF_COUNT as u8);

        for i in 0..self.descriptor.reference_count() {
            // SAFETY: references were initialized
            unsafe { std::ptr::drop_in_place(references_ptr.add(i as usize)) };
        }
    }
}

// TODO: merge VTables for different data array sizes
impl<C: CellFamily, const N: usize> Cell<C> for OrdinaryCell<C, N> {
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

    fn virtualize(&self) -> &dyn Cell<C> {
        if self.header.descriptor.level_mask().is_empty() {
            self
        } else {
            VirtualCellWrapper::wrap(self)
        }
    }

    fn hash(&self, level: u8) -> &CellHash {
        &self.header.level_descr(level).0
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

    fn virtualize(&self) -> &dyn Cell<C> {
        self
    }

    fn hash(&self, _: u8) -> &CellHash {
        &self.repr_hash
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

    fn virtualize(&self) -> &dyn Cell<C> {
        VirtualCellWrapper::wrap(self)
    }

    fn hash(&self, level: u8) -> &CellHash {
        let hash_index = hash_index(self.header.descriptor, level);
        if hash_index == self.header.level {
            &self.header.repr_hash
        } else {
            let offset = 2 + hash_index as usize * 32;
            debug_assert!(offset + 32 <= self.header.descriptor.byte_len() as usize);

            let data_ptr = std::ptr::addr_of!(self.data) as *const u8;

            // SAFETY: Cell was created from a well-formed parts, so data is big enough
            unsafe { &*(data_ptr.add(offset) as *const [u8; 32]) }
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

#[repr(transparent)]
struct VirtualCell<T>(T);

impl<C, T> Cell<C> for VirtualCell<T>
where
    for<'a> C: CellFamily + 'a,
    T: AsRef<dyn Cell<C>>,
{
    fn descriptor(&self) -> CellDescriptor {
        self.0.as_ref().descriptor()
    }

    fn data(&self) -> &[u8] {
        self.0.as_ref().data()
    }

    fn bit_len(&self) -> u16 {
        self.0.as_ref().bit_len()
    }

    fn reference(&self, index: u8) -> Option<&dyn Cell<C>> {
        Some(self.0.as_ref().reference(index)?.virtualize())
    }

    fn reference_cloned(&self, index: u8) -> Option<CellContainer<C>> {
        Some(C::virtualize(self.0.as_ref().reference_cloned(index)?))
    }

    fn virtualize(&self) -> &dyn Cell<C> {
        self
    }

    fn hash(&self, level: u8) -> &CellHash {
        let cell = self.0.as_ref();
        cell.hash(virtual_hash_index(cell.descriptor(), level))
    }

    fn depth(&self, level: u8) -> u16 {
        let cell = self.0.as_ref();
        cell.depth(virtual_hash_index(cell.descriptor(), level))
    }

    fn stats(&self) -> CellTreeStats {
        self.0.as_ref().stats()
    }
}

#[repr(transparent)]
struct VirtualCellWrapper<T>(T);

impl<T> VirtualCellWrapper<T> {
    pub fn wrap(value: &T) -> &Self {
        // SAFETY: VirtualCellWrapper<T> is #[repr(transparent)]
        unsafe { &*(value as *const T as *const Self) }
    }
}

impl<C: CellFamily, T: Cell<C>> Cell<C> for VirtualCellWrapper<T> {
    fn descriptor(&self) -> CellDescriptor {
        self.0.descriptor()
    }

    fn data(&self) -> &[u8] {
        self.0.data()
    }

    fn bit_len(&self) -> u16 {
        self.0.bit_len()
    }

    fn reference(&self, index: u8) -> Option<&dyn Cell<C>> {
        Some(self.0.reference(index)?.virtualize())
    }

    fn reference_cloned(&self, index: u8) -> Option<CellContainer<C>> {
        Some(C::virtualize(self.0.reference_cloned(index)?))
    }

    fn virtualize(&self) -> &dyn Cell<C> {
        self
    }

    fn hash(&self, level: u8) -> &CellHash {
        self.0.hash(virtual_hash_index(self.0.descriptor(), level))
    }

    fn depth(&self, level: u8) -> u16 {
        self.0.depth(virtual_hash_index(self.0.descriptor(), level))
    }

    fn stats(&self) -> CellTreeStats {
        self.0.stats()
    }
}

fn virtual_hash_index(descriptor: CellDescriptor, level: u8) -> u8 {
    descriptor.level_mask().virtualize(1).hash_index(level)
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

#[cfg(test)]
mod tests {
    use crate::boc::Boc;
    use crate::cell::{CellBuilder, DefaultFinalizer};
    use crate::{ArcCellFamily, RcCellFamily};

    #[test]
    fn static_cells() {
        fn check_static_cells<C>()
        where
            for<'a> C: DefaultFinalizer + 'a,
        {
            let mut builder = CellBuilder::<C>::new();
            assert!(builder.store_zeros(1023));
            let cell = builder.build().unwrap();
            let all_zeros = C::all_zeros_ref();
            assert_eq!(cell.as_ref().repr_hash(), all_zeros.repr_hash());
            assert_eq!(cell.as_ref().data(), all_zeros.data());
            assert_eq!(Boc::encode(cell.as_ref()), Boc::encode(all_zeros));

            let builder = CellBuilder::<C>::from_raw_data(&[0xff; 128], 1023).unwrap();
            let cell = builder.build().unwrap();
            let all_ones = C::all_ones_ref();
            assert_eq!(cell.as_ref().repr_hash(), all_ones.repr_hash());
            assert_eq!(cell.as_ref().data(), all_ones.data());
            assert_eq!(Boc::encode(cell.as_ref()), Boc::encode(all_ones));
        }

        check_static_cells::<ArcCellFamily>();
        check_static_cells::<RcCellFamily>();
    }
}
