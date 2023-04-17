use std::mem::MaybeUninit;

#[cfg(feature = "stats")]
use super::CellTreeStats;
use super::{Cell, CellDescriptor, CellFamily, CellHash, CellImpl, EMPTY_CELL_HASH, MAX_REF_COUNT};
use crate::util::TryAsMut;

macro_rules! define_gen_vtable_ptr {
    (($($param:tt)*) => $($type:tt)*) => {
        const fn gen_vtable_ptr<$($param)*>() -> *const () {
            let uninit = std::mem::MaybeUninit::<$($type)*>::uninit();
            let fat_ptr = uninit.as_ptr() as *const dyn crate::cell::CellImpl;
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
#[cfg(not(feature = "sync"))]
pub mod rc;
/// Thread-safe cell implementation.
#[cfg(feature = "sync")]
pub mod sync;

type ReplacedChild = Result<Cell, Cell>;

/// Helper struct for tightly packed cell data.
#[repr(C)]
struct HeaderWithData<H, const N: usize> {
    header: H,
    data: [u8; N],
}

struct EmptyOrdinaryCell;

impl CellImpl for EmptyOrdinaryCell {
    fn descriptor(&self) -> CellDescriptor {
        CellDescriptor::new([0, 0])
    }

    fn data(&self) -> &[u8] {
        &[]
    }

    fn bit_len(&self) -> u16 {
        0
    }

    fn reference(&self, _: u8) -> Option<&dyn CellImpl> {
        None
    }

    fn reference_cloned(&self, _: u8) -> Option<Cell> {
        None
    }

    fn virtualize(&self) -> &dyn CellImpl {
        self
    }

    fn hash(&self, _: u8) -> &CellHash {
        EMPTY_CELL_HASH
    }

    fn depth(&self, _: u8) -> u16 {
        0
    }

    fn take_first_child(&mut self) -> Option<Cell> {
        None
    }

    fn replace_first_child(&mut self, parent: Cell) -> ReplacedChild {
        Err(parent)
    }

    fn take_next_child(&mut self) -> Option<Cell> {
        None
    }

    #[cfg(feature = "stats")]
    fn stats(&self) -> CellTreeStats {
        CellTreeStats {
            bit_count: 0,
            cell_count: 1,
        }
    }
}

/// Static cell which can be used to create cell references in const context.
pub struct StaticCell {
    descriptor: CellDescriptor,
    data: &'static [u8],
    bit_len: u16,
    hash: &'static [u8; 32],
}

impl StaticCell {
    /// Creates a new plain ordinary cell from parts.
    ///
    /// # Safety
    ///
    /// The following must be true:
    /// - Data must be well-formed and normalized (contain bit tag if needed and
    ///   be enough to store `bit_len` of bits).
    /// - `bit_len` must be in range 0..=1023
    /// - `hash` must be a correct hash for the current cell.
    pub const unsafe fn new(data: &'static [u8], bit_len: u16, hash: &'static [u8; 32]) -> Self {
        Self {
            descriptor: CellDescriptor::new([0, CellDescriptor::compute_d2(bit_len)]),
            data,
            bit_len,
            hash,
        }
    }
}

impl CellImpl for StaticCell {
    fn descriptor(&self) -> CellDescriptor {
        self.descriptor
    }

    fn data(&self) -> &[u8] {
        self.data
    }

    fn bit_len(&self) -> u16 {
        self.bit_len
    }

    fn reference(&self, _: u8) -> Option<&dyn CellImpl> {
        None
    }

    fn reference_cloned(&self, _: u8) -> Option<Cell> {
        None
    }

    fn virtualize(&self) -> &dyn CellImpl {
        self
    }

    fn hash(&self, _: u8) -> &CellHash {
        self.hash
    }

    fn depth(&self, _: u8) -> u16 {
        0
    }

    fn take_first_child(&mut self) -> Option<Cell> {
        None
    }

    fn replace_first_child(&mut self, parent: Cell) -> ReplacedChild {
        Err(parent)
    }

    fn take_next_child(&mut self) -> Option<Cell> {
        None
    }

    #[cfg(feature = "stats")]
    fn stats(&self) -> CellTreeStats {
        CellTreeStats {
            bit_count: self.bit_len as u64,
            cell_count: 1,
        }
    }
}

static ALL_ZEROS_CELL: StaticCell = StaticCell {
    descriptor: CellDescriptor::new([0, 0xff]),
    data: &ALL_ZEROS_CELL_DATA,
    bit_len: 1023,
    hash: &ALL_ZEROS_CELL_HASH,
};

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

static ALL_ONES_CELL: StaticCell = StaticCell {
    descriptor: CellDescriptor::new([0, 0xff]),
    data: &ALL_ONES_CELL_DATA,
    bit_len: 1023,
    hash: &ALL_ONES_CELL_HASH,
};

const ALL_ONES_CELL_DATA: [u8; 128] = [0xff; 128];

const ALL_ONES_CELL_HASH: [u8; 32] = [
    0x82, 0x97, 0x0d, 0x46, 0x64, 0xb7, 0x68, 0x3c, 0x3d, 0x14, 0xd4, 0x9b, 0x1f, 0x9f, 0xf3, 0x49,
    0x66, 0x12, 0x81, 0x70, 0x30, 0x1a, 0x7b, 0xec, 0xc2, 0x7a, 0xf1, 0xad, 0xbe, 0x6a, 0x31, 0xc9,
];

type OrdinaryCell<const N: usize> = HeaderWithData<OrdinaryCellHeader, N>;

struct OrdinaryCellHeader {
    bit_len: u16,
    #[cfg(feature = "stats")]
    stats: CellTreeStats,
    hashes: Vec<(CellHash, u16)>,
    descriptor: CellDescriptor,
    references: [MaybeUninit<Cell>; MAX_REF_COUNT],
    without_first: bool,
}

impl OrdinaryCellHeader {
    fn level_descr(&self, level: u8) -> &(CellHash, u16) {
        let hash_index = hash_index(self.descriptor, level);
        debug_assert!((hash_index as usize) < self.hashes.len());

        // SAFETY: hash index is in range 0..=3
        unsafe { self.hashes.get_unchecked(hash_index as usize) }
    }

    fn reference(&self, i: u8) -> Option<&Cell> {
        if i < self.descriptor.reference_count() {
            // SAFETY: Item is initialized
            let child = unsafe { self.references.get_unchecked(i as usize).assume_init_ref() };
            Some(child)
        } else {
            None
        }
    }

    fn take_first_child(&mut self) -> Option<Cell> {
        if self.descriptor.reference_count() > 0 && !self.without_first {
            self.without_first = true;
            let references_ptr = self.references.as_ptr() as *const Cell;
            Some(unsafe { std::ptr::read(references_ptr) })
        } else {
            None
        }
    }

    fn replace_first_child_with_parent(&mut self, parent: Cell) -> ReplacedChild {
        if self.descriptor.reference_count() > 0 && !self.without_first {
            let references_ptr = self.references.as_mut_ptr() as *mut Cell;
            unsafe {
                let result = Ok(std::ptr::read(references_ptr));
                std::ptr::write(references_ptr, parent);
                result
            }
        } else {
            Err(parent)
        }
    }

    fn take_next_child(&mut self) -> Option<Cell> {
        if self.descriptor.reference_count() > 1 {
            self.descriptor.d1 -= 1;
            let references_ptr = self.references.as_ptr() as *const Cell;
            let idx = self.descriptor.d1 & CellDescriptor::REF_COUNT_MASK;
            Some(unsafe { std::ptr::read(references_ptr.add(idx as usize)) })
        } else {
            None
        }
    }
}

impl Drop for OrdinaryCellHeader {
    fn drop(&mut self) {
        // Returns the nearest ancestor and its consumed next child.
        // Returns `None` if no ancestors with children found.
        #[inline]
        fn take_ancestor_next_child(parent: Cell) -> Option<(Cell, Cell)> {
            let mut ancestor = parent;
            while let Some(ancestor_ref) = ancestor.try_as_mut() {
                // Try to get the next child from the direct ancestor
                if let Some(next_child) = ancestor_ref.take_next_child() {
                    return Some((ancestor, next_child));
                } else if let Some(grand_ancestor) = ancestor_ref.take_first_child() {
                    // Drop `ancestor` as it is now a leaf node
                    drop(ancestor);

                    // Move one level deeper
                    ancestor = grand_ancestor;
                } else {
                    // Break on leaf node
                    break;
                }
            }
            None
        }

        fn main_deep_safe_drop(mut parent: Cell) {
            // Consume first child from parent.
            let mut current = 'curr: {
                if let Some(parent) = parent.try_as_mut() {
                    if let Some(first_child) = parent.take_first_child() {
                        break 'curr first_child;
                    }
                }
                return;
            };

            loop {
                // If current node is unique
                if let Some(current_ref) = current.try_as_mut() {
                    // Try to replace its first child with the current parent
                    match current_ref.replace_first_child(parent) {
                        Ok(first_child) => {
                            // Move one layer lower
                            parent = current;
                            current = first_child;
                            continue;
                        }
                        Err(returned_parent) => {
                            parent = returned_parent;

                            // Current node is now a leaf, drop it
                            drop(current);
                        }
                    }
                }

                // Find the next child
                let Some((ancestor, child)) = take_ancestor_next_child(parent) else {
                    return;
                };

                parent = ancestor;
                current = child;
            }
        }

        fn deep_drop_impl(cell: &mut Cell) {
            let Some(cell) = cell.try_as_mut() else {
                return;
            };

            if let Some(first_child) = cell.take_first_child() {
                main_deep_safe_drop(first_child);

                while let Some(next_child) = cell.take_next_child() {
                    main_deep_safe_drop(next_child);
                }
            }
        }

        let references_ptr = self.references.as_mut_ptr() as *mut Cell;
        debug_assert!(self.descriptor.reference_count() <= MAX_REF_COUNT as u8);

        for i in 0..self.descriptor.reference_count() {
            if i == 0 && self.without_first {
                continue;
            }

            // SAFETY: references were initialized
            unsafe {
                let child_ptr = references_ptr.add(i as usize);
                deep_drop_impl(&mut *child_ptr);
                std::ptr::drop_in_place(child_ptr);
            }
        }
    }
}

// TODO: merge VTables for different data array sizes

impl<const N: usize> CellImpl for OrdinaryCell<N> {
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

    fn reference(&self, index: u8) -> Option<&dyn CellImpl> {
        Some(self.header.reference(index)?.as_ref())
    }

    fn reference_cloned(&self, index: u8) -> Option<Cell> {
        Some(self.header.reference(index)?.clone())
    }

    fn virtualize(&self) -> &dyn CellImpl {
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

    fn take_first_child(&mut self) -> Option<Cell> {
        self.header.take_first_child()
    }

    fn replace_first_child(&mut self, parent: Cell) -> ReplacedChild {
        self.header.replace_first_child_with_parent(parent)
    }

    fn take_next_child(&mut self) -> Option<Cell> {
        self.header.take_next_child()
    }

    #[cfg(feature = "stats")]
    fn stats(&self) -> CellTreeStats {
        self.header.stats
    }
}

struct LibraryReference {
    repr_hash: CellHash,
    descriptor: CellDescriptor,
    data: [u8; 33],
}

impl LibraryReference {
    const BIT_LEN: u16 = 8 + 256;
}

impl CellImpl for LibraryReference {
    fn descriptor(&self) -> CellDescriptor {
        self.descriptor
    }

    fn data(&self) -> &[u8] {
        self.data.as_ref()
    }

    fn bit_len(&self) -> u16 {
        LibraryReference::BIT_LEN
    }

    fn reference(&self, _: u8) -> Option<&dyn CellImpl> {
        None
    }

    fn reference_cloned(&self, _: u8) -> Option<Cell> {
        None
    }

    fn virtualize(&self) -> &dyn CellImpl {
        self
    }

    fn hash(&self, _: u8) -> &CellHash {
        &self.repr_hash
    }

    fn depth(&self, _: u8) -> u16 {
        0
    }

    fn take_first_child(&mut self) -> Option<Cell> {
        None
    }

    fn replace_first_child(&mut self, parent: Cell) -> ReplacedChild {
        Err(parent)
    }

    fn take_next_child(&mut self) -> Option<Cell> {
        None
    }

    #[cfg(feature = "stats")]
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
    level: u8,
    descriptor: CellDescriptor,
}

impl PrunedBranchHeader {
    #[inline]
    pub const fn cell_data_len(level: usize) -> usize {
        2 + level * (32 + 2)
    }
}

impl<const N: usize> CellImpl for PrunedBranch<N> {
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

    fn reference(&self, _: u8) -> Option<&dyn CellImpl> {
        None
    }

    fn reference_cloned(&self, _: u8) -> Option<Cell> {
        None
    }

    fn virtualize(&self) -> &dyn CellImpl {
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
            0
        } else {
            let offset = 2 + self.header.level as usize * 32 + hash_index as usize * 2;
            debug_assert!(offset + 2 <= self.header.descriptor.byte_len() as usize);

            let data_ptr = std::ptr::addr_of!(self.data) as *const u8;

            // SAFETY: Cell was created from a well-formed parts, so data is big enough
            u16::from_be_bytes(unsafe { *(data_ptr.add(offset) as *const [u8; 2]) })
        }
    }

    fn take_first_child(&mut self) -> Option<Cell> {
        None
    }

    fn replace_first_child(&mut self, parent: Cell) -> ReplacedChild {
        Err(parent)
    }

    fn take_next_child(&mut self) -> Option<Cell> {
        None
    }

    #[cfg(feature = "stats")]
    fn stats(&self) -> CellTreeStats {
        aligned_leaf_stats(self.header.descriptor)
    }
}

#[repr(transparent)]
pub struct VirtualCell<T>(T);

impl<T> CellImpl for VirtualCell<T>
where
    T: AsRef<dyn CellImpl> + TryAsMut<dyn CellImpl>,
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

    fn reference(&self, index: u8) -> Option<&dyn CellImpl> {
        Some(self.0.as_ref().reference(index)?.virtualize())
    }

    fn reference_cloned(&self, index: u8) -> Option<Cell> {
        Some(Cell::virtualize(self.0.as_ref().reference_cloned(index)?))
    }

    fn virtualize(&self) -> &dyn CellImpl {
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

    fn take_first_child(&mut self) -> Option<Cell> {
        self.0.try_as_mut()?.take_first_child()
    }

    fn take_next_child(&mut self) -> Option<Cell> {
        self.0.try_as_mut()?.take_next_child()
    }

    fn replace_first_child(&mut self, parent: Cell) -> ReplacedChild {
        match self.0.try_as_mut() {
            Some(cell) => cell.replace_first_child(parent),
            None => Err(parent),
        }
    }

    #[cfg(feature = "stats")]
    fn stats(&self) -> CellTreeStats {
        self.0.as_ref().stats()
    }
}

#[repr(transparent)]
pub struct VirtualCellWrapper<T>(T);

impl<T> VirtualCellWrapper<T> {
    pub fn wrap(value: &T) -> &Self {
        // SAFETY: VirtualCellWrapper<T> is #[repr(transparent)]
        unsafe { &*(value as *const T as *const Self) }
    }
}

impl<T: CellImpl> CellImpl for VirtualCellWrapper<T> {
    fn descriptor(&self) -> CellDescriptor {
        self.0.descriptor()
    }

    fn data(&self) -> &[u8] {
        self.0.data()
    }

    fn bit_len(&self) -> u16 {
        self.0.bit_len()
    }

    fn reference(&self, index: u8) -> Option<&dyn CellImpl> {
        Some(self.0.reference(index)?.virtualize())
    }

    fn reference_cloned(&self, index: u8) -> Option<Cell> {
        Some(Cell::virtualize(self.0.reference_cloned(index)?))
    }

    fn virtualize(&self) -> &dyn CellImpl {
        self
    }

    fn hash(&self, level: u8) -> &CellHash {
        self.0.hash(virtual_hash_index(self.0.descriptor(), level))
    }

    fn depth(&self, level: u8) -> u16 {
        self.0.depth(virtual_hash_index(self.0.descriptor(), level))
    }

    fn take_first_child(&mut self) -> Option<Cell> {
        self.0.take_first_child()
    }

    fn replace_first_child(&mut self, parent: Cell) -> ReplacedChild {
        self.0.replace_first_child(parent)
    }

    fn take_next_child(&mut self) -> Option<Cell> {
        self.0.take_next_child()
    }

    #[cfg(feature = "stats")]
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

#[cfg(feature = "stats")]
fn aligned_leaf_stats(descriptor: CellDescriptor) -> CellTreeStats {
    CellTreeStats {
        bit_count: descriptor.byte_len() as u64 * 8,
        cell_count: 1,
    }
}

#[cfg(test)]
mod tests {
    use crate::boc::Boc;
    use crate::cell::{Cell, CellBuilder, CellFamily};

    #[test]
    fn static_cells() {
        let mut builder = CellBuilder::new();
        builder.store_zeros(1023).unwrap();
        let cell = builder.build().unwrap();
        let all_zeros = Cell::all_zeros_ref();
        assert_eq!(cell.as_ref().repr_hash(), all_zeros.repr_hash());
        assert_eq!(cell.as_ref().data(), all_zeros.data());
        assert_eq!(Boc::encode(cell.as_ref()), Boc::encode(all_zeros));

        let builder = CellBuilder::from_raw_data(&[0xff; 128], 1023).unwrap();
        let cell = builder.build().unwrap();
        let all_ones = Cell::all_ones_ref();
        assert_eq!(cell.as_ref().repr_hash(), all_ones.repr_hash());
        assert_eq!(cell.as_ref().data(), all_ones.data());
        assert_eq!(Boc::encode(cell.as_ref()), Boc::encode(all_ones));
    }
}
