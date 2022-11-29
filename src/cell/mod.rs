use std::ops::{Add, AddAssign};
use std::ops::{BitOr, BitOrAssign};
use std::sync::Arc;

/// Generic cell implementation
pub(crate) mod generic_cell;

/// Cell finalization primitives
pub mod finalizer;

/// Represents the interface of a well-formed cell.
///
/// Since all basic operations are implements via dynamic dispatch,
/// all high-level helper methods are implemented for `dyn Cell`.
pub trait Cell {
    /// Returns cell descriptor.
    ///
    /// # See also
    ///
    /// Cell descriptor contains some tightly packed info about the cell.
    /// If you want convinient methods to access it use:
    /// [`cell_type`], [`level`], [`level_mask`], [`reference_count`], [`is_exotic`]
    ///
    /// [`cell_type`]: fn@crate::cell::Cell::cell_type
    /// [`level`]: fn@crate::cell::Cell::level
    /// [`level_mask`]: fn@crate::cell::Cell::level_mask
    /// [`reference_count`]: fn@crate::cell::Cell::reference_count
    /// [`is_exotic`]: fn@crate::cell::Cell::is_exotic
    fn descriptor(&self) -> CellDescriptor;

    /// Returns the raw data of this cell.
    fn data(&self) -> &[u8];

    /// Returns the data size of this cell in bits.
    fn bit_len(&self) -> u16;

    /// Returns a reference to the Nth child cell.
    fn reference(&self, index: u8) -> Option<&dyn Cell>;

    /// Returns the Nth child cell.
    fn reference_cloned(&self, index: u8) -> Option<ArcCell>;

    /// Returns cell hash for the specified level.
    ///
    /// Cell representation hash is the hash at the maximum level ([`LevelMask::MAX_LEVEL`]).
    /// Use [`repr_hash`] as a simple alias for this.
    ///
    /// [`repr_hash`]: fn@crate::cell::Cell::repr_hash
    fn hash(&self, level: u8) -> CellHash;

    /// Returns cell depth for the specified level.
    fn depth(&self, level: u8) -> u16;

    /// Returns the sum of all bits and cells of all elements in the cell tree
    /// (including this cell).
    fn stats(&self) -> CellTreeStats;
}

impl dyn Cell + '_ {
    /// Computes cell type from descriptor bytes.
    #[inline]
    pub fn cell_type(&self) -> CellType {
        self.descriptor().cell_type()
    }

    /// Computes cell level from level mask.
    #[inline]
    pub fn level(&self) -> u8 {
        self.descriptor().level_mask().level()
    }

    /// Computes level mask from descriptor bytes.
    #[inline]
    pub fn level_mask(&self) -> LevelMask {
        self.descriptor().level_mask()
    }

    /// Computes child cell count from descriptor bytes.
    #[inline]
    pub fn reference_count(&self) -> usize {
        self.descriptor().reference_count()
    }

    /// Returns whether the cell is not [`Ordinary`].
    ///
    /// [`Ordinary`]: crate::cell::CellType::Ordinary
    #[inline]
    pub fn is_exotic(&self) -> bool {
        self.descriptor().is_exotic()
    }

    /// Returns representation hash of the cell.
    #[inline]
    pub fn repr_hash(&self) -> [u8; 32] {
        self.hash(LevelMask::MAX_LEVEL)
    }

    /// Creates an iterator through child nodes.
    #[inline]
    pub fn references(&self) -> RefsIter<'_> {
        RefsIter {
            cell: self,
            len: self.reference_count() as u8,
            index: 0,
        }
    }

    /// Returns an object that implements [`Display`] for printing only
    /// the root cell of the cell tree.
    ///
    /// [`Display`]: std::fmt::Display
    #[inline]
    pub fn display_root(&'_ self) -> DisplayCellRoot<'_> {
        DisplayCellRoot(self)
    }

    /// Returns an object that implements [`Display`] for printing all
    /// cells in the cell tree.
    ///
    /// [`Display`]: std::fmt::Display
    #[inline]
    pub fn display_tree(&'_ self) -> DisplayCellTree<'_> {
        DisplayCellTree(self)
    }
}

/// An iterator through child nodes.
#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct RefsIter<'a> {
    cell: &'a dyn Cell,
    len: u8,
    index: u8,
}

impl<'a> RefsIter<'a> {
    /// Creates an iterator through child nodes which produces cloned references.
    #[inline]
    pub fn cloned(self) -> ClonedRefsIter<'a> {
        ClonedRefsIter { inner: self }
    }
}

impl<'a> Iterator for RefsIter<'a> {
    type Item = &'a dyn Cell;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.len {
            None
        } else {
            let child = self.cell.reference(self.index);
            self.index += 1;
            child
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.len.saturating_sub(self.index) as usize;
        (remaining, Some(remaining))
    }
}

impl<'a> DoubleEndedIterator for RefsIter<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len > self.index {
            self.len -= 1;
            self.cell.reference(self.len)
        } else {
            None
        }
    }
}

impl ExactSizeIterator for RefsIter<'_> {
    #[inline]
    fn len(&self) -> usize {
        self.size_hint().0
    }
}

/// An iterator through child nodes which produces cloned references.
#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ClonedRefsIter<'a> {
    inner: RefsIter<'a>,
}

impl<'a> Iterator for ClonedRefsIter<'a> {
    type Item = ArcCell;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.inner.index >= self.inner.len {
            None
        } else {
            let child = self.inner.cell.reference_cloned(self.inner.index);
            self.inner.index += 1;
            child
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a> DoubleEndedIterator for ClonedRefsIter<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.inner.len > self.inner.index {
            self.inner.len -= 1;
            self.inner.cell.reference_cloned(self.inner.len)
        } else {
            None
        }
    }
}

impl ExactSizeIterator for ClonedRefsIter<'_> {
    #[inline]
    fn len(&self) -> usize {
        self.size_hint().0
    }
}

pub type ArcCell = Arc<dyn Cell>;

pub type CellHash = [u8; 32];

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum CellType {
    /// Cell of this type just stores data and references.
    Ordinary,
    /// Exotic cell which was pruned from the original tree of cells
    /// when a Merkle proof has been created.
    PrunedBranch,
    /// Exotic cell with a reference to the cell with a library.
    LibraryReference,
    /// Exotic cell with one hash and one reference.
    MerkleProof,
    /// Exotic cell with two hashes and two references.
    MerkleUpdate,
}

impl CellType {
    /// Returns whether this cell type is Merkle proof or Merkle update.
    #[inline]
    pub const fn is_merkle(self) -> bool {
        matches!(self, Self::MerkleProof | Self::MerkleUpdate)
    }

    /// Returns whether the cell is not ordinary.
    #[inline]
    pub const fn is_exotic(self) -> bool {
        !matches!(self, Self::Ordinary)
    }

    /// Encodes cell type as byte
    #[inline]
    pub const fn to_byte(self) -> u8 {
        match self {
            CellType::Ordinary => 0xff,
            CellType::PrunedBranch => 1,
            CellType::LibraryReference => 2,
            CellType::MerkleProof => 3,
            CellType::MerkleUpdate => 4,
        }
    }
}

impl From<CellType> for u8 {
    #[inline]
    fn from(cell_type: CellType) -> u8 {
        cell_type.to_byte()
    }
}

/// Tightly packed info about a cell
#[derive(Hash, Debug, Clone, Copy)]
#[repr(C)]
pub struct CellDescriptor {
    /// First descriptor byte with a generic info about cell
    pub d1: u8,
    /// Second descriptor byte with a packed data size
    pub d2: u8,
}

impl CellDescriptor {
    pub const REF_COUNT_MASK: u8 = 0b0000_0111;
    pub const IS_EXOTIC_MASK: u8 = 0b0000_1000;
    pub const STORE_HASHES_MASK: u8 = 0b0001_0000;
    pub const LEVEL_MASK: u8 = 0b1110_0000;

    /// Constructs cell descriptor from descriptor bytes.
    #[inline(always)]
    pub const fn new(bytes: [u8; 2]) -> Self {
        Self {
            d1: bytes[0],
            d2: bytes[1],
        }
    }

    /// Computes cell type.
    pub fn cell_type(self) -> CellType {
        if self.d1 & Self::IS_EXOTIC_MASK == 0 {
            CellType::Ordinary
        } else {
            match self.d1 & Self::REF_COUNT_MASK {
                0 => {
                    // NOTE: zero mask <=> zero level
                    if self.d1 & Self::LEVEL_MASK == 0 {
                        CellType::LibraryReference
                    } else {
                        CellType::PrunedBranch
                    }
                }
                1 => CellType::MerkleProof,
                _ => CellType::MerkleUpdate,
            }
        }
    }

    /// Computes child cell count.
    #[inline(always)]
    pub const fn reference_count(self) -> usize {
        (self.d1 & Self::REF_COUNT_MASK) as usize
    }

    /// Returns whether the cell is not [`Ordinary`].
    ///
    /// [`Ordinary`]: crate::cell::CellType::Ordinary
    #[inline(always)]
    pub const fn is_exotic(self) -> bool {
        self.d1 & Self::IS_EXOTIC_MASK != 0
    }

    /// Returns whether this cell refers to some external data.
    #[inline(always)]
    pub fn is_absent(self) -> bool {
        self.d1 == (Self::REF_COUNT_MASK | Self::IS_EXOTIC_MASK)
    }

    /// Returns whether this cell should store hashes in data.
    #[inline(always)]
    pub const fn store_hashes(self) -> bool {
        self.d1 & Self::STORE_HASHES_MASK != 0
    }

    /// Computes level mask.
    #[inline(always)]
    pub const fn level_mask(self) -> LevelMask {
        // SAFETY: `u8 >> 5` is always 3 bits long
        unsafe { LevelMask::new_unchecked(self.d1 >> 5) }
    }

    /// Returns whether this cell's data is 8-bit aligned.
    #[inline(always)]
    pub const fn is_aligned(self) -> bool {
        self.d2 & 1 == 0
    }

    /// Returns this cell's data length in bytes.
    #[inline(always)]
    pub const fn byte_len(self) -> u8 {
        (self.d2 & 1) + (self.d2 >> 1)
    }
}

/// _de Brujn_ level presense bitset.
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct LevelMask(u8);

impl LevelMask {
    /// Empty bitset.
    pub const EMPTY: Self = LevelMask(0);
    /// Max _de Brujn_ level.
    pub const MAX_LEVEL: u8 = 3;

    /// Constructs a new level mask, truncating extra bits.
    #[inline(always)]
    pub const fn new(mask: u8) -> Self {
        Self(mask & 0b111)
    }

    /// Constructs a new level mask from the provided byte as is.
    ///
    /// # Safety
    ///
    /// The following must be true:
    /// - Mask must be in range `0b000..=0b111`.
    #[inline(always)]
    pub const unsafe fn new_unchecked(mask: u8) -> Self {
        Self(mask)
    }

    /// Creates a sufficient mask for the specified level.
    ///
    /// NOTE: levels > 3 has no effect (mask will always be `0b111`).
    #[inline(always)]
    pub const fn from_level(level: u8) -> Self {
        Self(match level {
            0 => 0,
            1 => 1,
            2 => 3,
            _ => 7,
        })
    }

    /// Counts presented higher hashes.
    pub const fn level(self) -> u8 {
        (self.0 & 1) + ((self.0 >> 1) & 1) + ((self.0 >> 2) & 1)
    }

    /// Computes hash index for the specified level.
    pub const fn hash_index(self, level: u8) -> u8 {
        Self(self.0 & Self::from_level(level).0).level()
    }

    /// Creates a new mask, shifted by the offset.
    #[inline(always)]
    pub const fn virtualize(self, offset: u8) -> Self {
        Self(self.0 >> offset)
    }
}

impl PartialEq<u8> for LevelMask {
    #[inline]
    fn eq(&self, other: &u8) -> bool {
        self.0 == *other
    }
}

impl BitOr for LevelMask {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for LevelMask {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl From<LevelMask> for u8 {
    #[inline(always)]
    fn from(m: LevelMask) -> u8 {
        m.0
    }
}

impl std::fmt::Debug for LevelMask {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:03b}", self.0))
    }
}

/// Cell tree storage stats.
///
/// NOTE: identical cells are counted each time they occur in the tree.
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct CellTreeStats {
    /// Total number of bits in tree.
    pub bit_count: u64,
    /// Total number of cells in tree.
    pub cell_count: u64,
}

impl Add for CellTreeStats {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            bit_count: self.bit_count + rhs.bit_count,
            cell_count: self.cell_count + rhs.cell_count,
        }
    }
}

impl AddAssign for CellTreeStats {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.bit_count += rhs.bit_count;
        self.cell_count += rhs.cell_count;
    }
}

/// Helper struct to print only the root cell in the cell tree.
#[derive(Clone, Copy)]
pub struct DisplayCellRoot<'a>(&'a dyn Cell);

impl std::fmt::Display for DisplayCellRoot<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO: encode on stack
        let data = hex::encode(self.0.data());

        if f.alternate() {
            std::fmt::Display::fmt(&data, f)
        } else {
            let repr_hash = self.0.repr_hash();
            let descriptor = self.0.descriptor();
            f.write_fmt(format_args!(
                "{data}\nbits: {:>4}, refs: {}, hash: {}",
                descriptor.byte_len(),
                descriptor.reference_count(),
                hex::encode(repr_hash),
            ))
        }
    }
}

/// Helper struct to print all cells in the cell tree.
#[derive(Clone, Copy)]
pub struct DisplayCellTree<'a>(&'a dyn Cell);

impl std::fmt::Display for DisplayCellTree<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut stack = vec![(0, self.0)];

        while let Some((level, cell)) = stack.pop() {
            f.write_fmt(format_args!("{:level$}{}\n", "", cell.display_root()))?;

            let reference_count = self.0.reference_count() as u8;
            for i in (0..reference_count).rev() {
                if let Some(child) = cell.reference(i) {
                    stack.push((level + 1, child));
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn correct_level() {
        const LEVEL: [u8; 8] = [0, 1, 1, 2, 1, 2, 2, 3];

        for mask in 0b000..=0b111 {
            assert_eq!(LevelMask(mask).level(), LEVEL[mask as usize]);
        }
    }

    #[test]
    fn correct_hash_index() {
        const HASH_INDEX_TABLE: [[u8; 4]; 8] = [
            // index      // mask
            [0, 0, 0, 0], // 000
            [0, 1, 1, 1], // 001
            [0, 0, 1, 1], // 010
            [0, 1, 2, 2], // 011
            [0, 0, 0, 1], // 100
            [0, 1, 1, 2], // 101
            [0, 0, 1, 2], // 110
            [0, 1, 2, 3], // 111
        ];

        for mask in 0b000..=0b111 {
            let mask = LevelMask(mask);

            for i in 0..=3 {
                let hash_index = mask.hash_index(i);
                assert_eq!(hash_index, HASH_INDEX_TABLE[mask.0 as usize][i as usize]);
            }
        }
    }
}
