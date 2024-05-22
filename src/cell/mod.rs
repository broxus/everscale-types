//! Cell tree implementation.

use std::ops::{BitOr, BitOrAssign};
use std::str::FromStr;

use crate::error::{Error, ParseHashBytesError};
use crate::util::Bitstring;

pub use self::builder::{CellBuilder, CellRefsBuilder, Store};
pub use self::cell_context::{CellContext, CellParts, LoadMode};
pub use self::cell_impl::{StaticCell, VirtualCellWrapper};
pub use self::slice::{CellSlice, CellSliceParts, CellSliceRange, CellSliceSize, ExactSize, Load};
pub use self::usage_tree::{UsageTree, UsageTreeMode, UsageTreeWithSubtrees};

#[cfg(not(feature = "sync"))]
pub use self::cell_impl::rc::{Cell, CellInner};

#[cfg(feature = "sync")]
pub use self::cell_impl::sync::{Cell, CellInner};

pub use everscale_types_proc::{Load, Store};

/// Generic cell implementation.
mod cell_impl;

/// Traits for gas accounting and resolving exotic cells.
mod cell_context;

/// Cell view utils.
mod slice;

/// Cell creation utils.
mod builder;

mod usage_tree;

#[cfg(feature = "sync")]
#[doc(hidden)]
mod __checks {
    use super::*;

    assert_impl_all!(Cell: Send);
    assert_impl_all!(CellSlice: Send);
    assert_impl_all!(CellBuilder: Send);
}

/// Marker trait which allows casting lazy-loaded data.
pub trait EquivalentRepr<T> {}

/// All types are equivalent to itself.
impl<T> EquivalentRepr<T> for T {}

/// Cell implementation family.
pub trait CellFamily: Sized {
    /// The default cell context type.
    type EmptyCellContext: CellContext;

    /// Creates an empty cell.
    ///
    /// NOTE: in most cases empty cell is ZST.
    fn empty_cell() -> Cell;

    /// Returns a static reference to the empty cell
    fn empty_cell_ref() -> &'static DynCell;

    /// Creates an empty cell context.
    fn empty_context() -> Self::EmptyCellContext;

    /// Returns a static reference to the cell with all zeros.
    fn all_zeros_ref() -> &'static DynCell;

    /// Returns a static reference to the cell with all ones.
    fn all_ones_ref() -> &'static DynCell;

    /// Creates a virtualized cell from the specified cell.
    fn virtualize(cell: Cell) -> Cell;
}

/// Dyn trait type alias.
#[cfg(not(feature = "sync"))]
pub type DynCell = dyn CellImpl;

/// Dyn trait type alias.
#[cfg(feature = "sync")]
pub type DynCell = dyn CellImpl + Send + Sync;

impl AsRef<DynCell> for DynCell {
    #[inline(always)]
    fn as_ref(&self) -> &Self {
        self
    }
}

impl AsMut<DynCell> for DynCell {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

/// Represents the interface of a well-formed cell.
///
/// Since all basic operations are implements via dynamic dispatch,
/// all high-level helper methods are implemented for `dyn Cell`.
pub trait CellImpl {
    /// Unwraps the root cell from the usage tracking.
    fn untrack(self: CellInner<Self>) -> Cell;

    /// Returns cell descriptor.
    ///
    /// # See also
    ///
    /// Cell descriptor contains some tightly packed info about the cell.
    /// If you want convenient methods to access it use:
    /// [`cell_type`], [`level_mask`], [`reference_count`], [`is_exotic`]
    ///
    /// [`cell_type`]: CellDescriptor::cell_type
    /// [`level_mask`]: CellDescriptor::level_mask
    /// [`reference_count`]: CellDescriptor::reference_count
    /// [`is_exotic`]: CellDescriptor::is_exotic
    fn descriptor(&self) -> CellDescriptor;

    /// Returns the raw data of this cell.
    fn data(&self) -> &[u8];

    /// Returns the data size of this cell in bits.
    fn bit_len(&self) -> u16;

    /// Returns a reference to the Nth child cell.
    fn reference(&self, index: u8) -> Option<&DynCell>;

    /// Returns the Nth child cell.
    fn reference_cloned(&self, index: u8) -> Option<Cell>;

    /// Returns this cell as a virtualized cell, so that all hashes
    /// and depths will have an offset.
    fn virtualize(&self) -> &DynCell;

    /// Returns cell hash for the specified level.
    ///
    /// Cell representation hash is the hash at the maximum level ([`LevelMask::MAX_LEVEL`]).
    /// Use `repr_hash` as a simple alias for this.
    fn hash(&self, level: u8) -> &HashBytes;

    /// Returns cell depth for the specified level.
    fn depth(&self, level: u8) -> u16;

    /// Consumes the first child during the deep drop.
    fn take_first_child(&mut self) -> Option<Cell>;

    /// Replaces the first child with the provided parent during the deep drop.
    ///
    /// Returns `Ok(child)` if child was successfully replaced,
    /// `Err(parent)` otherwise.
    fn replace_first_child(&mut self, parent: Cell) -> Result<Cell, Cell>;

    /// Consumes the next child (except first) during the deep drop.
    fn take_next_child(&mut self) -> Option<Cell>;

    /// Returns the sum of all bits and cells of all elements in the cell tree
    /// (including this cell).
    ///
    /// NOTE: identical cells are counted each time they occur in the tree.
    #[cfg(feature = "stats")]
    fn stats(&self) -> CellTreeStats;
}

impl DynCell {
    /// Computes cell type from descriptor bytes.
    #[inline]
    pub fn cell_type(&self) -> CellType {
        self.descriptor().cell_type()
    }

    /// Computes the cell level from the level mask.
    #[inline]
    pub fn level(&self) -> u8 {
        self.descriptor().level_mask().level()
    }

    /// Computes the level mask from the descriptor bytes.
    #[inline]
    pub fn level_mask(&self) -> LevelMask {
        self.descriptor().level_mask()
    }

    /// Computes the number of child cells from descriptor bytes.
    #[inline]
    pub fn reference_count(&self) -> u8 {
        self.descriptor().reference_count()
    }

    /// Tries to load the specified child cell as slice.
    /// Returns an error if the loaded cell is absent or is pruned.
    pub fn get_reference_as_slice(&self, index: u8) -> Result<CellSlice<'_>, Error> {
        match self.reference(index) {
            Some(cell) => CellSlice::new(cell),
            None => Err(Error::CellUnderflow),
        }
    }

    /// Returns whether the cell is not [`Ordinary`].
    ///
    /// [`Ordinary`]: CellType::Ordinary
    #[inline]
    pub fn is_exotic(&self) -> bool {
        self.descriptor().is_exotic()
    }

    /// Returns a representation hash of the cell.
    #[inline]
    pub fn repr_hash(&self) -> &HashBytes {
        self.hash(LevelMask::MAX_LEVEL)
    }

    /// Returns a representation depth of the cell.
    #[inline]
    pub fn repr_depth(&self) -> u16 {
        self.depth(LevelMask::MAX_LEVEL)
    }

    /// Returns true if the cell is empty (no bits, no refs).
    pub fn is_empty(&self) -> bool {
        self.hash(LevelMask::MAX_LEVEL) == EMPTY_CELL_HASH
    }

    /// Creates an iterator through child nodes.
    #[inline]
    pub fn references(&self) -> RefsIter<'_> {
        RefsIter {
            cell: self,
            max: self.reference_count(),
            index: 0,
        }
    }

    /// Returns this cell as a cell slice.
    /// Returns an error if the cell is pruned.
    #[inline]
    pub fn as_slice(&'_ self) -> Result<CellSlice<'_>, Error> {
        CellSlice::new(self)
    }

    /// Returns this cell as a cell slice.
    ///
    /// # Safety
    ///
    /// The following must be true:
    /// - cell is not pruned
    #[inline]
    pub unsafe fn as_slice_unchecked(&'_ self) -> CellSlice<'_> {
        CellSlice::new_unchecked(self)
    }

    /// Recursively computes the count of distinct cells returning
    /// the total storage used by this dag taking into account the
    /// identification of equal cells.
    pub fn compute_unique_stats(&self, limit: usize) -> Option<CellTreeStats> {
        StorageStat::compute_for_cell(self, limit)
    }

    /// Returns an object that implements [`Debug`] for printing only
    /// the root cell of the cell tree.
    ///
    /// [`Debug`]: std::fmt::Debug
    #[inline]
    pub fn debug_root(&'_ self) -> DebugCell<'_> {
        DebugCell(self)
    }

    /// Returns an object that implements [`Display`] for printing only
    /// the root cell of the cell tree.
    ///
    /// [`Display`]: std::fmt::Display
    #[inline]
    pub fn display_root(&'_ self) -> DisplayCellRoot<'_> {
        DisplayCellRoot {
            cell: self,
            level: 0,
        }
    }

    /// Returns an object that implements [`Display`] for printing all
    /// cells in the cell tree.
    ///
    /// [`Display`]: std::fmt::Display
    #[inline]
    pub fn display_tree(&'_ self) -> DisplayCellTree<'_> {
        DisplayCellTree(self)
    }

    /// Returns an object which will display cell data as a bitstring
    /// with a termination bit.
    #[inline]
    pub fn display_data(&self) -> impl std::fmt::Display + std::fmt::Binary + '_ {
        struct DisplayData<'a>(&'a DynCell);

        impl std::fmt::Display for DisplayData<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(
                    &Bitstring {
                        bytes: self.0.data(),
                        bit_len: self.0.bit_len(),
                    },
                    f,
                )
            }
        }

        impl std::fmt::Binary for DisplayData<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Binary::fmt(
                    &Bitstring {
                        bytes: self.0.data(),
                        bit_len: self.0.bit_len(),
                    },
                    f,
                )
            }
        }

        DisplayData(self)
    }

    /// Converts this cell into a slice and tries to load the specified type from it.
    ///
    /// NOTE: parsing `Cell` will load the first reference!
    #[inline]
    pub fn parse<'a, T: Load<'a>>(&'a self) -> Result<T, Error> {
        T::load_from(&mut ok!(self.as_slice()))
    }
}

impl std::fmt::Debug for DynCell {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        crate::util::debug_struct_field2_finish(
            f,
            "Cell",
            "ty",
            &self.cell_type(),
            "hash",
            self.repr_hash(),
        )
    }
}

impl Eq for DynCell {}

impl PartialEq<DynCell> for DynCell {
    #[inline]
    fn eq(&self, other: &DynCell) -> bool {
        self.repr_hash() == other.repr_hash()
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for DynCell {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let boc = crate::boc::Boc::encode(self);
        if serializer.is_human_readable() {
            serializer.serialize_str(&crate::util::encode_base64(boc))
        } else {
            serializer.serialize_bytes(&boc)
        }
    }
}

/// An iterator through child nodes.
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct RefsIter<'a> {
    cell: &'a DynCell,
    max: u8,
    index: u8,
}

impl<'a> RefsIter<'a> {
    /// Returns a cell by children of which we are iterating.
    #[inline]
    pub fn cell(&self) -> &'a DynCell {
        self.cell
    }

    /// Returns a reference to the next() value without advancing the iterator.
    #[inline]
    pub fn peek(&self) -> Option<&'a DynCell> {
        if self.index >= self.max {
            None
        } else {
            self.cell.reference(self.index)
        }
    }

    /// Returns a cloned reference to the next() value without advancing the iterator.
    #[inline]
    pub fn peek_cloned(&self) -> Option<Cell> {
        if self.index >= self.max {
            None
        } else {
            self.cell.reference_cloned(self.index)
        }
    }

    /// Returns a reference to the next_back() value without advancing the iterator.
    #[inline]
    pub fn peek_prev(&self) -> Option<&'a DynCell> {
        if self.index > 0 {
            self.cell.reference(self.index - 1)
        } else {
            None
        }
    }

    /// Returns a cloned reference to the next_back() value without advancing the iterator.
    #[inline]
    pub fn peek_prev_cloned(&self) -> Option<Cell> {
        if self.index > 0 {
            self.cell.reference_cloned(self.index - 1)
        } else {
            None
        }
    }

    /// Creates an iterator through child nodes which produces cloned references.
    #[inline]
    pub fn cloned(self) -> ClonedRefsIter<'a> {
        ClonedRefsIter { inner: self }
    }
}

impl Clone for RefsIter<'_> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            cell: self.cell,
            max: self.max,
            index: self.index,
        }
    }
}

impl<'a> Iterator for RefsIter<'a> {
    type Item = &'a DynCell;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.max {
            None
        } else {
            let child = self.cell.reference(self.index);
            self.index += 1;
            child
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.max.saturating_sub(self.index) as usize;
        (remaining, Some(remaining))
    }
}

impl<'a> DoubleEndedIterator for RefsIter<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.max > self.index {
            self.max -= 1;
            self.cell.reference(self.max)
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
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ClonedRefsIter<'a> {
    inner: RefsIter<'a>,
}

impl<'a> ClonedRefsIter<'a> {
    /// Returns a cell by children of which we are iterating.
    #[inline]
    pub fn cell(&self) -> &'a DynCell {
        self.inner.cell
    }

    /// Returns a reference to the next() value without advancing the iterator.
    #[inline]
    pub fn peek(&self) -> Option<Cell> {
        self.inner.peek_cloned()
    }

    /// Returns a reference to the next_back() value without advancing the iterator.
    #[inline]
    pub fn peek_prev(&self) -> Option<Cell> {
        self.inner.peek_prev_cloned()
    }
}

impl Clone for ClonedRefsIter<'_> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a> Iterator for ClonedRefsIter<'a> {
    type Item = Cell;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.inner.index >= self.inner.max {
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
        if self.inner.max > self.inner.index {
            self.inner.max -= 1;
            self.inner.cell.reference_cloned(self.inner.max)
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

/// Type alias for a cell hash.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[repr(transparent)]
pub struct HashBytes(pub [u8; 32]);

impl HashBytes {
    /// Array of zero bytes.
    pub const ZERO: Self = Self([0; 32]);

    /// Converts slice to a hash bytes.
    ///
    /// # Panics
    ///
    /// Panics if the length of the slice is not 32 bytes.
    #[inline]
    pub fn from_slice(slice: &[u8]) -> Self {
        Self(slice.try_into().expect("slice with incorrect length"))
    }

    /// Wraps a reference to an internal array into a newtype reference.
    #[inline(always)]
    pub const fn wrap(value: &[u8; 32]) -> &Self {
        // SAFETY: HashBytes is #[repr(transparent)]
        unsafe { &*(value as *const [u8; 32] as *const Self) }
    }

    /// Returns a slice containing the entire array.
    pub const fn as_slice(&self) -> &[u8] {
        self.0.as_slice()
    }

    /// Returns a mutable slice containing the entire array.
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        self.0.as_mut_slice()
    }

    /// Returns an internal array.
    pub const fn as_array(&self) -> &[u8; 32] {
        &self.0
    }

    /// Returns a mutable internal array.
    pub fn as_mut_array(&mut self) -> &mut [u8; 32] {
        &mut self.0
    }

    /// Returns a raw pointer to the slice's buffer.
    #[inline(always)]
    pub const fn as_ptr(&self) -> *const u8 {
        &self.0 as *const [u8] as *const u8
    }

    /// Returns a first chunk of 8 bytes.
    pub const fn first_chunk(&self) -> &[u8; 8] {
        match self.0.first_chunk::<8>() {
            Some(chunk) => chunk,
            // SAFETY: Const unwrap go brr
            None => unsafe { std::hint::unreachable_unchecked() },
        }
    }
}

impl Default for HashBytes {
    #[inline(always)]
    fn default() -> Self {
        Self::ZERO
    }
}

impl AsRef<[u8; 32]> for HashBytes {
    #[inline(always)]
    fn as_ref(&self) -> &[u8; 32] {
        &self.0
    }
}

impl AsRef<[u8]> for HashBytes {
    #[inline(always)]
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl AsMut<[u8; 32]> for HashBytes {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut [u8; 32] {
        &mut self.0
    }
}

impl AsMut<[u8]> for HashBytes {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut [u8] {
        self.0.as_mut()
    }
}

impl std::borrow::Borrow<[u8]> for HashBytes {
    #[inline(always)]
    fn borrow(&self) -> &[u8] {
        &self.0
    }
}

impl std::borrow::BorrowMut<[u8]> for HashBytes {
    #[inline(always)]
    fn borrow_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl std::borrow::Borrow<HashBytes> for [u8; 32] {
    #[inline(always)]
    fn borrow(&self) -> &HashBytes {
        HashBytes::wrap(self)
    }
}

impl PartialEq<[u8; 32]> for HashBytes {
    #[inline(always)]
    fn eq(&self, other: &[u8; 32]) -> bool {
        &self.0 == other
    }
}

impl PartialEq<HashBytes> for [u8; 32] {
    #[inline(always)]
    fn eq(&self, other: &HashBytes) -> bool {
        self == &other.0
    }
}

impl PartialEq<[u8]> for HashBytes {
    #[inline(always)]
    fn eq(&self, other: &[u8]) -> bool {
        self.0 == other
    }
}

impl PartialEq<HashBytes> for [u8] {
    #[inline(always)]
    fn eq(&self, other: &HashBytes) -> bool {
        self == other.0
    }
}

impl From<[u8; 32]> for HashBytes {
    #[inline(always)]
    fn from(value: [u8; 32]) -> Self {
        Self(value)
    }
}

impl From<sha2::digest::Output<sha2::Sha256>> for HashBytes {
    #[inline(always)]
    fn from(value: sha2::digest::Output<sha2::Sha256>) -> Self {
        Self(value.into())
    }
}

#[cfg(feature = "blake3")]
impl From<blake3::Hash> for HashBytes {
    #[inline(always)]
    fn from(value: blake3::Hash) -> Self {
        Self(value.into())
    }
}

impl From<HashBytes> for [u8; 32] {
    #[inline(always)]
    fn from(value: HashBytes) -> Self {
        value.0
    }
}

impl FromStr for HashBytes {
    type Err = ParseHashBytesError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut result = Self::default();
        match s.len() {
            64 => {
                if let Err(e) = hex::decode_to_slice(s, &mut result.0) {
                    return Err(ParseHashBytesError::InvalidHex(e));
                }
            }
            66 => {
                if let Err(e) = hex::decode_to_slice(&s[2..], &mut result.0) {
                    return Err(ParseHashBytesError::InvalidHex(e));
                }
            }
            #[cfg(feature = "base64")]
            44 => {
                if let Err(e) = crate::util::decode_base64_slice(s, &mut result.0) {
                    return Err(ParseHashBytesError::InvalidBase64(e));
                }
            }
            _ => return Err(ParseHashBytesError::UnexpectedStringLength),
        }
        Ok(result)
    }
}

impl std::fmt::Display for HashBytes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut output = [0u8; 64];
        hex::encode_to_slice(self, &mut output).ok();

        // SAFETY: output is guaranteed to contain only [0-9a-f]
        let output = unsafe { std::str::from_utf8_unchecked(&output) };
        f.write_str(output)
    }
}

impl std::fmt::Debug for HashBytes {
    #[inline(always)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

impl<I> std::ops::Index<I> for HashBytes
where
    [u8; 32]: std::ops::Index<I>,
{
    type Output = <[u8; 32] as std::ops::Index<I>>::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        std::ops::Index::index(&self.0, index)
    }
}

impl<I> std::ops::IndexMut<I> for HashBytes
where
    [u8; 32]: std::ops::IndexMut<I>,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        std::ops::IndexMut::index_mut(&mut self.0, index)
    }
}

#[cfg(any(feature = "rand", test))]
impl rand::distributions::Distribution<HashBytes> for rand::distributions::Standard {
    #[inline]
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> HashBytes {
        HashBytes(rand::distributions::Standard.sample(rng))
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for HashBytes {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        if serializer.is_human_readable() {
            let mut output = [0u8; 64];
            hex::encode_to_slice(self.0.as_slice(), &mut output).ok();

            // SAFETY: output is guaranteed to contain only [0-9a-f]
            let output = unsafe { std::str::from_utf8_unchecked(&output) };
            serializer.serialize_str(output)
        } else {
            serializer.serialize_bytes(&self.0)
        }
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for HashBytes {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use ::serde::de::{Error, Visitor};

        struct HashBytesHexVisitor;

        impl<'de> Visitor<'de> for HashBytesHexVisitor {
            type Value = HashBytes;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("hex-encoded byte array of size 32")
            }

            fn visit_str<E: Error>(self, value: &str) -> Result<Self::Value, E> {
                let mut result = HashBytes([0; 32]);
                match hex::decode_to_slice(value, &mut result.0) {
                    Ok(()) => Ok(result),
                    Err(_) => Err(Error::invalid_value(
                        serde::de::Unexpected::Str(value),
                        &self,
                    )),
                }
            }
        }

        pub struct HashBytesRawVisitor;

        impl<'de> Visitor<'de> for HashBytesRawVisitor {
            type Value = HashBytes;

            fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.write_fmt(format_args!("a byte array of size 32"))
            }

            fn visit_bytes<E: Error>(self, v: &[u8]) -> Result<Self::Value, E> {
                v.try_into()
                    .map(HashBytes)
                    .map_err(|_e| Error::invalid_length(v.len(), &self))
            }
        }

        if deserializer.is_human_readable() {
            deserializer.deserialize_str(HashBytesHexVisitor)
        } else {
            deserializer.deserialize_bytes(HashBytesRawVisitor)
        }
    }
}

/// Hash of an empty (0 bits of data, no refs) ordinary cell.
pub static EMPTY_CELL_HASH: &HashBytes = HashBytes::wrap(&[
    0x96, 0xa2, 0x96, 0xd2, 0x24, 0xf2, 0x85, 0xc6, 0x7b, 0xee, 0x93, 0xc3, 0x0f, 0x8a, 0x30, 0x91,
    0x57, 0xf0, 0xda, 0xa3, 0x5d, 0xc5, 0xb8, 0x7e, 0x41, 0x0b, 0x78, 0x63, 0x0a, 0x09, 0xcf, 0xc7,
]);

/// Well-formed cell type.
#[derive(Default, Debug, Copy, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CellType {
    /// Cell of this type just stores data and references.
    #[default]
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

    /// Returns whether the cell is a pruned branch
    #[inline]
    pub const fn is_pruned_branch(self) -> bool {
        matches!(self, Self::PrunedBranch)
    }

    /// Encodes cell type as byte.
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

    /// Decodes any cell type from byte.
    #[inline]
    pub const fn from_byte(byte: u8) -> Option<Self> {
        Some(match byte {
            0xff => CellType::Ordinary,
            1 => CellType::PrunedBranch,
            2 => CellType::LibraryReference,
            3 => CellType::MerkleProof,
            4 => CellType::MerkleUpdate,
            _ => return None,
        })
    }

    /// Decodes exotic cell type from byte.
    #[inline]
    pub const fn from_byte_exotic(byte: u8) -> Option<Self> {
        Some(match byte {
            1 => CellType::PrunedBranch,
            2 => CellType::LibraryReference,
            3 => CellType::MerkleProof,
            4 => CellType::MerkleUpdate,
            _ => return None,
        })
    }
}

impl From<CellType> for u8 {
    #[inline]
    fn from(cell_type: CellType) -> u8 {
        cell_type.to_byte()
    }
}

/// Tightly packed info about a cell.
#[derive(Hash, Debug, Clone, Copy)]
#[repr(C)]
pub struct CellDescriptor {
    /// First descriptor byte with a generic info about cell.
    pub d1: u8,
    /// Second descriptor byte with a packed data size.
    pub d2: u8,
}

impl CellDescriptor {
    /// Bit mask to store the number of references in the descriptor.
    pub const REF_COUNT_MASK: u8 = 0b0000_0111;
    /// Bit mask to store the `is_exotic` flag in the descriptor.
    pub const IS_EXOTIC_MASK: u8 = 0b0000_1000;
    /// Bit mask to store the `store_hashes` flag in the descriptor.
    pub const STORE_HASHES_MASK: u8 = 0b0001_0000;
    /// _de Brujn_ level presence mask in the descriptor.
    pub const LEVEL_MASK: u8 = 0b1110_0000;

    /// Computes d1 descriptor byte from parts
    #[inline(always)]
    pub const fn compute_d1(level_mask: LevelMask, is_exotic: bool, ref_count: u8) -> u8 {
        (level_mask.0 << 5) | ((is_exotic as u8) << 3) | (ref_count & Self::REF_COUNT_MASK)
    }

    /// Computes d2 descriptor byte from cell length in bits
    #[inline(always)]
    pub const fn compute_d2(bit_len: u16) -> u8 {
        (((bit_len >> 2) as u8) & !0b1) | ((bit_len % 8 != 0) as u8)
    }

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
    pub const fn reference_count(self) -> u8 {
        self.d1 & Self::REF_COUNT_MASK
    }

    /// Computes hash count.
    ///
    /// NOTE: Guaranteed to be in range 1..=4.
    #[inline(always)]
    pub const fn hash_count(self) -> u8 {
        let level = self.level_mask().level();
        if self.is_exotic() && self.reference_count() == 0 && level > 0 {
            1 // pruned branch always has 1 hash
        } else {
            level + 1
        }
    }

    /// Returns whether the cell is not [`Ordinary`].
    ///
    /// [`Ordinary`]: CellType::Ordinary
    #[inline(always)]
    pub const fn is_exotic(self) -> bool {
        self.d1 & Self::IS_EXOTIC_MASK != 0
    }

    /// Returns whether this cell is a pruned branch cell
    #[inline(always)]
    pub const fn is_pruned_branch(self) -> bool {
        self.is_exotic() && self.reference_count() == 0 && !self.level_mask().is_empty()
    }

    /// Returns whether this cell type is Merkle proof or Merkle update.
    #[inline(always)]
    pub const fn is_merkle(self) -> bool {
        self.is_exotic() && self.reference_count() != 0
    }

    /// Returns whether this cell refers to some external data.
    #[inline(always)]
    pub const fn is_absent(self) -> bool {
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

/// _de Brujn_ level presence bitset.
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

    /// Returns true if there are no levels in mask.
    #[inline(always)]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
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

    /// Returns whether the specified level is included into the mask.
    pub const fn contains(self, level: u8) -> bool {
        level == 0 || self.0 & LevelMask::from_level(level).0 != 0
    }

    /// Creates a new mask, shifted by the offset.
    #[inline(always)]
    pub const fn virtualize(self, offset: u8) -> Self {
        Self(self.0 >> offset)
    }

    /// Encodes level mask as byte.
    #[inline]
    pub const fn to_byte(self) -> u8 {
        self.0
    }
}

impl IntoIterator for LevelMask {
    type Item = u8;
    type IntoIter = LevelMaskIter;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        // Include zero level
        LevelMaskIter(1 | self.0 << 1)
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

/// _de Brujn_ level presence bitset iterator.
#[derive(Clone)]
pub struct LevelMaskIter(u8);

impl Iterator for LevelMaskIter {
    type Item = u8;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        (self.0 != 0).then(|| {
            //  111 - 1   = 110
            // !110       = 001
            //  111 & 001 = 001
            let mask = self.0 & !(self.0 - 1);

            // 111 & !001 = 110
            self.0 &= !mask;

            mask.trailing_zeros() as u8
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.0.count_ones() as usize;
        (len, Some(len))
    }
}

/// Cell tree storage stats.
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct CellTreeStats {
    /// Total number of bits in tree.
    pub bit_count: u64,
    /// Total number of cells in tree.
    pub cell_count: u64,
}

impl CellTreeStats {
    /// The additive identity for this type, i.e. `0`.
    pub const ZERO: Self = CellTreeStats {
        bit_count: 0,
        cell_count: 0,
    };
}

impl std::ops::Add for CellTreeStats {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            bit_count: self.bit_count.saturating_add(rhs.bit_count),
            cell_count: self.cell_count.saturating_add(rhs.cell_count),
        }
    }
}

impl std::ops::AddAssign for CellTreeStats {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.bit_count = self.bit_count.saturating_add(rhs.bit_count);
        self.cell_count = self.cell_count.saturating_add(rhs.cell_count);
    }
}

impl std::ops::Add<CellSliceSize> for CellTreeStats {
    type Output = Self;

    #[inline]
    fn add(self, rhs: CellSliceSize) -> Self::Output {
        Self {
            bit_count: self.bit_count.saturating_add(rhs.bits as _),
            cell_count: self.cell_count.saturating_add(rhs.refs as _),
        }
    }
}

impl std::iter::Sum for CellTreeStats {
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        let mut res = Self::ZERO;
        for item in iter {
            res += item;
        }
        res
    }
}

impl std::ops::AddAssign<CellSliceSize> for CellTreeStats {
    fn add_assign(&mut self, rhs: CellSliceSize) {
        self.bit_count = self.bit_count.saturating_add(rhs.bits as _);
        self.cell_count = self.cell_count.saturating_add(rhs.refs as _);
    }
}

impl std::ops::Sub for CellTreeStats {
    type Output = Self;

    #[inline]
    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl std::ops::SubAssign for CellTreeStats {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.bit_count = self.bit_count.saturating_sub(rhs.bit_count);
        self.cell_count = self.cell_count.saturating_sub(rhs.cell_count);
    }
}

impl std::ops::SubAssign<CellSliceSize> for CellTreeStats {
    #[inline]
    fn sub_assign(&mut self, rhs: CellSliceSize) {
        self.bit_count = self.bit_count.saturating_sub(rhs.bits as _);
        self.cell_count = self.cell_count.saturating_sub(rhs.refs as _);
    }
}

/// A helper to track the size of the unique data in multiple cell trees.
///
/// NOTE: It uses hashes for deduplication, so you can only use it for
/// fully computed and valid trees.
pub struct StorageStat<'a> {
    visited: ahash::HashSet<&'a HashBytes>,
    stack: Vec<RefsIter<'a>>,
    stats: CellTreeStats,
    limit: usize,
}

impl<'a> StorageStat<'a> {
    /// Recursively computes the count of distinct cells returning
    /// the total storage used by this dag taking into account the
    /// identification of equal cells.
    ///
    /// Root slice does not count as cell. A slice subrange of
    /// cells is used during computation.
    pub fn compute_for_slice<'b: 'a>(
        slice: &'a CellSlice<'b>,
        limit: usize,
    ) -> Option<CellTreeStats> {
        let mut this = Self::with_limit(limit);
        if this.add_slice(slice) {
            Some(this.stats)
        } else {
            None
        }
    }

    /// Recursively computes the count of distinct cells returning
    /// the total storage used by this dag taking into account the
    /// identification of equal cells.
    pub fn compute_for_cell(cell: &'a DynCell, limit: usize) -> Option<CellTreeStats> {
        let mut this = Self::with_limit(limit);
        if this.add_cell(cell) {
            Some(this.stats)
        } else {
            None
        }
    }

    /// Creates a new storage stat state with an explicit limit.
    pub fn with_limit(limit: usize) -> Self {
        Self {
            visited: Default::default(),
            stack: Vec::new(),
            stats: CellTreeStats::ZERO,
            limit,
        }
    }

    /// Creates a new storage stat state without a limit.
    pub fn unlimited() -> Self {
        Self::with_limit(usize::MAX)
    }

    /// Returns the current tree stats.
    pub fn stats(&self) -> CellTreeStats {
        self.stats
    }

    /// Merges current stats with the stats from the provided cell tree.
    ///
    /// Returns `false` if the limit was reached.
    pub fn add_cell(&mut self, cell: &'a DynCell) -> bool {
        if !self.visited.insert(cell.repr_hash()) {
            return true;
        }

        self.stats.bit_count += cell.bit_len() as u64;
        self.stats.cell_count += 1;

        self.stack.clear();
        self.stack.push(cell.references());
        self.reduce_stack()
    }

    /// Merges current stats with the stats from the provided slice.
    ///
    /// Returns `false` if the limit was reached.
    pub fn add_slice(&mut self, slice: &CellSlice<'a>) -> bool {
        self.stats.bit_count += slice.remaining_bits() as u64;

        self.stack.clear();
        self.stack.push(slice.references());
        self.reduce_stack()
    }

    fn reduce_stack(&mut self) -> bool {
        'outer: while let Some(item) = self.stack.last_mut() {
            for cell in item.by_ref() {
                if !self.visited.insert(cell.repr_hash()) {
                    continue;
                }

                if self.stats.cell_count >= self.limit as u64 {
                    return false;
                }

                self.stats.bit_count += cell.bit_len() as u64;
                self.stats.cell_count += 1;

                let next = cell.references();
                if next.max > 0 {
                    self.stack.push(next);
                    continue 'outer;
                }
            }

            self.stack.pop();
        }

        true
    }
}

/// Helper struct to debug print the root cell.
#[derive(Clone, Copy)]
pub struct DebugCell<'a>(&'a DynCell);

impl std::fmt::Debug for DebugCell<'_> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

/// Helper struct to print only the root cell in the cell tree.
#[derive(Clone, Copy)]
pub struct DisplayCellRoot<'a> {
    cell: &'a DynCell,
    level: usize,
}

impl std::fmt::Display for DisplayCellRoot<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO: encode on stack
        let data = hex::encode(self.cell.data());

        let indent = self.level * 2;
        if f.alternate() {
            f.write_fmt(format_args!("{:indent$}{data}\n", ""))
        } else {
            let repr_depth = self.cell.depth(LevelMask::MAX_LEVEL);
            let repr_hash = self.cell.repr_hash();
            let descriptor = self.cell.descriptor();
            f.write_fmt(format_args!(
                "{:indent$}{:?}: {data}\n{:indent$}bits: {:>4}, refs: {}, l: {:?}, depth: {}, hash: {}\n",
                "",
                descriptor.cell_type(),
                "",
                self.cell.bit_len(),
                descriptor.reference_count(),
                descriptor.level_mask(),
                repr_depth,
                repr_hash,
            ))
        }
    }
}

/// Helper struct to print all cells in the cell tree.
#[derive(Clone, Copy)]
pub struct DisplayCellTree<'a>(&'a DynCell);

impl std::fmt::Display for DisplayCellTree<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut stack = vec![(0, self.0)];

        while let Some((level, cell)) = stack.pop() {
            ok!(std::fmt::Display::fmt(&DisplayCellRoot { cell, level }, f));

            let reference_count = cell.reference_count();
            for i in (0..reference_count).rev() {
                if let Some(child) = cell.reference(i) {
                    stack.push((level + 1, child));
                }
            }
        }

        Ok(())
    }
}

/// Max cell data capacity in bits
pub const MAX_BIT_LEN: u16 = 1023;
/// Maximum number of child cells
pub const MAX_REF_COUNT: usize = 4;

#[cfg(feature = "arbitrary")]
impl arbitrary::Arbitrary<'_> for Cell {
    fn arbitrary(u: &mut arbitrary::Unstructured) -> arbitrary::Result<Self> {
        let builder = CellBuilder::arbitrary(u)?;
        builder
            .build()
            .map_err(|_| arbitrary::Error::IncorrectFormat)
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

    #[test]
    fn ultra_virtual_cell_by_ref() {
        let cell = Cell::empty_cell();

        let pruned1 =
            crate::merkle::make_pruned_branch(cell.as_ref(), 0, &mut Cell::empty_context())
                .unwrap();

        let pruned2 =
            crate::merkle::make_pruned_branch(pruned1.as_ref(), 1, &mut Cell::empty_context())
                .unwrap();

        let pruned3 =
            crate::merkle::make_pruned_branch(pruned2.as_ref(), 2, &mut Cell::empty_context())
                .unwrap();

        // Level 3 -> 2
        let pruned3 = pruned3.virtualize();
        assert_eq!(pruned3.repr_hash(), pruned2.repr_hash());
        assert_eq!(pruned3.repr_depth(), pruned2.repr_depth());

        // Level 2 -> 1
        let pruned3 = pruned3.virtualize();
        assert_eq!(pruned3.repr_hash(), pruned1.repr_hash());
        assert_eq!(pruned3.repr_depth(), pruned1.repr_depth());

        // Level 1 -> 0
        let pruned3 = pruned3.virtualize();
        assert_eq!(pruned3.repr_hash(), cell.repr_hash());
        assert_eq!(pruned3.repr_depth(), cell.repr_depth());

        // Level 0 -> 0
        let pruned3 = pruned3.virtualize();
        assert_eq!(pruned3.repr_hash(), cell.repr_hash());
        assert_eq!(pruned3.repr_depth(), cell.repr_depth());

        // Level 0 -> 0 (just in case)
        let pruned3 = pruned3.virtualize();
        assert_eq!(pruned3.repr_hash(), cell.repr_hash());
        assert_eq!(pruned3.repr_depth(), cell.repr_depth());
    }
}
