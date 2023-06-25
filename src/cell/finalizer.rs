use sha2::Digest;

use crate::cell::{Cell, CellDescriptor, CellFamily, HashBytes, CellType, LevelMask, MAX_REF_COUNT};
use crate::error::Error;
use crate::util::{unlikely, ArrayVec};

#[cfg(feature = "stats")]
use crate::cell::CellTreeStats;

/// A trait for describing cell finalization logic.
pub trait Finalizer {
    /// Builds a new cell from cell parts.
    fn finalize_cell(&mut self, cell: CellParts<'_>) -> Result<Cell, Error>;
}

impl<F> Finalizer for F
where
    F: FnMut(CellParts) -> Result<Cell, Error>,
{
    fn finalize_cell(&mut self, cell: CellParts) -> Result<Cell, Error> {
        (*self)(cell)
    }
}

/// Cell family with known default finalizer (noop in most cases).
pub trait DefaultFinalizer: CellFamily {
    /// The default finalizer type.
    type Finalizer: Finalizer;

    /// Creates a default finalizer.
    fn default_finalizer() -> Self::Finalizer;
}

/// Partially assembled cell.
pub struct CellParts<'a> {
    /// Cell tree storage stats.
    #[cfg(feature = "stats")]
    pub stats: CellTreeStats,

    /// Length of this cell's data in bits.
    pub bit_len: u16,

    /// Well-formed cell descriptor.
    pub descriptor: CellDescriptor,

    /// Bitwise OR of child level masks.
    pub children_mask: LevelMask,

    /// Array of child cells.
    ///
    /// NOTE: it is guaranteed that the length of the array is consistent
    /// with the descriptor.
    pub references: ArrayVec<Cell, MAX_REF_COUNT>,

    /// Cell data slice.
    pub data: &'a [u8],
}

impl<'a> CellParts<'a> {
    /// Validates cell and computes all hashes.
    pub fn compute_hashes(&self) -> Result<Vec<(HashBytes, u16)>, Error> {
        const HASH_BITS: usize = 256;
        const DEPTH_BITS: usize = 16;

        let mut descriptor = self.descriptor;
        let bit_len = self.bit_len as usize;
        let level_mask = descriptor.level_mask();
        let level = level_mask.level() as usize;

        let references = self.references.as_ref();

        // `hashes_len` is guaranteed to be in range 1..4
        let mut hashes_len = level + 1;

        let (cell_type, computed_level_mask) = if unlikely(descriptor.is_exotic()) {
            let Some(&first_byte) = self.data.first() else {
                return Err(Error::InvalidCell);
            };

            match CellType::from_byte_exotic(first_byte) {
                // 8 bits type, 8 bits level mask, level x (hash, depth)
                Some(CellType::PrunedBranch) => {
                    if unlikely(level == 0) {
                        return Err(Error::InvalidCell);
                    }

                    let expected_bit_len = 8 + 8 + level * (HASH_BITS + DEPTH_BITS);
                    if unlikely(bit_len != expected_bit_len || !references.is_empty()) {
                        return Err(Error::InvalidCell);
                    }

                    let stored_mask = self.data.get(1).copied().unwrap_or_default();
                    if unlikely(level_mask != stored_mask) {
                        return Err(Error::InvalidCell);
                    }

                    hashes_len = 1;
                    (CellType::PrunedBranch, level_mask)
                }
                // 8 bits type, hash, depth
                Some(CellType::MerkleProof) => {
                    const EXPECTED_BIT_LEN: usize = 8 + HASH_BITS + DEPTH_BITS;
                    if unlikely(bit_len != EXPECTED_BIT_LEN || references.len() != 1) {
                        return Err(Error::InvalidCell);
                    }

                    (CellType::MerkleProof, self.children_mask.virtualize(1))
                }
                // 8 bits type, 2 x (hash, depth)
                Some(CellType::MerkleUpdate) => {
                    const EXPECTED_BIT_LEN: usize = 8 + 2 * (HASH_BITS + DEPTH_BITS);
                    if unlikely(bit_len != EXPECTED_BIT_LEN || references.len() != 2) {
                        return Err(Error::InvalidCell);
                    }

                    (CellType::MerkleUpdate, self.children_mask.virtualize(1))
                }
                // 8 bits type, hash
                Some(CellType::LibraryReference) => {
                    const EXPECTED_BIT_LEN: usize = 8 + HASH_BITS;
                    if unlikely(bit_len != EXPECTED_BIT_LEN || !references.is_empty()) {
                        return Err(Error::InvalidCell);
                    }

                    (CellType::LibraryReference, LevelMask::EMPTY)
                }
                _ => return Err(Error::InvalidCell),
            }
        } else {
            (CellType::Ordinary, self.children_mask)
        };

        if unlikely(computed_level_mask != level_mask) {
            return Err(Error::InvalidCell);
        }

        let level_offset = cell_type.is_merkle() as u8;

        let mut hashes = Vec::<(HashBytes, u16)>::with_capacity(hashes_len);
        for level in 0..hashes_len {
            let mut hasher = sha2::Sha256::new();

            let level_mask = if cell_type == CellType::PrunedBranch {
                level_mask
            } else {
                LevelMask::from_level(level as u8)
            };

            descriptor.d1 &= !(CellDescriptor::LEVEL_MASK | CellDescriptor::STORE_HASHES_MASK);
            descriptor.d1 |= u8::from(level_mask) << 5;
            hasher.update([descriptor.d1, descriptor.d2]);

            if level == 0 {
                hasher.update(self.data);
            } else {
                debug_assert!((level - 1) < hashes.len());
                // SAFETY: new hash is added on each iteration, so there will
                // definitely be a hash, when level>0
                let prev_hash = unsafe { hashes.get_unchecked(level - 1) };
                hasher.update(prev_hash.0.as_slice());
            }

            let mut depth = 0;
            for child in references {
                let child_depth = child.as_ref().depth(level as u8 + level_offset);
                let next_depth = match child_depth.checked_add(1) {
                    Some(next_depth) => next_depth,
                    None => return Err(Error::DepthOverflow),
                };
                depth = std::cmp::max(depth, next_depth);

                hasher.update(child_depth.to_be_bytes());
            }

            for child in references {
                let child_hash = child.as_ref().hash(level as u8 + level_offset);
                hasher.update(child_hash.as_slice());
            }

            let hash = hasher.finalize().into();
            hashes.push((hash, depth));
        }

        Ok(hashes)
    }
}
