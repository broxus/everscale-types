use sha2::Digest;

use crate::cell::{
    Cell, CellContainer, CellDescriptor, CellFamily, CellHash, CellTreeStats, CellType, LevelMask,
    MAX_REF_COUNT,
};
use crate::util::{unlikely, ArrayVec};

/// A trait for describing cell finalization logic.
pub trait Finalizer<C: CellFamily + ?Sized> {
    /// Builds a new cell from cell parts.
    fn finalize_cell(&mut self, cell: CellParts<'_, C>) -> Option<CellContainer<C>>;
}

impl<F, C: CellFamily> Finalizer<C> for F
where
    F: FnMut(CellParts<C>) -> Option<CellContainer<C>>,
    CellContainer<C>: AsRef<dyn Cell<C>>,
{
    fn finalize_cell(&mut self, cell: CellParts<C>) -> Option<CellContainer<C>> {
        (*self)(cell)
    }
}

/// Cell implementation family extension.
pub trait DefaultFinalizer: CellFamily {
    type Finalizer: Finalizer<Self>;

    fn default_finalizer() -> Self::Finalizer;
}

/// Partially assembled cell.
pub struct CellParts<'a, C: CellFamily + ?Sized> {
    /// Cell tree storage stats.
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
    pub references: ArrayVec<CellContainer<C>, MAX_REF_COUNT>,

    /// Cell data slice.
    pub data: &'a [u8],
}

impl<'a, C: CellFamily + 'a> CellParts<'a, C>
where
    CellContainer<C>: AsRef<dyn Cell<C>>,
{
    /// Validates cell and computes all hashes.
    pub fn compute_hashes(&self) -> Option<Vec<(CellHash, u16)>> {
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
                return None;
            };

            const PRUNED_BRANCH: u8 = CellType::PrunedBranch.to_byte();
            const MERKLE_PROOF: u8 = CellType::MerkleProof.to_byte();
            const MERKLE_UPDATE: u8 = CellType::MerkleUpdate.to_byte();
            const LIBRARY_REFERENCE: u8 = CellType::LibraryReference.to_byte();

            match first_byte {
                // 8 bits type, 8 bits level mask, level x (hash, depth)
                PRUNED_BRANCH => {
                    if unlikely(level == 0) {
                        return None;
                    }

                    let expected_bit_len = 8 + 8 + level * (HASH_BITS + DEPTH_BITS);
                    if unlikely(bit_len != expected_bit_len || !references.is_empty()) {
                        return None;
                    }

                    let stored_mask = self.data.get(1).copied().unwrap_or_default();
                    if unlikely(level_mask != stored_mask) {
                        return None;
                    }

                    hashes_len = 1;
                    (CellType::PrunedBranch, level_mask)
                }
                // 8 bits type, hash, depth
                MERKLE_PROOF => {
                    const EXPECTED_BIT_LEN: usize = 8 + HASH_BITS + DEPTH_BITS;
                    if unlikely(bit_len != EXPECTED_BIT_LEN || references.len() != 1) {
                        return None;
                    }

                    (CellType::MerkleProof, self.children_mask.virtualize(1))
                }
                // 8 bits type, 2 x (hash, depth)
                MERKLE_UPDATE => {
                    const EXPECTED_BIT_LEN: usize = 8 + 2 * (HASH_BITS + DEPTH_BITS);
                    if unlikely(bit_len != EXPECTED_BIT_LEN || references.len() != 2) {
                        return None;
                    }

                    (CellType::MerkleUpdate, self.children_mask.virtualize(1))
                }
                // 8 bits type, hash
                LIBRARY_REFERENCE => {
                    const EXPECTED_BIT_LEN: usize = 8 + HASH_BITS;
                    if unlikely(bit_len != EXPECTED_BIT_LEN || !references.is_empty()) {
                        return None;
                    }

                    (CellType::LibraryReference, LevelMask::EMPTY)
                }
                _ => return None,
            }
        } else {
            (CellType::Ordinary, self.children_mask)
        };

        if unlikely(computed_level_mask != level_mask) {
            return None;
        }

        let level_offset = cell_type.is_merkle() as u8;

        let mut hashes = Vec::<(CellHash, u16)>::with_capacity(hashes_len);
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
                depth = std::cmp::max(depth, child_depth.checked_add(1)?);

                hasher.update(child_depth.to_be_bytes());
            }

            for child in references {
                let child_hash = child.as_ref().hash(level as u8 + level_offset);
                hasher.update(child_hash.as_slice());
            }

            let hash = hasher.finalize().into();
            hashes.push((hash, depth));
        }

        Some(hashes)
    }
}
