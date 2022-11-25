use super::descriptor::{Descriptor, CellType};
use super::level_mask::LevelMask;
use super::{ArcCell, Cell, CellHash, CellTreeStats};
use crate::error::{invalid_data, unexpected_eof};
use crate::util::{unlikely, ArrayVec};

pub trait Finalizer<R = ArcCell> {
    fn finalize_cell(&mut self, cell: PartialCell<R>) -> std::io::Result<R>;
}

impl<F, R> Finalizer<R> for F
where
    F: FnMut(PartialCell<R>) -> std::io::Result<R>,
{
    fn finalize_cell(&mut self, cell: PartialCell<R>) -> std::io::Result<R> {
        (*self)(cell)
    }
}

pub struct PartialCell<'a, R> {
    pub stats: CellTreeStats,
    pub bit_len: u16,
    pub descriptor: Descriptor,
    pub children_mask: LevelMask,
    pub references: ArrayVec<R, 4>,
    pub data: &'a [u8],
}

impl<'a, R> PartialCell<'a, R>
where
    R: AsRef<dyn Cell>,
{
    pub fn compute_hashes(&self) -> std::io::Result<Vec<(CellHash, u16)>> {
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
                return Err(unexpected_eof("empty data for exotic cell"))
            };

            match first_byte {
                // 8 bits type, 8 bits level mask, level x (hash, depth)
                CellType::PRUNED_BRANCH => {
                    if unlikely(level == 0) {
                        return Err(invalid_data("invalid pruned branch level"));
                    }

                    let expected_bit_len = 8 + 8 + level * (HASH_BITS + DEPTH_BITS);
                    if unlikely(bit_len != expected_bit_len) {
                        return Err(invalid_data("pruned branch bit length mismatch"));
                    } else if unlikely(!references.is_empty()) {
                        return Err(invalid_data("pruned branch contains references"));
                    }

                    let stored_mask = self.data.get(1).copied().unwrap_or_default();
                    if unlikely(level_mask != stored_mask) {
                        return Err(invalid_data("pruned branch level mask mismatch"));
                    }

                    hashes_len = 1;
                    (CellType::PrunedBranch, level_mask)
                }
                // 8 bits type, hash, depth
                CellType::MERKLE_PROOF => {
                    const EXPECTED_BIT_LEN: usize = 8 + HASH_BITS + DEPTH_BITS;
                    if unlikely(bit_len != EXPECTED_BIT_LEN) {
                        return Err(invalid_data("merkle proof bit length mismatch"));
                    } else if unlikely(references.len() != 1) {
                        return Err(invalid_data(
                            "merkle proof cell must contain exactly one reference",
                        ));
                    }

                    (CellType::MerkleProof, self.children_mask.virtualize(1))
                }
                // 8 bits type, 2 x (hash, depth)
                CellType::MERKLE_UPDATE => {
                    const EXPECTED_BIT_LEN: usize = 8 + 2 * (HASH_BITS + DEPTH_BITS);
                    if unlikely(bit_len != EXPECTED_BIT_LEN) {
                        return Err(invalid_data("merkle update bit length mismatch"));
                    } else if unlikely(references.len() != 2) {
                        return Err(invalid_data(
                            "merkle update cell must contain exactly two references",
                        ));
                    }

                    (CellType::MerkleUpdate, self.children_mask.virtualize(1))
                }
                // 8 bits type, hash
                CellType::LIBRARY_REFERENCE => {
                    const EXPECTED_BIT_LEN: usize = 8 + HASH_BITS;
                    if unlikely(bit_len != EXPECTED_BIT_LEN) {
                        return Err(invalid_data("library reference cell bit length mismatch"));
                    } else if unlikely(!references.is_empty()) {
                        return Err(invalid_data("library reference cell contains references"));
                    }

                    (CellType::LibraryReference, LevelMask::EMPTY)
                }
                _ => return Err(invalid_data("unknown cell type")),
            }
        } else {
            (CellType::Ordinary, self.children_mask)
        };

        if unlikely(computed_level_mask != level_mask) {
            return Err(invalid_data("level mask mismatch"));
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

            descriptor.d1 &= !(Descriptor::LEVEL_MASK | Descriptor::STORE_HASHES_MASK);
            descriptor.d1 |= u8::from(level_mask) << 5;
            hasher.update([descriptor.d1, descriptor.d2]);

            if level == 0 {
                hasher.update(self.data);
            } else {
                let prev_hash = unsafe { hashes.get_unchecked(level - 1) };
                hasher.update(prev_hash.0.as_slice());
            }

            let mut depth = 0;
            for child in references {
                let child_depth = child.depth(level as u8 + level_offset);

                // TODO: check depth overflow
                depth = std::cmp::max(depth, child_depth + 1);

                hasher.update(child_depth.to_be_bytes());
            }

            for child in references {
                let child_hash = child.hash(level as u8 + level_offset);
                hasher.update(child_hash.as_slice());
            }

            let hash = hasher.finalize().into();
            hashes.push((hash, depth));
        }

        Ok(hashes)
    }
}
