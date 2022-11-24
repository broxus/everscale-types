use std::sync::Arc;

use self::level_mask::LevelMask;

pub mod arc_cell;
pub mod descriptor;
pub mod level_mask;

/// Represents valid cell interface
pub trait Cell {
    fn cell_type(&self) -> CellType;

    fn level_mask(&self) -> LevelMask;

    fn data(&self) -> &[u8];

    fn bit_len(&self) -> u16;

    fn reference_count(&self) -> usize;

    fn reference(&self, index: u8) -> Option<&dyn Cell>;

    fn reference_cloned(&self, index: u8) -> Option<ArcCell>;

    fn hash(&self, index: u8) -> CellHash;

    fn depth(&self, index: u8) -> u16;

    fn tree_bit_count(&self) -> u64;

    fn tree_cell_count(&self) -> u64;
}

impl dyn Cell + '_ {
    pub fn repr_hash(&self) -> [u8; 32] {
        self.hash(LevelMask::MAX_LEVEL)
    }

    pub fn display_root(&'_ self) -> DisplayCellRoot<'_> {
        DisplayCellRoot(self)
    }

    pub fn display_tree(&'_ self) -> DisplayCellTree<'_> {
        DisplayCellTree(self)
    }
}

pub type ArcCell = Arc<dyn Cell>;

pub type CellHash = [u8; 32];

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum CellType {
    Ordinary,
    PrunedBranch,
    LibraryReference,
    MerkleProof,
    MerkleUpdate,
}

impl CellType {
    pub const ORDINARY: u8 = 0xff;
    pub const PRUNED_BRANCH: u8 = 1;
    pub const LIBRARY_REFERENCE: u8 = 2;
    pub const MERKLE_PROOF: u8 = 3;
    pub const MERKLE_UPDATE: u8 = 4;

    #[inline]
    pub const fn is_merkle(&self) -> bool {
        matches!(self, Self::MerkleProof | Self::MerkleUpdate)
    }
}

impl From<CellType> for u8 {
    fn from(cell_type: CellType) -> u8 {
        match cell_type {
            CellType::Ordinary => CellType::ORDINARY,
            CellType::PrunedBranch => CellType::PRUNED_BRANCH,
            CellType::LibraryReference => CellType::LIBRARY_REFERENCE,
            CellType::MerkleProof => CellType::MERKLE_PROOF,
            CellType::MerkleUpdate => CellType::MERKLE_UPDATE,
        }
    }
}

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
            f.write_fmt(format_args!(
                "{data}\nbits: {:>4}, refs: {}, hash: {}",
                self.0.bit_len(),
                self.0.reference_count(),
                hex::encode(repr_hash),
            ))
        }
    }
}

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
