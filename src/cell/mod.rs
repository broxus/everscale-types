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
