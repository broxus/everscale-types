use std::rc::Rc;
use std::sync::Arc;

use self::level_mask::*;

mod generic_cell;
pub mod level_mask;

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum CellType {
    Ordinary,
    PrunedBranch,
    LibraryReference,
    MerkleProof,
    MerkleUpdate,
}

impl From<CellType> for u8 {
    fn from(cell_type: CellType) -> u8 {
        match cell_type {
            CellType::Ordinary => 0xff,
            CellType::PrunedBranch => 1,
            CellType::LibraryReference => 2,
            CellType::MerkleProof => 3,
            CellType::MerkleUpdate => 4,
        }
    }
}

pub trait Cell {
    fn cell_type(&self) -> CellType;

    fn level_mask(&self) -> LevelMask;

    fn data(&self) -> &[u8];

    fn bit_len(&self) -> u16;

    fn reference_count(&self) -> usize;

    fn reference(&self, index: u8) -> Option<&dyn Cell>;

    fn tree_bit_count(&self) -> u64;

    fn tree_cell_count(&self) -> u64;
}

pub type ArcCell = Arc<dyn Cell>;
pub type RcCell = Rc<dyn Cell>;
