use crate::cell::CellHash;

pub use self::proof::{MerkleProof, MerkleProofBuilder};
pub use self::pruned_branch::make_pruned_branch;
pub use self::update::MerkleUpdate;

mod proof;
mod pruned_branch;
mod update;

pub trait MerkleFilter {
    fn contains(&self, cell: &CellHash) -> bool;
}

impl<T: MerkleFilter + ?Sized> MerkleFilter for &T {
    #[inline]
    fn contains(&self, cell: &CellHash) -> bool {
        <T as MerkleFilter>::contains(self, cell)
    }
}
