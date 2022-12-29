use std::borrow::Borrow;
use std::collections::HashSet;
use std::hash::{BuildHasher, Hash};

use crate::cell::{CellHash, RcUsageTree};

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

impl MerkleFilter for RcUsageTree {
    fn contains(&self, cell: &CellHash) -> bool {
        RcUsageTree::contains(self, cell)
    }
}

impl<S: BuildHasher> MerkleFilter for HashSet<CellHash, S> {
    fn contains(&self, cell: &CellHash) -> bool {
        HashSet::contains(self, cell)
    }
}

impl<S: BuildHasher> MerkleFilter for HashSet<&CellHash, S> {
    fn contains(&self, cell: &CellHash) -> bool {
        HashSet::contains(self, cell)
    }
}
