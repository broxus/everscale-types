//! Merkle stuff.

use std::collections::HashSet;
use std::hash::BuildHasher;

use crate::cell::{CellHash, RcUsageTree};

pub use self::proof::{MerkleProof, MerkleProofBuilder, MerkleProofExtBuilder};
pub use self::pruned_branch::make_pruned_branch;
pub use self::update::{MerkleUpdate, MerkleUpdateBuilder};

mod proof;
mod pruned_branch;
mod update;

/// A cell tree filter that controls which cells will be included
/// in the merkle proof or update.
pub trait MerkleFilter {
    /// Returns `true` if the cell should be included in the merkle proof or update.
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
