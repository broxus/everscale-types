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
/// in the Merkle proof or update.
pub trait MerkleFilter {
    /// Returns how the cell should be included in the Merkle proof or update.
    fn check(&self, cell: &CellHash) -> FilterAction;
}

/// Merkle filter action.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum FilterAction {
    /// Skip this cell and its subtree.
    Skip,
    /// Include this cell and continue checking its subtree.
    Include,
    /// Include this cell and its subtree.
    IncludeSubtree,
}

impl<T: MerkleFilter + ?Sized> MerkleFilter for &T {
    #[inline]
    fn check(&self, cell: &CellHash) -> FilterAction {
        <T as MerkleFilter>::check(self, cell)
    }
}

impl MerkleFilter for RcUsageTree {
    fn check(&self, cell: &CellHash) -> FilterAction {
        if RcUsageTree::contains(self, cell) {
            FilterAction::Include
        } else {
            FilterAction::Skip
        }
    }
}

impl<S: BuildHasher> MerkleFilter for HashSet<CellHash, S> {
    fn check(&self, cell: &CellHash) -> FilterAction {
        if HashSet::contains(self, cell) {
            FilterAction::Include
        } else {
            FilterAction::Skip
        }
    }
}

impl<S: BuildHasher> MerkleFilter for HashSet<&CellHash, S> {
    fn check(&self, cell: &CellHash) -> FilterAction {
        if HashSet::contains(self, cell) {
            FilterAction::Include
        } else {
            FilterAction::Skip
        }
    }
}
