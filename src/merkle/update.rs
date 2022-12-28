use std::collections::{HashMap, HashSet};
use std::hash::BuildHasher;

use super::{make_pruned_branch, MerkleFilter, MerkleProofBuilder};
use crate::cell::*;

pub struct MerkleUpdate<C: CellFamily> {
    pub old_hash: CellHash,
    pub new_hash: CellHash,
    pub old_depth: u16,
    pub new_depth: u16,
    pub old: CellContainer<C>,
    pub new: CellContainer<C>,
}

impl<C: CellFamily> std::fmt::Debug for MerkleUpdate<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MerkleUpdate")
            .field("old_hash", &self.old_hash)
            .field("new_hash", &self.new_hash)
            .field("old_depth", &self.old_depth)
            .field("new_depth", &self.new_depth)
            .field("old", &self.old.as_ref().debug_root())
            .field("new", &self.new.as_ref().debug_root())
            .finish()
    }
}

impl<C: CellFamily> Eq for MerkleUpdate<C> {}
impl<C: CellFamily> PartialEq for MerkleUpdate<C> {
    fn eq(&self, other: &Self) -> bool {
        self.old_hash == other.old_hash
            && self.new_hash == other.new_hash
            && self.old_depth == other.old_depth
            && self.new_depth == other.new_depth
            && self.old.as_ref() == other.old.as_ref()
            && self.new.as_ref() == other.new.as_ref()
    }
}

impl<C: CellFamily> Default for MerkleUpdate<C> {
    fn default() -> Self {
        let empty_cell = C::empty_cell();
        Self {
            old_hash: EMPTY_CELL_HASH,
            new_hash: EMPTY_CELL_HASH,
            old_depth: 0,
            new_depth: 0,
            old: empty_cell.clone(),
            new: empty_cell,
        }
    }
}

impl<C: CellFamily> Load<'_, C> for MerkleUpdate<C> {
    fn load_from(s: &mut CellSlice<C>) -> Option<Self> {
        if !s.has_remaining(Self::BITS, Self::REFS) {
            return None;
        }

        if s.get_u8(0)? != CellType::MerkleUpdate.to_byte() {
            return None;
        }

        let res = Self {
            old_hash: s.get_u256(8)?,
            new_hash: s.get_u256(8 + 256)?,
            old_depth: s.get_u16(8 + 256 * 2)?,
            new_depth: s.get_u16(8 + 256 * 2 + 16)?,
            old: s.get_reference_cloned(0)?,
            new: s.get_reference_cloned(1)?,
        };
        if res.old.as_ref().hash(0) == &res.old_hash
            && res.old.as_ref().depth(0) == res.old_depth
            && res.new.as_ref().hash(0) == &res.new_hash
            && res.new.as_ref().depth(0) == res.new_depth
            && s.try_advance(Self::BITS, Self::REFS)
        {
            Some(res)
        } else {
            None
        }
    }
}

impl<C: CellFamily> Store<C> for MerkleUpdate<C> {
    fn store_into(&self, b: &mut CellBuilder<C>) -> bool {
        if !b.has_capacity(Self::BITS, Self::REFS) {
            return false;
        }
        let old_level_mask = self.old.as_ref().level_mask();
        let new_level_mask = self.new.as_ref().level_mask();
        b.set_level_mask((old_level_mask | new_level_mask).virtualize(1));
        b.set_exotic(true);
        b.store_u8(CellType::MerkleUpdate.to_byte())
            && b.store_u256(&self.old_hash)
            && b.store_u256(&self.new_hash)
            && b.store_u16(self.old_depth)
            && b.store_u16(self.new_depth)
            && b.store_reference(self.old.clone())
            && b.store_reference(self.new.clone())
    }
}

impl<C: CellFamily> MerkleUpdate<C> {
    pub const BITS: u16 = 8 + (256 + 16) * 2;
    pub const REFS: u8 = 2;

    pub fn create<'a, F>(
        old: &'a dyn Cell<C>,
        new: &'a dyn Cell<C>,
        f: F,
    ) -> MerkleUpdateBuilder<'a, C, F>
    where
        F: MerkleFilter + 'a,
    {
        MerkleUpdateBuilder::new(old, new, f)
    }
}

pub struct MerkleUpdateBuilder<'a, C: CellFamily, F, S = ahash::RandomState> {
    old: &'a dyn Cell<C>,
    new: &'a dyn Cell<C>,
    filter: F,
    _marker: std::marker::PhantomData<S>,
}

impl<'a, C: CellFamily, S, F> MerkleUpdateBuilder<'a, C, F, S>
where
    F: MerkleFilter,
    S: BuildHasher + Default,
{
    pub fn new(old: &'a dyn Cell<C>, new: &'a dyn Cell<C>, f: F) -> Self {
        Self {
            old,
            new,
            filter: f,
            _marker: std::marker::PhantomData::<S>,
        }
    }

    pub fn build_ext(self, finalizer: &mut dyn Finalizer<C>) -> Option<MerkleUpdate<C>> {
        BuilderImpl {
            old: self.old,
            new: self.new,
            filter: &self.filter,
            finalizer,
            _marker: std::marker::PhantomData::<S>,
        }
        .build()
    }
}

impl<'a, C: DefaultFinalizer, F, S> MerkleUpdateBuilder<'a, C, F, S>
where
    F: MerkleFilter,
    S: BuildHasher + Default,
{
    pub fn build(self) -> Option<MerkleUpdate<C>> {
        self.build_ext(&mut C::default_finalizer())
    }
}

struct BuilderImpl<'a, 'b, C: CellFamily, S> {
    old: &'a dyn Cell<C>,
    new: &'a dyn Cell<C>,
    filter: &'b dyn MerkleFilter,
    finalizer: &'b mut dyn Finalizer<C>,
    _marker: std::marker::PhantomData<S>,
}

impl<'a: 'b, 'b, C: CellFamily, S> BuilderImpl<'a, 'b, C, S>
where
    S: BuildHasher + Default,
{
    fn build(self) -> Option<MerkleUpdate<C>> {
        struct Resolver<'a, S> {
            pruned_branches: HashMap<CellHash, bool, S>,
            visited: HashSet<&'a CellHash, S>,
            filter: &'a dyn MerkleFilter,
            changed_cells: HashSet<&'a CellHash, S>,
        }

        impl<'a, S> Resolver<'a, S>
        where
            S: BuildHasher,
        {
            fn fill<C: CellFamily>(&mut self, cell: &'a dyn Cell<C>) -> bool {
                let repr_hash = cell.repr_hash();

                // Skip visited cells
                if self.visited.contains(repr_hash) {
                    return false;
                }
                self.visited.insert(repr_hash);

                let is_pruned = match self.pruned_branches.get_mut(repr_hash) {
                    Some(true) => return false,
                    Some(visited) => {
                        *visited = true;
                        true
                    }
                    None => false,
                };

                let mut result = false;
                if self.filter.contains(repr_hash) {
                    for child in cell.references() {
                        result |= self.fill(child);
                    }

                    if result {
                        self.changed_cells.insert(repr_hash);
                    }
                }

                result | is_pruned
            }
        }

        struct InvertedFilter<F>(F);

        impl<F: MerkleFilter> MerkleFilter for InvertedFilter<F> {
            #[inline]
            fn contains(&self, cell: &CellHash) -> bool {
                !self.0.contains(cell)
            }
        }

        #[derive(Clone, Copy)]
        struct ChangedCellsFilter<'a, S>(&'a HashSet<&'a CellHash, S>);

        impl<S: BuildHasher> MerkleFilter for ChangedCellsFilter<'_, S> {
            fn contains(&self, cell: &CellHash) -> bool {
                self.0.contains(cell)
            }
        }

        let old_hash = self.old.repr_hash();
        let old_depth = self.old.repr_depth();
        let new_hash = self.new.repr_hash();
        let new_depth = self.new.repr_depth();

        // Handle the simplest case with empty merkle update
        if old_hash != new_hash {
            let pruned = make_pruned_branch(self.old, 0, self.finalizer)?;
            return Some(MerkleUpdate {
                old_hash: *old_hash,
                new_hash: *old_hash,
                old_depth,
                new_depth: old_depth,
                old: pruned.clone(),
                new: pruned,
            });
        }

        // Prepare cell diff resolver
        let mut resolver = Resolver::<S> {
            pruned_branches: Default::default(),
            visited: Default::default(),
            filter: self.filter,
            changed_cells: Default::default(),
        };

        // Create merkle proof cell which contains only new cells
        let new = MerkleProofBuilder::<C, _, S>::new(self.new, InvertedFilter(self.filter))
            .track_pruned_branches(&mut resolver.pruned_branches)
            .build_raw_ext(self.finalizer)?;

        // Find all changed cells in the old cell tree
        if resolver.fill(self.old) {
            resolver.changed_cells.insert(old_hash);
        }

        // Create merkle proof cell which contains only changed cells
        let old = MerkleProofBuilder::<C, _, S>::new(
            self.old,
            ChangedCellsFilter(&resolver.changed_cells),
        )
        .build_raw_ext(self.finalizer)?;

        // Done
        Some(MerkleUpdate {
            old_hash: *old_hash,
            new_hash: *new_hash,
            old_depth,
            new_depth,
            old,
            new,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::{RcCellBuilder, RcCellFamily};

    use super::*;

    #[test]
    fn correct_store_load() {
        let default = MerkleUpdate::<RcCellFamily>::default();

        let mut builder = RcCellBuilder::new();
        assert!(default.store_into(&mut builder));
        let cell = builder.build().unwrap();

        let parsed = MerkleUpdate::load_from(&mut cell.as_slice()).unwrap();
        assert_eq!(default, parsed);
    }
}
