use std::collections::{HashMap, HashSet};
use std::hash::BuildHasher;

use super::{make_pruned_branch, FilterAction, MerkleFilter, MerkleProofBuilder};
use crate::cell::*;

/// Parsed Merkle update representation.
///
/// NOTE: Serialized into `MerkleUpdate` cell.
pub struct MerkleUpdate<C: CellFamily> {
    /// Representation hash of the original cell.
    pub old_hash: CellHash,
    /// Representation hash of the updated cell.
    pub new_hash: CellHash,
    /// Representation depth of the original cell.
    pub old_depth: u16,
    /// Representation depth of the updated cell.
    pub new_depth: u16,
    /// Partially pruned tree with unchanged cells of the origin cell.
    pub old: CellContainer<C>,
    /// Partially pruned tree with all cells that are not in the original cell.
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
            old_hash: *EMPTY_CELL_HASH,
            new_hash: *EMPTY_CELL_HASH,
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
    fn store_into(&self, b: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
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
    /// The number of data bits that the Merkle update occupies.
    pub const BITS: u16 = 8 + (256 + 16) * 2;
    /// The number of references that the Merkle update occupies.
    pub const REFS: u8 = 2;

    /// Starts building a Merkle update between the specified cells,
    /// using old cells determined by filter.
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

    /// Tries to apply this Merkle update to the specified cell,
    /// producing a new cell and using the specified finalizer.
    pub fn apply_ext(
        &self,
        old: &CellContainer<C>,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Option<CellContainer<C>> {
        if old.as_ref().repr_hash() != &self.old_hash {
            return None;
        }

        if self.old_hash == self.new_hash {
            return Some(old.clone());
        }

        struct Applier<'a, C: CellFamily> {
            old_cells: ahash::HashMap<CellHash, CellContainer<C>>,
            new_cells: ahash::HashMap<CellHash, CellContainer<C>>,
            finalizer: &'a mut dyn Finalizer<C>,
        }

        impl<C: CellFamily> Applier<'_, C> {
            fn run(&mut self, cell: &dyn Cell<C>, merkle_depth: u8) -> Option<CellContainer<C>> {
                let descriptor = cell.descriptor();
                let merkle_offset = descriptor.cell_type().is_merkle() as u8;
                let child_merkle_depth = merkle_depth + merkle_offset;

                // Start building a new cell
                let mut result = CellBuilder::<C>::new();
                result.set_exotic(descriptor.is_exotic());

                // Build all child cells
                let mut children_mask = LevelMask::EMPTY;
                for child in cell.references().cloned() {
                    let child_descriptor = child.as_ref().descriptor();

                    let child = if child_descriptor.is_pruned_branch() {
                        // Replace pruned branches with old cells
                        let mask = child_descriptor.level_mask();
                        if mask.to_byte() & (1 << child_merkle_depth) != 0 {
                            // Use original hash for pruned branches
                            let child_hash = child.as_ref().hash(mask.level() - 1);
                            self.old_cells.get(child_hash)?.clone()
                        } else {
                            child
                        }
                    } else {
                        // Build a child cell if it hasn't been built before
                        let child_hash = child.as_ref().hash(child_merkle_depth);
                        if let Some(child) = self.new_cells.get(child_hash) {
                            child.clone()
                        } else {
                            let child = self.run(child.as_ref(), child_merkle_depth)?;
                            self.new_cells.insert(*child_hash, child.clone());
                            child
                        }
                    };

                    children_mask |= child.as_ref().level_mask();
                    result.store_reference(child);
                }

                result.set_level_mask(children_mask.virtualize(merkle_offset));
                result.store_cell_data(cell);

                result.build_ext(self.finalizer)
            }
        }

        // Collect old cells
        let old_cells = {
            // Collect and check old cells tree
            let old_cell_hashes = self.find_old_cells()?;

            let mut visited = ahash::HashSet::default();
            let mut stack = Vec::new();
            let mut old_cells = ahash::HashMap::default();

            stack.push((old.clone(), 0));
            while let Some((cell, mut merkle_depth)) = stack.pop() {
                if !visited.insert(*cell.as_ref().repr_hash()) {
                    continue;
                }

                let hash = cell.as_ref().hash(merkle_depth);
                if old_cell_hashes.contains(hash) {
                    merkle_depth += cell.as_ref().descriptor().is_merkle() as u8;
                    for child in cell.as_ref().references().cloned() {
                        stack.push((child, merkle_depth));
                    }
                    old_cells.insert(*hash, cell);
                }
            }

            old_cells
        };

        // Apply changed cells
        let new = Applier {
            old_cells,
            new_cells: Default::default(),
            finalizer,
        }
        .run(self.new.as_ref(), 0)?;

        if new.as_ref().repr_hash() == &self.new_hash {
            Some(new)
        } else {
            None
        }
    }

    fn find_old_cells(&self) -> Option<ahash::HashSet<&CellHash>> {
        let mut visited = ahash::HashSet::default();
        let mut old_cells = ahash::HashSet::default();

        // Traverse old cells
        let mut stack = vec![(self.old.as_ref(), 0)];
        while let Some((cell, mut merkle_depth)) = stack.pop() {
            // Skip visited cells
            if !visited.insert(cell.repr_hash()) {
                continue;
            }

            // Store cell with original merkle depth
            old_cells.insert(cell.hash(merkle_depth));

            // Skip children for pruned branches
            let descriptor = cell.descriptor();
            if descriptor.is_pruned_branch() {
                continue;
            }

            // Traverse children as virtualized cells
            merkle_depth += descriptor.is_merkle() as u8;
            for child in cell.references() {
                stack.push((child, merkle_depth));
            }
        }

        // Reset temp state
        visited.clear();
        stack.clear();

        // Traverse new cells
        stack.push((self.new.as_ref(), 0));
        while let Some((cell, mut merkle_depth)) = stack.pop() {
            // Skip visited cells
            if !visited.insert(cell.repr_hash()) {
                continue;
            }

            // Unchanged cells (as pruned branches) must be presented in the old tree
            let descriptor = cell.descriptor();
            if descriptor.is_pruned_branch() {
                if descriptor.level_mask().level() == merkle_depth + 1
                    && !old_cells.contains(cell.hash(merkle_depth))
                {
                    return None;
                }
            } else {
                // Traverse children as virtualized cells
                merkle_depth += descriptor.is_merkle() as u8;
                for child in cell.references() {
                    stack.push((child, merkle_depth));
                }
            }
        }

        // Done
        Some(old_cells)
    }
}

impl<C: DefaultFinalizer> MerkleUpdate<C> {
    /// Tries to apply this Merkle update to the specified cell,
    /// producing a new cell and using the default finalizer.
    pub fn apply(&self, old: &CellContainer<C>) -> Option<CellContainer<C>> {
        self.apply_ext(old, &mut C::default_finalizer())
    }
}

/// Helper struct to build a Merkle update.
pub struct MerkleUpdateBuilder<'a, C: CellFamily, F> {
    old: &'a dyn Cell<C>,
    new: &'a dyn Cell<C>,
    filter: F,
}

impl<'a, C: CellFamily, F> MerkleUpdateBuilder<'a, C, F>
where
    F: MerkleFilter,
{
    /// Creates a new Merkle update between the specified cells,
    /// using old cells determined by filter.
    pub fn new(old: &'a dyn Cell<C>, new: &'a dyn Cell<C>, f: F) -> Self {
        Self {
            old,
            new,
            filter: f,
        }
    }

    /// Builds a Merkle update using the specified finalizer.
    pub fn build_ext(self, finalizer: &mut dyn Finalizer<C>) -> Option<MerkleUpdate<C>> {
        BuilderImpl {
            old: self.old,
            new: self.new,
            filter: &self.filter,
            finalizer,
        }
        .build()
    }
}

impl<'a, C: DefaultFinalizer, F> MerkleUpdateBuilder<'a, C, F>
where
    F: MerkleFilter,
{
    /// Builds a Merkle update using the default finalizer.
    pub fn build(self) -> Option<MerkleUpdate<C>> {
        self.build_ext(&mut C::default_finalizer())
    }
}

struct BuilderImpl<'a, 'b, C: CellFamily> {
    old: &'a dyn Cell<C>,
    new: &'a dyn Cell<C>,
    filter: &'b dyn MerkleFilter,
    finalizer: &'b mut dyn Finalizer<C>,
}

impl<'a: 'b, 'b, C: CellFamily> BuilderImpl<'a, 'b, C> {
    fn build(self) -> Option<MerkleUpdate<C>> {
        struct Resolver<'a, S> {
            pruned_branches: HashMap<&'a CellHash, bool, S>,
            visited: HashSet<&'a CellHash, S>,
            filter: &'a dyn MerkleFilter,
            changed_cells: HashSet<&'a CellHash, S>,
        }

        impl<'a, S> Resolver<'a, S>
        where
            S: BuildHasher,
        {
            fn fill<C: CellFamily>(
                &mut self,
                cell: &'a dyn Cell<C>,
                mut skip_filter: bool,
            ) -> bool {
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

                let process_children = if skip_filter {
                    true
                } else {
                    match self.filter.check(repr_hash) {
                        FilterAction::Skip => false,
                        FilterAction::Include => true,
                        FilterAction::IncludeSubtree => {
                            skip_filter = true;
                            true
                        }
                    }
                };

                let mut result = false;
                if process_children {
                    for child in cell.references() {
                        result |= self.fill(child, skip_filter);
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
            fn check(&self, cell: &CellHash) -> FilterAction {
                if self.0.check(cell) == FilterAction::Skip {
                    // TODO: check if FilterAction::IncludeSubtree is correct,
                    // because it is more optimal to just include the new subtree
                    FilterAction::Include
                } else {
                    FilterAction::Skip
                }
            }
        }

        let old_hash = self.old.repr_hash();
        let old_depth = self.old.repr_depth();
        let new_hash = self.new.repr_hash();
        let new_depth = self.new.repr_depth();

        // Handle the simplest case with empty Merkle update
        if old_hash == new_hash {
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

        // Create Merkle proof cell which contains only new cells
        let (new, pruned_branches) =
            MerkleProofBuilder::<C, _>::new(self.new, InvertedFilter(self.filter))
                .track_pruned_branches()
                .build_raw_ext(self.finalizer)?;

        // Prepare cell diff resolver
        let mut resolver = Resolver {
            pruned_branches,
            visited: Default::default(),
            filter: self.filter,
            changed_cells: Default::default(),
        };

        // Find all changed cells in the old cell tree
        if resolver.fill(self.old, false) {
            resolver.changed_cells.insert(old_hash);
        }

        // Create Merkle proof cell which contains only changed cells
        let old = MerkleProofBuilder::<C, _>::new(self.old, resolver.changed_cells)
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
    use crate::{RcCell, RcCellBuilder, RcCellFamily, RcDict};

    use super::*;

    #[test]
    fn correct_store_load() {
        let default = MerkleUpdate::<RcCellFamily>::default();

        let mut builder = RcCellBuilder::new();
        assert!(default.store_into(&mut builder, &mut RcCellFamily::default_finalizer()));
        let cell = builder.build().unwrap();

        let parsed = MerkleUpdate::load_from(&mut cell.as_slice()).unwrap();
        assert_eq!(default, parsed);
    }

    #[test]
    fn dict_merkle_update() {
        fn build_u32(key: u32) -> RcCell {
            let mut builder = RcCellBuilder::new();
            builder.store_u32(key);
            builder.build().unwrap()
        }

        fn serialize_dict(dict: RcDict<32>) -> RcCell {
            let mut builder = RcCellBuilder::new();
            dict.store_into(&mut builder, &mut RcCellFamily::default_finalizer());
            builder.build().unwrap()
        }

        fn visit_all_cells(cell: &RcCell) -> ahash::HashSet<&CellHash> {
            let mut result = ahash::HashSet::default();

            let mut stack = vec![cell.as_ref()];
            while let Some(cell) = stack.pop() {
                let repr_hash = cell.repr_hash();
                if !result.insert(repr_hash) {
                    continue;
                }

                for child in cell.references() {
                    stack.push(child);
                }
            }

            result
        }

        // Create dict with keys 0..10
        let mut dict = RcDict::<32>::new();

        for i in 0..10 {
            let key = build_u32(i);
            let value = build_u32(i * 10);
            dict.add(key.as_slice(), value.as_slice()).unwrap();
        }

        // Serialize old dict
        let old_dict_cell = serialize_dict(dict.clone());
        let old_dict_hashes = visit_all_cells(&old_dict_cell);

        // Serialize new dict
        dict.set(build_u32(0).as_slice(), build_u32(1).as_slice())
            .unwrap();
        let new_dict_cell = serialize_dict(dict);

        assert_ne!(old_dict_cell.as_ref(), new_dict_cell.as_ref());

        // Create merkle update
        let merkle_update = MerkleUpdate::create(
            old_dict_cell.as_ref(),
            new_dict_cell.as_ref(),
            old_dict_hashes,
        )
        .build()
        .unwrap();

        {
            // Test serialization
            let mut builder = RcCellBuilder::new();
            assert!(merkle_update.store_into(&mut builder, &mut RcCellFamily::default_finalizer()));
            builder.build().unwrap();
        }

        let after_apply = merkle_update.apply(&old_dict_cell).unwrap();
        assert_eq!(after_apply.as_ref(), new_dict_cell.as_ref());
    }
}
