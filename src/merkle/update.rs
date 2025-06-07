use std::collections::HashSet;
use std::hash::BuildHasher;

use dashmap::{DashMap, DashSet};

use super::{make_pruned_branch, FilterAction, MerkleFilter, MerkleProofBuilder};
use crate::cell::*;
use crate::error::Error;
use crate::util::unlikely;

/// Parsed Merkle update representation.
///
/// NOTE: Serialized into `MerkleUpdate` cell.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MerkleUpdate {
    /// Representation hash of the original cell.
    pub old_hash: HashBytes,
    /// Representation hash of the updated cell.
    pub new_hash: HashBytes,
    /// Representation depth of the original cell.
    pub old_depth: u16,
    /// Representation depth of the updated cell.
    pub new_depth: u16,
    /// Partially pruned tree with unchanged cells of the origin cell.
    #[cfg_attr(feature = "serde", serde(with = "crate::boc::Boc"))]
    pub old: Cell,
    /// Partially pruned tree with all cells that are not in the original cell.
    #[cfg_attr(feature = "serde", serde(with = "crate::boc::Boc"))]
    pub new: Cell,
}

impl Eq for MerkleUpdate {}
impl PartialEq for MerkleUpdate {
    fn eq(&self, other: &Self) -> bool {
        self.old_hash == other.old_hash
            && self.new_hash == other.new_hash
            && self.old_depth == other.old_depth
            && self.new_depth == other.new_depth
            && self.old.as_ref() == other.old.as_ref()
            && self.new.as_ref() == other.new.as_ref()
    }
}

impl Default for MerkleUpdate {
    fn default() -> Self {
        let empty_cell = Cell::empty_cell();
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

impl<'a> LoadCell<'a> for MerkleUpdate {
    fn load_from_cell(cell: &'a DynCell) -> Result<Self, Error> {
        if unlikely(!cell.is_exotic()) {
            return Err(Error::UnexpectedOrdinaryCell);
        }

        let mut s = cell.as_slice_allow_exotic();
        if s.size_bits() != Self::BITS || s.size_refs() != Self::REFS {
            return Err(Error::CellUnderflow);
        }

        if ok!(s.load_u8()) != CellType::MerkleUpdate.to_byte() {
            return Err(Error::InvalidCell);
        }

        let res = Self {
            old_hash: ok!(s.load_u256()),
            new_hash: ok!(s.load_u256()),
            old_depth: ok!(s.load_u16()),
            new_depth: ok!(s.load_u16()),
            old: ok!(s.load_reference_cloned()),
            new: ok!(s.load_reference_cloned()),
        };
        debug_assert!(s.is_data_empty() && s.is_refs_empty());

        if res.old.as_ref().hash(0) == &res.old_hash
            && res.old.as_ref().depth(0) == res.old_depth
            && res.new.as_ref().hash(0) == &res.new_hash
            && res.new.as_ref().depth(0) == res.new_depth
        {
            Ok(res)
        } else {
            Err(Error::InvalidCell)
        }
    }
}

impl Store for MerkleUpdate {
    fn store_into(&self, b: &mut CellBuilder, _: &dyn CellContext) -> Result<(), Error> {
        if !b.has_capacity(Self::BITS, Self::REFS) {
            return Err(Error::CellOverflow);
        }

        b.set_exotic(true);
        ok!(b.store_u8(CellType::MerkleUpdate.to_byte()));
        ok!(b.store_u256(&self.old_hash));
        ok!(b.store_u256(&self.new_hash));
        ok!(b.store_u32(((self.old_depth as u32) << 16) | self.new_depth as u32));
        ok!(b.store_reference(self.old.clone()));
        b.store_reference(self.new.clone())
    }
}

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for MerkleUpdate {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let old = Cell::arbitrary(u).and_then(crate::arbitrary::check_max_depth)?;
        let new = Cell::arbitrary(u).and_then(crate::arbitrary::check_max_depth)?;
        Ok(Self {
            old_hash: *old.hash(0),
            new_hash: *new.hash(0),
            old_depth: old.depth(0),
            new_depth: new.depth(0),
            old,
            new,
        })
    }

    fn size_hint(_: usize) -> (usize, Option<usize>) {
        (4, None)
    }
}

impl MerkleUpdate {
    /// The number of data bits that the Merkle update occupies.
    pub const BITS: u16 = 8 + (256 + 16) * 2;
    /// The number of references that the Merkle update occupies.
    pub const REFS: u8 = 2;

    /// Starts building a Merkle update between the specified cells,
    /// using old cells determined by filter.
    pub fn create<'a, F>(old: &'a DynCell, new: &'a DynCell, f: F) -> MerkleUpdateBuilder<'a, F>
    where
        F: MerkleFilter + Send + Sync + 'a,
    {
        MerkleUpdateBuilder::new(old, new, f)
    }

    /// Tries to apply this Merkle update to the specified cell,
    /// producing a new cell and using an empty cell context.
    pub fn apply(&self, old: &Cell) -> Result<Cell, Error> {
        self.apply_ext(old, Cell::empty_context())
    }

    /// Tries to apply this Merkle update to the specified cell,
    /// producing a new cell and using an empty cell context.
    pub fn apply_ext(&self, old: &Cell, context: &dyn CellContext) -> Result<Cell, Error> {
        if old.as_ref().repr_hash() != &self.old_hash {
            return Err(Error::InvalidData);
        }

        if self.old_hash == self.new_hash {
            return Ok(old.clone());
        }

        struct Applier<'a> {
            old_cells: ahash::HashMap<HashBytes, Cell>,
            new_cells: ahash::HashMap<HashBytes, Cell>,
            context: &'a dyn CellContext,
        }

        impl Applier<'_> {
            fn run(&mut self, cell: &DynCell, merkle_depth: u8) -> Result<Cell, Error> {
                let descriptor = cell.descriptor();
                let child_merkle_depth = merkle_depth + descriptor.cell_type().is_merkle() as u8;

                // Start building a new cell
                let mut result = CellBuilder::new();
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
                            match self.old_cells.get(child_hash) {
                                Some(cell) => cell.clone(),
                                None => return Err(Error::InvalidData),
                            }
                        } else {
                            child
                        }
                    } else {
                        // Build a child cell if it hasn't been built before
                        let child_hash = child.as_ref().hash(child_merkle_depth);
                        if let Some(child) = self.new_cells.get(child_hash) {
                            child.clone()
                        } else {
                            let child = ok!(self.run(child.as_ref(), child_merkle_depth));
                            self.new_cells.insert(*child_hash, child.clone());
                            child
                        }
                    };

                    children_mask |= child.as_ref().level_mask();
                    _ = result.store_reference(child);
                }

                _ = result.store_cell_data(cell);

                result.build_ext(self.context)
            }
        }

        // Collect old cells
        let old_cells = {
            // Collect and check old cells tree
            let old_cell_hashes = ok!(self.find_old_cells());

            let mut visited = ahash::HashSet::default();
            let mut old_cells = ahash::HashMap::default();

            // Insert root
            let mut merkle_depth = 0u8;

            visited.insert(old.repr_hash());
            old_cells.insert(*old.hash(merkle_depth), old.clone());
            merkle_depth += old.descriptor().is_merkle() as u8;
            let mut stack = vec![old.references()];

            'outer: while let Some(iter) = stack.last_mut() {
                let cloned = iter.clone().cloned();
                for (child_ref, child) in std::iter::zip(&mut *iter, cloned) {
                    if !visited.insert(child_ref.repr_hash()) {
                        continue;
                    }

                    let hash = child_ref.hash(merkle_depth);
                    if !old_cell_hashes.contains(hash) {
                        // Skip new cells
                        continue;
                    }

                    // Store an owned cell with original merkle depth
                    old_cells.insert(*hash, child);

                    // Increase the current merkle depth if needed
                    merkle_depth += child_ref.descriptor().is_merkle() as u8;
                    // And proceed to processing this child
                    stack.push(child_ref.references());
                    continue 'outer;
                }

                // Decrease the current merkle depth if needed
                merkle_depth -= iter.cell().descriptor().is_merkle() as u8;
                // And return to the previous depth
                stack.pop();
            }

            old_cells
        };

        // Apply changed cells
        let new = Applier {
            old_cells,
            new_cells: Default::default(),
            context,
        }
        .run(self.new.as_ref(), 0)?;

        if new.as_ref().repr_hash() == &self.new_hash {
            Ok(new)
        } else {
            Err(Error::InvalidData)
        }
    }

    /// Computes the removed cells diff using the original cell.
    pub fn compute_removed_cells<'a>(
        &self,
        old: &'a DynCell,
    ) -> Result<ahash::HashMap<&'a HashBytes, u32>, Error> {
        use std::collections::hash_map;

        if old.repr_hash() != &self.old_hash || self.old.hash(0) != old.repr_hash() {
            return Err(Error::InvalidData);
        }

        if self.old_hash == self.new_hash {
            // No cells were removed
            return Ok(Default::default());
        }

        let mut new_cells = ahash::HashSet::default();

        // Compute a list of all hashes in the `new` merkle update tree
        {
            // TODO: check if `new_cells` set can be used instead of `visited`
            let mut visited = ahash::HashSet::default();
            let mut merkle_depth = self.new.descriptor().is_merkle() as u8;
            let mut stack = vec![self.new.references()];

            visited.insert(self.new.repr_hash());
            new_cells.insert(self.new.hash(0));

            'outer: while let Some(iter) = stack.last_mut() {
                for child in &mut *iter {
                    if !visited.insert(child.repr_hash()) {
                        continue;
                    }

                    // Track new cells
                    new_cells.insert(child.hash(merkle_depth));

                    // Unchanged cells (as pruned branches) must be presented in the old tree
                    let descriptor = child.descriptor();
                    if descriptor.is_pruned_branch() {
                        continue;
                    }

                    // Increase the current merkle depth if needed
                    merkle_depth += descriptor.is_merkle() as u8;
                    // And proceed to processing this child
                    stack.push(child.references());
                    continue 'outer;
                }

                merkle_depth -= iter.cell().descriptor().is_merkle() as u8;
                stack.pop();
            }

            debug_assert_eq!(merkle_depth, 0);
        }

        // Traverse old cells
        let mut result = ahash::HashMap::default();
        result.insert(old.repr_hash(), 1);

        let mut stack = Vec::new();
        if !new_cells.contains(old.repr_hash()) {
            stack.push(old.references());
        }

        'outer: while let Some(iter) = stack.last_mut() {
            for child in &mut *iter {
                let hash = child.repr_hash();
                match result.entry(hash) {
                    hash_map::Entry::Occupied(mut entry) => {
                        *entry.get_mut() += 1;
                        continue;
                    }
                    hash_map::Entry::Vacant(entry) => {
                        entry.insert(1);
                    }
                }

                // Skip empty or used subtrees
                if child.reference_count() == 0 || new_cells.contains(hash) {
                    continue;
                }

                stack.push(child.references());
                continue 'outer;
            }
            stack.pop();
        }

        Ok(result)
    }

    fn find_old_cells(&self) -> Result<ahash::HashSet<&HashBytes>, Error> {
        let mut visited = ahash::HashSet::default();
        let mut old_cells = ahash::HashSet::default();

        // Traverse old cells
        let mut merkle_depth = 0u8;

        // Insert root
        visited.insert(self.old.repr_hash());
        old_cells.insert(self.old.hash(merkle_depth));
        merkle_depth += self.old.descriptor().is_merkle() as u8;
        let mut stack = vec![self.old.references()];

        'outer: while let Some(iter) = stack.last_mut() {
            for child in &mut *iter {
                if !visited.insert(child.repr_hash()) {
                    continue;
                }

                // Store cell with original merkle depth
                old_cells.insert(child.hash(merkle_depth));

                // Skip children for pruned branches
                let descriptor = child.descriptor();
                if descriptor.is_pruned_branch() {
                    continue;
                }

                // Increase the current merkle depth if needed
                merkle_depth += descriptor.is_merkle() as u8;
                // And proceed to processing this child
                stack.push(child.references());
                continue 'outer;
            }

            // Decrease the current merkle depth if needed
            merkle_depth -= iter.cell().descriptor().is_merkle() as u8;
            // And return to the previous depth
            stack.pop();
        }

        debug_assert_eq!(merkle_depth, 0);

        // Traverse new cells

        // Insert root
        visited.clear();
        visited.insert(self.new.repr_hash());
        stack.push(self.new.references());
        merkle_depth += self.new.descriptor().is_merkle() as u8;

        'outer: while let Some(iter) = stack.last_mut() {
            for child in &mut *iter {
                // Skip visited cells
                if !visited.insert(child.repr_hash()) {
                    continue;
                }

                // Unchanged cells (as pruned branches) must be presented in the old tree
                let descriptor = child.descriptor();
                if descriptor.is_pruned_branch() {
                    if descriptor.level_mask().level() == merkle_depth + 1
                        && !old_cells.contains(child.hash(merkle_depth))
                    {
                        return Err(Error::InvalidData);
                    }
                } else {
                    // Increase the current merkle depth if needed
                    merkle_depth += descriptor.is_merkle() as u8;
                    // And proceed to processing this child
                    stack.push(child.references());
                    continue 'outer;
                }
            }

            // Decrease the current merkle depth if needed
            merkle_depth -= iter.cell().descriptor().is_merkle() as u8;
            // And return to the previous depth
            stack.pop();
        }

        debug_assert_eq!(merkle_depth, 0);

        // Done
        Ok(old_cells)
    }
}

/// Helper struct to build a Merkle update.
pub struct MerkleUpdateBuilder<'a, F> {
    old: &'a DynCell,
    new: &'a DynCell,
    filter: F,
}

impl<'a, F> MerkleUpdateBuilder<'a, F>
where
    F: MerkleFilter + Send + Sync,
{
    /// Creates a new Merkle update between the specified cells,
    /// using old cells determined by filter.
    pub fn new(old: &'a DynCell, new: &'a DynCell, f: F) -> Self {
        Self {
            old,
            new,
            filter: f,
        }
    }

    /// Builds a Merkle update using the specified cell context.
    pub fn build_ext(
        self,
        context: &(dyn CellContext + Send + Sync),
    ) -> Result<MerkleUpdate, Error> {
        BuilderImpl {
            old: self.old,
            new: self.new,
            filter: &self.filter,
            context,
        }
        .build()
    }

    /// Multithreaded build a Merkle update using the specified cell context.
    pub fn mt_build_ext(
        self,
        context: &(dyn CellContext + Send + Sync),
        new_cells: ahash::HashSet<HashBytes>,
        old_cells: ahash::HashSet<HashBytes>,
    ) -> Result<MerkleUpdate, Error> {
        BuilderImpl {
            old: self.old,
            new: self.new,
            filter: &self.filter,
            context,
        }
        .mt_build(new_cells, old_cells)
    }
}

impl<F> MerkleUpdateBuilder<'_, F>
where
    F: MerkleFilter + Send + Sync,
{
    /// Builds a Merkle update using an empty cell context.
    pub fn build(self) -> Result<MerkleUpdate, Error> {
        self.build_ext(Cell::empty_context())
    }

    /// Multithreaded build a Merkle update using an empty cell context.
    pub fn mt_build(
        self,
        new_cells: ahash::HashSet<HashBytes>,
        old_cells: ahash::HashSet<HashBytes>,
    ) -> Result<MerkleUpdate, Error> {
        self.mt_build_ext(Cell::empty_context(), new_cells, old_cells)
    }
}

struct BuilderImpl<'a, 'b, 'c: 'a> {
    old: &'a DynCell,
    new: &'a DynCell,
    filter: &'b (dyn MerkleFilter + Send + Sync),
    context: &'c (dyn CellContext + Send + Sync),
}

impl<'a: 'b, 'b, 'c: 'a> BuilderImpl<'a, 'b, 'c> {
    fn build(self) -> Result<MerkleUpdate, Error> {
        struct Resolver<'a, S> {
            pruned_branches: DashMap<&'a HashBytes, bool, S>,
            visited: HashSet<&'a HashBytes, S>,
            filter: &'a dyn MerkleFilter,
            changed_cells: HashSet<&'a HashBytes, S>,
        }

        impl<'a, S> Resolver<'a, S>
        where
            S: BuildHasher + Clone,
        {
            fn fill(&mut self, cell: &'a DynCell, mut skip_filter: bool) -> bool {
                let repr_hash = cell.repr_hash();

                // Skip visited cells
                if self.visited.contains(repr_hash) {
                    return false;
                }
                self.visited.insert(repr_hash);

                let is_pruned = match self.pruned_branches.get_mut(repr_hash) {
                    Some(mut res) => {
                        let visited = res.value_mut();
                        if *visited {
                            false
                        } else {
                            *visited = true;
                            true
                        }
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

        impl<F: MerkleFilter + Send + Sync> MerkleFilter for InvertedFilter<F> {
            #[inline]
            fn check(&self, cell: &HashBytes) -> FilterAction {
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
            let pruned = ok!(make_pruned_branch(self.old, 0, self.context));
            return Ok(MerkleUpdate {
                old_hash: *old_hash,
                new_hash: *old_hash,
                old_depth,
                new_depth: old_depth,
                old: pruned.clone(),
                new: pruned,
            });
        }

        // Create Merkle proof cell which contains only new cells
        let (new, pruned_branches) = ok! {
            MerkleProofBuilder::<_>::new(
                self.new,
                InvertedFilter(self.filter)
            )
            .track_pruned_branches()
            .allow_different_root(true)
            .build_raw_ext(self.context)
        };

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
        let old = ok! {
            MerkleProofBuilder::<_>::new(self.old, resolver.changed_cells)
                .allow_different_root(true)
                .build_raw_ext(self.context)
        };

        // Done
        Ok(MerkleUpdate {
            old_hash: *old_hash,
            new_hash: *new_hash,
            old_depth,
            new_depth,
            old,
            new,
        })
    }

    fn mt_build(
        self,
        new_cells: ahash::HashSet<HashBytes>,
        old_cells: ahash::HashSet<HashBytes>,
    ) -> Result<MerkleUpdate, Error> {
        struct Resolver<'a, S> {
            pruned_branches: DashMap<&'a HashBytes, bool, S>,
            changed_cells: DashSet<&'a HashBytes, S>,
            visited: DashSet<&'a HashBytes, S>,
            filter: &'a dyn MerkleFilter,
        }

        impl<'a, S> Resolver<'a, S>
        where
            S: BuildHasher + Clone,
        {
            fn resolve(&self, cell: &'a DynCell, skip_filter: bool) {
                struct Node<'a> {
                    references: RefsIter<'a>,
                    skip_filter: bool,
                    has_changes: bool,
                }

                let mut stack = Vec::with_capacity(cell.repr_depth() as usize);
                stack.push(Node {
                    references: cell.references(),
                    skip_filter,
                    has_changes: false,
                });

                while let Some(last) = stack.last_mut() {
                    if let Some(child) = last.references.next() {
                        let repr_hash = child.repr_hash();

                        // Skip visited cells
                        if self.visited.contains(repr_hash) {
                            continue;
                        }
                        self.visited.insert(repr_hash);

                        let is_pruned = match self.pruned_branches.get_mut(repr_hash) {
                            Some(mut res) => {
                                let visited = res.value_mut();
                                if *visited {
                                    false
                                } else {
                                    *visited = true;
                                    true
                                }
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
                                    last.skip_filter = true;
                                    true
                                }
                            }
                        };

                        if process_children {
                            stack.push(Node {
                                references: child.references(),
                                skip_filter,
                                has_changes: false,
                            });

                            continue;
                        }

                        last.has_changes |= is_pruned;
                    } else if let Some(last) = stack.pop() {
                        if last.has_changes {
                            let cell = last.references.cell();
                            self.changed_cells.insert(cell.repr_hash());
                        }

                        if let Some(parent) = stack.last_mut() {
                            parent.has_changes |= last.has_changes;
                        }
                    }
                }
            }
        }

        struct InvertedFilter<F>(F);

        impl<F: MerkleFilter + Send + Sync> MerkleFilter for InvertedFilter<F> {
            #[inline]
            fn check(&self, cell: &HashBytes) -> FilterAction {
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
            let pruned = ok!(make_pruned_branch(self.old, 0, self.context));
            return Ok(MerkleUpdate {
                old_hash: *old_hash,
                new_hash: *old_hash,
                old_depth,
                new_depth: old_depth,
                old: pruned.clone(),
                new: pruned,
            });
        }

        // Create Merkle proof cell which contains only new cells
        let (new, pruned_branches) = ok! {
            MerkleProofBuilder::<_>::new(
                self.new,
                InvertedFilter(self.filter)
            )
            .track_pruned_branches()
            .allow_different_root(true)
            .mt_build_raw_ext(self.context, &new_cells)
        };

        // Prepare cell diff resolver
        let resolver = Resolver {
            pruned_branches,
            visited: Default::default(),
            filter: self.filter,
            changed_cells: Default::default(),
        };

        // Find all changed cells in the old cell tree
        resolver.resolve(self.old, false);

        // Create Merkle proof cell which contains only changed cells
        let old = ok! {
            MerkleProofBuilder::<_>::new(self.old, resolver.changed_cells)
                .allow_different_root(true)
                .mt_build_raw_ext(self.context, &old_cells)
        };

        // Done
        Ok(MerkleUpdate {
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
    use super::*;
    use crate::prelude::*;

    fn visit_all_cells(cell: &Cell) -> ahash::HashSet<&HashBytes> {
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

    #[test]
    fn mt_build() {
        let old = "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";
        let new = "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";

        let old_cell = Boc::decode_base64(old).unwrap();
        let new_cell = Boc::decode_base64(new).unwrap();

        let usage_tree = UsageTree::new(UsageTreeMode::OnLoad);
        let merkle_update_builder =
            MerkleUpdate::create(old_cell.as_ref(), new_cell.as_ref(), usage_tree);

        let _state_update = merkle_update_builder.build().unwrap();
    }

    #[test]
    fn correct_store_load() {
        let default = MerkleUpdate::default();

        let mut builder = CellBuilder::new();
        default
            .store_into(&mut builder, Cell::empty_context())
            .unwrap();
        let cell = builder.build().unwrap();

        let parsed = cell.parse_exotic::<MerkleUpdate>().unwrap();
        assert_eq!(default, parsed);
    }

    #[test]
    fn dict_merkle_update() {
        // Create dict with keys 0..10
        let mut dict = Dict::<u32, u32>::new();
        for i in 0..10 {
            dict.add(i, i * 10).unwrap();
        }

        // Serialize old dict
        let old_dict_cell = CellBuilder::build_from(&dict).unwrap();
        let old_dict_hashes = visit_all_cells(&old_dict_cell);

        // Serialize new dict
        dict.set(0, 1).unwrap();
        let new_dict_cell = CellBuilder::build_from(dict).unwrap();

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
            let mut builder = CellBuilder::new();
            merkle_update
                .store_into(&mut builder, Cell::empty_context())
                .unwrap();
            builder.build().unwrap();
        }

        let after_apply = merkle_update.apply(&old_dict_cell).unwrap();
        assert_eq!(after_apply.as_ref(), new_dict_cell.as_ref());
    }

    #[test]
    fn dict_merkle_update_with_usage_tree() {
        // Serialize old dict
        let old_dict_cell = {
            // Create dict with keys 0..10
            let mut dict = Dict::<u32, u32>::new();
            for i in 0..10 {
                dict.add(i, i * 10).unwrap();
            }

            CellBuilder::build_from(&dict).unwrap()
        };

        let usage_tree = UsageTree::new(UsageTreeMode::OnLoad);
        let old_dict_cell_tracked = usage_tree.track(&old_dict_cell);

        // Serialize new dict
        let new_dict_cell = {
            let mut dict = old_dict_cell_tracked.parse::<Dict<u32, u32>>().unwrap();
            dict.set(0, 1).unwrap();
            dict.set(10, 321).unwrap();
            CellBuilder::build_from(dict).unwrap()
        };

        assert_ne!(old_dict_cell.as_ref(), new_dict_cell.as_ref());

        // Create merkle update
        let merkle_update =
            MerkleUpdate::create(old_dict_cell.as_ref(), new_dict_cell.as_ref(), usage_tree)
                .build()
                .unwrap();

        // Test serialization
        let merkle_update_cell = CellBuilder::build_from(&merkle_update).unwrap();
        println!("BOC: {}", Boc::encode_base64(merkle_update_cell));

        let after_apply = merkle_update.apply(&old_dict_cell).unwrap();
        assert_eq!(after_apply.as_ref(), new_dict_cell.as_ref());
    }

    #[test]
    fn dict_removed_cells_diff() {
        // Create dict with keys 0..10
        let mut dict = Dict::<u32, u32>::new();
        for i in 0..10 {
            dict.add(i, 0).unwrap();
        }

        // Serialize old dict
        let old_dict_cell = CellBuilder::build_from(&dict).unwrap();
        let old_dict_hashes = visit_all_cells(&old_dict_cell);

        // Serialize new dict
        dict.set(0, 1).unwrap();
        let new_dict_cell = CellBuilder::build_from(dict).unwrap();

        assert_ne!(old_dict_cell.as_ref(), new_dict_cell.as_ref());

        // Create merkle update
        let merkle_update = MerkleUpdate::create(
            old_dict_cell.as_ref(),
            new_dict_cell.as_ref(),
            old_dict_hashes,
        )
        .build()
        .unwrap();

        // Test diff
        let mut refs_for_both = RefsStorage::default();
        refs_for_both.store_cell(old_dict_cell.as_ref());
        refs_for_both.store_cell(new_dict_cell.as_ref());

        let mut only_new_refs = RefsStorage::default();
        only_new_refs.store_cell(new_dict_cell.as_ref());

        let diff = merkle_update
            .compute_removed_cells(old_dict_cell.as_ref())
            .unwrap();
        assert!(refs_for_both.remove_batch(diff));

        assert_eq!(only_new_refs.refs, refs_for_both.refs);
    }

    #[test]
    fn dict_removed_all_cells_diff() {
        // Create dict with keys 0..10
        let mut dict = Dict::<u32, u32>::new();
        for i in 0..10 {
            dict.add(i, 0).unwrap();
        }

        // Serialize old dict
        let old_dict_cell = CellBuilder::build_from(&dict).unwrap();
        let old_dict_hashes = visit_all_cells(&old_dict_cell);

        // Serialize new dict
        let new_dict_cell = CellBuilder::build_from(Dict::<u32, u32>::new()).unwrap();

        assert_ne!(old_dict_cell.as_ref(), new_dict_cell.as_ref());

        // Create merkle update
        let merkle_update = MerkleUpdate::create(
            old_dict_cell.as_ref(),
            new_dict_cell.as_ref(),
            old_dict_hashes,
        )
        .build()
        .unwrap();

        // Test diff
        let mut refs_for_both = RefsStorage::default();
        refs_for_both.store_cell(old_dict_cell.as_ref());
        refs_for_both.store_cell(new_dict_cell.as_ref());

        let mut only_new_refs = RefsStorage::default();
        only_new_refs.store_cell(new_dict_cell.as_ref());

        let diff = merkle_update
            .compute_removed_cells(old_dict_cell.as_ref())
            .unwrap();
        assert!(refs_for_both.remove_batch(diff));

        assert_eq!(only_new_refs.refs, refs_for_both.refs);
    }

    #[derive(Default)]
    struct RefsStorage<'a> {
        refs: ahash::HashMap<&'a HashBytes, u32>,
    }

    impl<'a> RefsStorage<'a> {
        fn store_cell(&mut self, root: &'a DynCell) {
            use std::collections::hash_map;

            *self.refs.entry(root.repr_hash()).or_default() += 1;

            let mut stack = vec![root.references()];
            'outer: while let Some(iter) = stack.last_mut() {
                for child in iter {
                    let hash = child.repr_hash();
                    match self.refs.entry(hash) {
                        hash_map::Entry::Occupied(mut entry) => {
                            *entry.get_mut() += 1;
                            continue;
                        }
                        hash_map::Entry::Vacant(entry) => {
                            entry.insert(1);
                        }
                    }

                    stack.push(child.references());
                    continue 'outer;
                }
                stack.pop();
            }
        }

        fn remove_batch(&mut self, mut batch: ahash::HashMap<&'a HashBytes, u32>) -> bool {
            self.refs.retain(|hash, refs| {
                if let Some(diff) = batch.remove(hash) {
                    *refs -= diff;
                }
                *refs != 0
            });
            batch.is_empty()
        }
    }
}
