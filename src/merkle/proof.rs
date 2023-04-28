use std::collections::HashMap;
use std::hash::BuildHasher;

use super::{make_pruned_branch, FilterAction, MerkleFilter};
use crate::cell::*;
use crate::error::Error;
use crate::util::*;

/// Parsed Merkle proof representation.
///
/// NOTE: Serialized into `MerkleProof` cell.
#[derive(CustomDebug, Clone)]
pub struct MerkleProof {
    /// Representation hash of the original cell.
    #[debug(with = "DisplayHash")]
    pub hash: CellHash,
    /// Representation depth of the origin cell.
    pub depth: u16,
    /// Partially pruned tree with the contents of the original cell.
    pub cell: Cell,
}

impl Eq for MerkleProof {}

impl PartialEq for MerkleProof {
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash
            && self.depth == other.depth
            && self.cell.as_ref() == other.cell.as_ref()
    }
}

impl Default for MerkleProof {
    fn default() -> Self {
        Self {
            hash: *EMPTY_CELL_HASH,
            depth: 0,
            cell: Cell::empty_cell(),
        }
    }
}

impl Load<'_> for MerkleProof {
    fn load_from(s: &mut CellSlice) -> Result<Self, Error> {
        if !s.has_remaining(Self::BITS, Self::REFS) {
            return Err(Error::CellUnderflow);
        }

        if ok!(s.get_u8(0)) != CellType::MerkleProof.to_byte() {
            return Err(Error::InvalidCell);
        }

        let res = Self {
            hash: ok!(s.get_u256(8)),
            depth: ok!(s.get_u16(8 + 256)),
            cell: ok!(s.get_reference_cloned(0)),
        };
        if res.cell.as_ref().hash(0) == &res.hash
            && res.cell.as_ref().depth(0) == res.depth
            && s.try_advance(Self::BITS, Self::REFS)
        {
            Ok(res)
        } else {
            Err(Error::InvalidCell)
        }
    }
}

impl Store for MerkleProof {
    fn store_into(&self, b: &mut CellBuilder, _: &mut dyn Finalizer) -> Result<(), Error> {
        if !b.has_capacity(Self::BITS, Self::REFS) {
            return Err(Error::CellOverflow);
        }

        let level_mask = self.cell.as_ref().level_mask();
        b.set_level_mask(level_mask.virtualize(1));
        b.set_exotic(true);
        ok!(b.store_u8(CellType::MerkleProof.to_byte()));
        ok!(b.store_u256(&self.hash));
        ok!(b.store_u16(self.depth));
        b.store_reference(self.cell.clone())
    }
}

impl MerkleProof {
    /// The number of data bits that the Merkle proof occupies.
    pub const BITS: u16 = 8 + 256 + 16;
    /// The number of references that the Merkle proof occupies.
    pub const REFS: u8 = 1;

    /// Starts building a Merkle proof for the specified root,
    /// using cells determined by filter.
    pub fn create<'a, F>(root: &'a DynCell, f: F) -> MerkleProofBuilder<'a, F>
    where
        F: MerkleFilter + 'a,
    {
        MerkleProofBuilder::new(root, f)
    }

    /// Create a Merkle proof for the single cell with the specified
    /// representation hash.
    ///
    /// Only ancestors of the first occurrence are included in the proof.
    ///
    /// Proof creation will fail if the specified child is not found.
    pub fn create_for_cell<'a>(
        root: &'a DynCell,
        child_hash: &'a CellHash,
    ) -> MerkleProofBuilder<'a, impl MerkleFilter + 'a> {
        struct RootOrChild<'a> {
            cells: ahash::HashSet<&'a CellHash>,
            child_hash: &'a CellHash,
        }

        impl MerkleFilter for RootOrChild<'_> {
            fn check(&self, cell: &CellHash) -> FilterAction {
                if self.cells.contains(cell) || cell == self.child_hash {
                    FilterAction::Include
                } else {
                    FilterAction::Skip
                }
            }
        }

        let mut stack = vec![root.references()];
        while let Some(last_cells) = stack.last_mut() {
            match last_cells.next() {
                Some(child) if child.repr_hash() == child_hash => break,
                Some(child) => stack.push(child.references()),
                None => {
                    stack.pop();
                }
            }
        }

        let mut cells = ahash::HashSet::with_capacity_and_hasher(stack.len(), Default::default());
        for item in stack {
            cells.insert(item.cell().repr_hash());
        }

        MerkleProofBuilder::new(root, RootOrChild { cells, child_hash })
    }
}

/// Helper struct to build a Merkle proof.
pub struct MerkleProofBuilder<'a, F> {
    root: &'a DynCell,
    filter: F,
}

impl<'a, F> MerkleProofBuilder<'a, F>
where
    F: MerkleFilter,
{
    /// Creates a new Merkle proof builder for the tree with the specified root,
    /// using cells determined by filter.
    pub fn new(root: &'a DynCell, f: F) -> Self {
        Self { root, filter: f }
    }

    /// Extends the builder to additionally save all hashes
    /// of cells not included in Merkle proof.
    pub fn track_pruned_branches(self) -> MerkleProofExtBuilder<'a, F> {
        MerkleProofExtBuilder {
            root: self.root,
            filter: self.filter,
        }
    }

    /// Builds a Merkle proof using the specified finalizer.
    pub fn build_ext(self, finalizer: &mut dyn Finalizer) -> Result<MerkleProof, Error> {
        let root = self.root;
        let cell = ok!(self.build_raw_ext(finalizer));
        Ok(MerkleProof {
            hash: *root.repr_hash(),
            depth: root.repr_depth(),
            cell,
        })
    }

    /// Builds a Merkle proof child cell using the specified finalizer.
    pub fn build_raw_ext(self, finalizer: &mut dyn Finalizer) -> Result<Cell, Error> {
        BuilderImpl::<ahash::RandomState> {
            root: self.root,
            filter: &self.filter,
            cells: Default::default(),
            pruned_branches: None,
            finalizer,
        }
        .build()
    }
}

impl<'a, F> MerkleProofBuilder<'a, F>
where
    F: MerkleFilter,
{
    /// Builds a Merkle proof using the default finalizer.
    pub fn build(self) -> Result<MerkleProof, Error> {
        self.build_ext(&mut Cell::default_finalizer())
    }
}

/// Helper struct to build a Merkle proof and keep track of all pruned cells.
pub struct MerkleProofExtBuilder<'a, F> {
    root: &'a DynCell,
    filter: F,
}

impl<'a, F> MerkleProofExtBuilder<'a, F>
where
    F: MerkleFilter,
{
    /// Builds a Merkle proof child cell using the specified finalizer.
    pub fn build_raw_ext(
        self,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(Cell, ahash::HashMap<&'a CellHash, bool>), Error> {
        let mut pruned_branches = Default::default();
        let mut builder = BuilderImpl {
            root: self.root,
            filter: &self.filter,
            cells: Default::default(),
            pruned_branches: Some(&mut pruned_branches),
            finalizer,
        };
        let cell = ok!(builder.build());
        Ok((cell, pruned_branches))
    }
}

struct BuilderImpl<'a, 'b, S = ahash::RandomState> {
    root: &'a DynCell,
    filter: &'b dyn MerkleFilter,
    cells: HashMap<&'a CellHash, Cell, S>,
    pruned_branches: Option<&'b mut HashMap<&'a CellHash, bool, S>>,
    finalizer: &'b mut dyn Finalizer,
}

impl<'a, 'b, S> BuilderImpl<'a, 'b, S>
where
    S: BuildHasher + Default,
{
    fn build(&mut self) -> Result<Cell, Error> {
        struct Node<'a> {
            references: RefsIter<'a>,
            descriptor: CellDescriptor,
            merkle_depth: u8,
            children: CellRefsBuilder,
        }

        if self.filter.check(self.root.repr_hash()) == FilterAction::Skip {
            return Err(Error::EmptyProof);
        }

        let mut stack = Vec::with_capacity(self.root.repr_depth() as usize);

        // Push root node
        let root_descriptor = self.root.descriptor();
        stack.push(Node {
            references: self.root.references(),
            descriptor: root_descriptor,
            merkle_depth: root_descriptor.is_merkle() as u8,
            children: CellRefsBuilder::default(),
        });

        while let Some(last) = stack.last_mut() {
            if let Some(child) = last.references.next() {
                // Process children if they are left

                let child_repr_hash = child.repr_hash();
                let child = if let Some(child) = self.cells.get(child_repr_hash) {
                    // Reused processed cells
                    child.clone()
                } else {
                    // Fetch child descriptor
                    let descriptor = child.descriptor();

                    // Check if child is in a tree
                    match self.filter.check(child_repr_hash) {
                        // Included subtrees are used as is
                        FilterAction::IncludeSubtree => {
                            last.references.peek_prev_cloned().expect("mut not fail")
                        }
                        // Replace all skipped subtrees with pruned branch cells
                        FilterAction::Skip if descriptor.reference_count() > 0 => {
                            // Create pruned branch
                            let child = ok!(make_pruned_branch_cold(
                                child,
                                last.merkle_depth,
                                self.finalizer
                            ));

                            // Insert pruned branch for the current cell
                            if let Some(pruned_branch) = &mut self.pruned_branches {
                                pruned_branch.insert(child_repr_hash, false);
                            }

                            // Use new pruned branch as a child
                            child
                        }
                        // All other cells will be included in a different branch
                        _ => {
                            // Add merkle offset to the current merkle depth
                            let merkle_depth = last.merkle_depth + descriptor.is_merkle() as u8;

                            // Push child node and start processing its references
                            stack.push(Node {
                                references: child.references(),
                                descriptor,
                                merkle_depth,
                                children: CellRefsBuilder::default(),
                            });
                            continue;
                        }
                    }
                };

                // Add child to the references builder
                _ = last.children.store_reference(child);
            } else if let Some(last) = stack.pop() {
                // Build a new cell if there are no child nodes left to process

                let cell = last.references.cell();

                // Compute children mask
                let children_mask =
                    last.descriptor.level_mask() | last.children.compute_level_mask();
                let merkle_offset = last.descriptor.is_merkle() as u8;

                // Build the cell
                let mut builder = CellBuilder::new();
                builder.set_exotic(last.descriptor.is_exotic());
                builder.set_level_mask(children_mask.virtualize(merkle_offset));
                _ = builder.store_cell_data(cell);
                builder.set_references(last.children);
                let proof_cell = ok!(builder.build_ext(self.finalizer));

                // Save this cell as processed cell
                self.cells.insert(cell.repr_hash(), proof_cell.clone());

                match stack.last_mut() {
                    // Append this cell to the ancestor
                    Some(last) => {
                        _ = last.children.store_reference(proof_cell);
                    }
                    // Or return it as a result (for the root node)
                    None => return Ok(proof_cell),
                }
            }
        }

        // Something is wrong if we are here
        Err(Error::EmptyProof)
    }
}

#[cold]
fn make_pruned_branch_cold(
    cell: &DynCell,
    merkle_depth: u8,
    finalizer: &mut dyn Finalizer,
) -> Result<Cell, Error> {
    make_pruned_branch(cell, merkle_depth, finalizer)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::Error;
    use crate::prelude::*;

    #[test]
    fn correct_store_load() {
        let proof = MerkleProof::default();
        let cell = CellBuilder::build_from(&proof).unwrap();

        let parsed = cell.as_ref().parse::<MerkleProof>().unwrap();
        assert_eq!(parsed, proof);
    }

    #[test]
    fn test_proof() {
        const BOC: &str = "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";

        let root = Boc::decode_base64(BOC).unwrap();
        let target_hash = root.as_ref().reference(1).unwrap().repr_hash();

        let merkle_proof = MerkleProof::create_for_cell(root.as_ref(), target_hash)
            .build()
            .unwrap();

        let virtual_root = merkle_proof.cell.as_ref().virtualize();
        println!("{}", virtual_root.display_tree());

        assert_eq!(root.as_ref().repr_hash(), virtual_root.repr_hash());
        assert_eq!(root.as_ref().repr_depth(), virtual_root.repr_depth());
    }

    #[test]
    #[cfg_attr(miri, ignore)] // takes too long to execute on miri
    fn create_proof_for_deep_cell() {
        let mut cell = Cell::empty_cell();
        for i in 0..65000 {
            let mut builder = CellBuilder::new();
            builder.store_u32(i).unwrap();
            builder.store_reference(cell).unwrap();
            cell = builder.build().unwrap();
        }

        {
            let encoded = Boc::encode_base64(cell.as_ref());
            let decoded = Boc::decode_base64(encoded).unwrap();
            assert_eq!(decoded.as_ref(), cell.as_ref());
        }

        let cell = MerkleProof::create_for_cell(cell.as_ref(), EMPTY_CELL_HASH)
            .build()
            .unwrap();

        let encoded = BocRepr::encode_base64(&cell).unwrap();
        let decoded = Boc::decode_base64(encoded)
            .unwrap()
            .as_ref()
            .parse::<MerkleProof>()
            .unwrap();

        assert_eq!(cell, decoded);
    }

    #[test]
    fn create_proof_for_dict() {
        // Create dict with keys 0..10
        let mut dict = Dict::<u32, u32>::new();

        for i in 0..10 {
            dict.add(i, i * 10).unwrap();
        }

        // Create a usage tree for accessing an element with keys 0 and 9
        let usage_tree = UsageTree::new(UsageTreeMode::OnDataAccess);
        let tracked_cell = usage_tree.track(&CellBuilder::build_from(dict).unwrap());
        let tracked_dict = tracked_cell.as_ref().parse::<Dict<u32, u32>>().unwrap();
        tracked_dict.get(0).unwrap().unwrap();
        tracked_dict.get(9).unwrap().unwrap();

        // Create proof from the usage tree
        let merkle_proof = MerkleProof::create(tracked_cell.as_ref(), usage_tree)
            .build()
            .unwrap();

        // Try to read some keys
        let dict = merkle_proof.cell.as_ref().virtualize();
        let dict = dict.parse::<Dict<u32, u32>>().unwrap();
        dict.get(0).unwrap().unwrap();
        dict.get(9).unwrap().unwrap();

        assert!(matches!(dict.get(5), Err(Error::PrunedBranchAccess)));
    }

    #[test]
    fn proof_with_subtree() -> anyhow::Result<()> {
        let mut dict = Dict::<u32, u32>::new();
        for i in 0..10 {
            dict.add(i, i * 10)?;
        }
        let dict = CellBuilder::build_from(dict)?;

        let some_other_cell = {
            let mut builder = CellBuilder::new();
            builder.store_u128(123123)?;
            builder.store_reference(Cell::empty_cell())?;
            builder.store_reference(Cell::empty_cell())?;
            builder.build()?
        };

        let root_cell = {
            let mut builder = CellBuilder::new();
            builder.store_u128(321321)?;
            builder.store_reference(some_other_cell)?;
            builder.store_reference(dict.clone())?;
            builder.build()?
        };

        let mut usage_tree = UsageTree::new(UsageTreeMode::OnDataAccess).with_subtrees();
        let root_cell = usage_tree.track(&root_cell);

        {
            let mut root_cell = root_cell.as_ref().as_slice()?;
            root_cell.load_u32().unwrap();

            assert!(usage_tree.add_subtree(dict.as_ref()));
        }

        let proof = MerkleProof::create(root_cell.as_ref(), usage_tree).build()?;
        let mut virtual_cell = proof.cell.as_ref().virtualize().as_slice()?;

        assert_eq!(virtual_cell.load_u128(), Ok(321321));

        let first_ref = virtual_cell.load_reference()?;
        assert_eq!(first_ref.cell_type(), CellType::PrunedBranch);

        let second_ref = virtual_cell.load_reference()?;
        assert_eq!(second_ref.cell_type(), CellType::Ordinary);
        assert!(second_ref.descriptor().level_mask().is_empty());

        let dict = second_ref.parse::<Dict<u32, u32>>()?;
        for (i, entry) in dict.iter().enumerate() {
            let (key, value) = entry?;
            assert_eq!(i, key as usize);
            assert_eq!(key * 10, value);
        }
        assert_eq!(dict.values().count(), 10);

        Ok(())
    }
}
