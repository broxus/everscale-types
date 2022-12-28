use std::collections::{HashMap, HashSet};
use std::hash::BuildHasher;

use super::make_pruned_branch;
use crate::cell::*;

pub struct MerkleProof<C: CellFamily> {
    pub hash: CellHash,
    pub depth: u16,
    pub cell: CellContainer<C>,
}

impl<C: CellFamily> std::fmt::Debug for MerkleProof<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MerkleProof")
            .field("hash", &hex::encode(self.hash.as_slice()))
            .field("depth", &self.depth)
            .field("cell", &self.cell.as_ref().debug_root())
            .finish()
    }
}

impl<C: CellFamily> Eq for MerkleProof<C> {}
impl<C: CellFamily> PartialEq for MerkleProof<C> {
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash
            && self.depth == other.depth
            && self.cell.as_ref() == other.cell.as_ref()
    }
}

impl<C: CellFamily> Default for MerkleProof<C> {
    fn default() -> Self {
        Self {
            hash: EMPTY_CELL_HASH,
            depth: 0,
            cell: C::empty_cell(),
        }
    }
}

impl<C: CellFamily> Load<'_, C> for MerkleProof<C> {
    fn load_from(s: &mut CellSlice<C>) -> Option<Self> {
        if !s.has_remaining(Self::BITS, Self::REFS) {
            return None;
        }

        if s.get_u8(0)? != CellType::MerkleProof.to_byte() {
            return None;
        }

        let res = Self {
            hash: s.get_u256(8)?,
            depth: s.get_u16(8 + 256)?,
            cell: s.get_reference_cloned(0)?,
        };
        if res.cell.as_ref().hash(0) == &res.hash
            && res.cell.as_ref().depth(0) == res.depth
            && s.try_advance(Self::BITS, Self::REFS)
        {
            Some(res)
        } else {
            None
        }
    }
}

impl<C: CellFamily> Store<C> for MerkleProof<C> {
    fn store_into(&self, b: &mut CellBuilder<C>) -> bool {
        if !b.has_capacity(Self::BITS, Self::REFS) {
            return false;
        }

        let level_mask = self.cell.as_ref().level_mask();
        b.set_level_mask(level_mask.virtualize(1));
        b.set_exotic(true);
        b.store_u8(CellType::MerkleProof.to_byte())
            && b.store_u256(&self.hash)
            && b.store_u16(self.depth)
            && b.store_reference(self.cell.clone())
    }
}

impl<C: CellFamily> MerkleProof<C> {
    pub const BITS: u16 = 8 + 256 + 16;
    pub const REFS: u8 = 1;

    pub fn create<'a, F, S>(root: &'a dyn Cell<C>, f: F) -> MerkleProofBuilder<'a, C>
    where
        F: FnMut(&CellHash) -> bool + 'a,
    {
        MerkleProofBuilder::new(root, f)
    }

    pub fn create_for_cell<'a>(
        root: &'a dyn Cell<C>,
        child_hash: &'a CellHash,
    ) -> MerkleProofBuilder<'a, C> {
        MerkleProofBuilder::new_for_cell(root, child_hash)
    }
}

pub struct MerkleProofBuilder<'a, C: CellFamily, S = ahash::RandomState> {
    root: &'a dyn Cell<C>,
    predicate: Box<dyn FnMut(&CellHash) -> bool + 'a>,
    cells: HashMap<CellHash, CellContainer<C>, S>,
    pruned_branches: Option<&'a mut HashSet<CellHash, S>>,
}

impl<'a, C: CellFamily, S> MerkleProofBuilder<'a, C, S>
where
    S: BuildHasher + Default,
{
    pub fn new<F>(root: &'a dyn Cell<C>, f: F) -> Self
    where
        F: FnMut(&CellHash) -> bool + 'a,
    {
        MerkleProofBuilder {
            root,
            predicate: Box::new(f),
            cells: Default::default(),
            pruned_branches: None,
        }
    }

    pub fn new_for_cell(root: &'a dyn Cell<C>, child_hash: &'a CellHash) -> Self {
        let repr_hash = *root.repr_hash();
        MerkleProofBuilder {
            root,
            predicate: Box::new(move |hash| hash == &repr_hash || hash == child_hash),
            cells: Default::default(),
            pruned_branches: None,
        }
    }
}

impl<'a, C: CellFamily, S> MerkleProofBuilder<'a, C, S>
where
    S: BuildHasher,
{
    pub fn track_pruned_branches(mut self, pruned_branches: &'a mut HashSet<CellHash, S>) -> Self {
        self.pruned_branches = Some(pruned_branches);
        self
    }

    pub fn build_ext(mut self, finalizer: &mut dyn Finalizer<C>) -> Option<MerkleProof<C>> {
        if !(self.predicate)(self.root.repr_hash()) {
            return None;
        }
        let cell = self.fill(self.root, 0, finalizer)?;
        Some(MerkleProof {
            hash: *self.root.repr_hash(),
            depth: self.root.repr_depth(),
            cell,
        })
    }

    fn fill(
        &mut self,
        cell: &dyn Cell<C>,
        merkle_depth: u8,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Option<CellContainer<C>> {
        let descriptor = cell.descriptor();
        let merkle_offset = descriptor.cell_type().is_merkle() as u8;
        let child_merkle_depth = merkle_depth + merkle_offset;

        let mut result = CellBuilder::<C>::new();
        result.set_exotic(descriptor.is_exotic());

        let mut children_mask = descriptor.level_mask();
        for child in cell.references().cloned() {
            let child_repr_hash = child.as_ref().repr_hash();

            let child = if let Some(child) = self.cells.get(child_repr_hash) {
                child.clone()
            } else if child.as_ref().reference_count() == 0 || (self.predicate)(child_repr_hash) {
                self.fill(child.as_ref(), child_merkle_depth, finalizer)?
            } else {
                let child = make_pruned_branch(child.as_ref(), merkle_depth, finalizer)?;
                if let Some(pruned_branch) = &mut self.pruned_branches {
                    pruned_branch.insert(*child_repr_hash);
                }
                child
            };

            children_mask |= child.as_ref().level_mask();
            result.store_reference(child);
        }

        result.set_level_mask(children_mask.virtualize(merkle_offset));
        result.store_slice_data(&cell.as_slice());

        let proof_cell = result.build_ext(finalizer)?;
        self.cells.insert(*cell.repr_hash(), proof_cell.clone());

        Some(proof_cell)
    }
}

impl<'a, C: DefaultFinalizer, S> MerkleProofBuilder<'a, C, S>
where
    S: BuildHasher,
{
    pub fn build(self) -> Option<MerkleProof<C>> {
        self.build_ext(&mut C::default_finalizer())
    }
}

#[cfg(test)]
mod tests {
    use crate::{RcBoc, RcCellBuilder, RcCellFamily};

    use super::*;

    #[test]
    fn correct_store_load() {
        let default = MerkleProof::<RcCellFamily>::default();

        let mut builder = RcCellBuilder::new();
        assert!(default.store_into(&mut builder));
        let cell = builder.build().unwrap();

        let parsed = MerkleProof::load_from(&mut cell.as_slice()).unwrap();
        assert_eq!(default, parsed);
    }

    #[test]
    fn test_proof() {
        let root = RcBoc::decode_base64("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").unwrap();
        let target_hash = root.reference(1).unwrap().repr_hash();

        let merkle_proof = MerkleProof::create_for_cell(root.as_ref(), target_hash)
            .build()
            .unwrap();

        let virtual_root = merkle_proof.cell.virtualize();
        println!("{}", virtual_root.display_tree());

        assert_eq!(root.repr_hash(), virtual_root.repr_hash());
        assert_eq!(root.repr_depth(), virtual_root.repr_depth());
    }
}
