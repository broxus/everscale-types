use dashmap::DashMap;
use std::hash::BuildHasher;
use std::sync::mpsc;

use crate::cell::*;
use crate::error::Error;
use crate::util::unlikely;

use super::{make_pruned_branch, FilterAction, MerkleFilter};

/// Non-owning parsed Merkle proof representation.
///
/// NOTE: Serialized into `MerkleProof` cell.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct MerkleProofRef<'a> {
    /// Representation hash of the original cell.
    pub hash: HashBytes,
    /// Representation depth of the origin cell.
    pub depth: u16,
    /// Partially pruned tree with the contents of the original cell.
    pub cell: &'a DynCell,
}

impl Eq for MerkleProofRef<'_> {}

impl PartialEq for MerkleProofRef<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash && self.depth == other.depth && *self.cell == *other.cell
    }
}

impl PartialEq<MerkleProof> for MerkleProofRef<'_> {
    fn eq(&self, other: &MerkleProof) -> bool {
        self.hash == other.hash && self.depth == other.depth && *self.cell == *other.cell
    }
}

impl Default for MerkleProofRef<'_> {
    fn default() -> Self {
        Self {
            hash: *EMPTY_CELL_HASH,
            depth: 0,
            cell: Cell::empty_cell_ref(),
        }
    }
}

impl<'a> LoadCell<'a> for MerkleProofRef<'a> {
    fn load_from_cell(cell: &'a DynCell) -> Result<Self, Error> {
        if unlikely(!cell.is_exotic()) {
            return Err(Error::UnexpectedOrdinaryCell);
        }

        let mut s = cell.as_slice_allow_exotic();
        if s.size_bits() != MerkleProof::BITS || s.size_refs() != MerkleProof::REFS {
            return Err(Error::CellUnderflow);
        }

        if ok!(s.load_u8()) != CellType::MerkleProof.to_byte() {
            return Err(Error::InvalidCell);
        }

        let res = Self {
            hash: ok!(s.load_u256()),
            depth: ok!(s.load_u16()),
            cell: ok!(s.load_reference()),
        };
        debug_assert!(s.is_empty());

        if res.cell.hash(0) == &res.hash && res.cell.depth(0) == res.depth {
            Ok(res)
        } else {
            Err(Error::InvalidCell)
        }
    }
}

/// Parsed Merkle proof representation.
///
/// NOTE: Serialized into `MerkleProof` cell.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MerkleProof {
    /// Representation hash of the original cell.
    pub hash: HashBytes,
    /// Representation depth of the origin cell.
    pub depth: u16,
    /// Partially pruned tree with the contents of the original cell.
    #[cfg_attr(feature = "serde", serde(with = "crate::boc::Boc"))]
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

impl PartialEq<MerkleProofRef<'_>> for MerkleProof {
    fn eq(&self, other: &MerkleProofRef<'_>) -> bool {
        self.hash == other.hash && self.depth == other.depth && *self.cell == *other.cell
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

impl<'a> LoadCell<'a> for MerkleProof {
    fn load_from_cell(cell: &'a DynCell) -> Result<Self, Error> {
        if unlikely(!cell.is_exotic()) {
            return Err(Error::UnexpectedOrdinaryCell);
        }

        let mut s = cell.as_slice_allow_exotic();
        if s.size_bits() != MerkleProof::BITS || s.size_refs() != MerkleProof::REFS {
            return Err(Error::CellUnderflow);
        }

        if ok!(s.load_u8()) != CellType::MerkleProof.to_byte() {
            return Err(Error::InvalidCell);
        }

        let res = Self {
            hash: ok!(s.load_u256()),
            depth: ok!(s.load_u16()),
            cell: ok!(s.load_reference_cloned()),
        };
        debug_assert!(s.is_empty());

        if res.cell.hash(0) == &res.hash && res.cell.depth(0) == res.depth {
            Ok(res)
        } else {
            Err(Error::InvalidCell)
        }
    }
}

impl Store for MerkleProof {
    fn store_into(&self, b: &mut CellBuilder, _: &dyn CellContext) -> Result<(), Error> {
        if !b.has_capacity(Self::BITS, Self::REFS) {
            return Err(Error::CellOverflow);
        }

        b.set_exotic(true);
        ok!(b.store_u8(CellType::MerkleProof.to_byte()));
        ok!(b.store_u256(&self.hash));
        ok!(b.store_u16(self.depth));
        b.store_reference(self.cell.clone())
    }
}

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for MerkleProof {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let cell = Cell::arbitrary(u).and_then(crate::arbitrary::check_max_depth)?;
        Ok(Self {
            hash: *cell.hash(0),
            depth: cell.depth(0),
            cell,
        })
    }

    fn size_hint(_: usize) -> (usize, Option<usize>) {
        (2, None)
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
        F: MerkleFilter + Send + Sync + 'a,
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
        child_hash: &'a HashBytes,
    ) -> MerkleProofBuilder<'a, impl MerkleFilter + 'a> {
        struct RootOrChild<'a> {
            cells: ahash::HashSet<&'a HashBytes>,
            child_hash: &'a HashBytes,
        }

        impl MerkleFilter for RootOrChild<'_> {
            fn check(&self, cell: &HashBytes) -> FilterAction {
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
    allow_different_root: bool,
    prune_big_cells: bool,
}

impl<'a, F> MerkleProofBuilder<'a, F>
where
    F: MerkleFilter + Send + Sync,
{
    /// Creates a new Merkle proof builder for the tree with the specified root,
    /// using cells determined by filter.
    pub fn new(root: &'a DynCell, f: F) -> Self {
        Self {
            root,
            filter: f,
            allow_different_root: false,
            prune_big_cells: false,
        }
    }

    /// Mark whether the different root is ok for this proof.
    pub fn allow_different_root(mut self, allow: bool) -> Self {
        self.allow_different_root = allow;
        self
    }

    /// Prune not visited ordinary cells without references based on
    /// their bit len.
    pub fn prune_big_cells(mut self, allow: bool) -> Self {
        self.prune_big_cells = allow;
        self
    }

    /// Extends the builder to additionally save all hashes
    /// of cells not included in Merkle proof.
    pub fn track_pruned_branches(self) -> MerkleProofExtBuilder<'a, F> {
        MerkleProofExtBuilder {
            root: self.root,
            filter: self.filter,
            allow_different_root: self.allow_different_root,
            prune_big_cells: self.prune_big_cells,
        }
    }

    /// Builds a Merkle proof using the specified cell context.
    pub fn build_ext(
        self,
        context: &(dyn CellContext + Send + Sync),
    ) -> Result<MerkleProof, Error> {
        let root = self.root;
        let cell = ok!(self.build_raw_ext(context));
        Ok(MerkleProof {
            hash: *root.repr_hash(),
            depth: root.repr_depth(),
            cell,
        })
    }

    // /// TODO
    // pub fn par_build_ext(
    //     self,
    //     context: &(dyn CellContext + Send + Sync),
    //     par_cells: &ahash::HashSet<HashBytes>,
    // ) -> Result<MerkleProof, Error> {
    //     let root = self.root;
    //     let cell = ok!(self.par_build_raw_ext(context, par_cells));
    //     Ok(MerkleProof {
    //         hash: *root.repr_hash(),
    //         depth: root.repr_depth(),
    //         cell,
    //     })
    // }

    /// Builds a Merkle proof child cell using the specified cell context.
    pub fn build_raw_ext(self, context: &(dyn CellContext + Send + Sync)) -> Result<Cell, Error> {
        BuilderImpl::<ahash::RandomState> {
            root: self.root,
            filter: &self.filter,
            cells: Default::default(),
            pruned_branches: None,
            context,
            allow_different_root: self.allow_different_root,
            prune_big_cells: self.prune_big_cells,
        }
        .build()
    }

    // /// Builds a Merkle proof child cell using the specified cell context.
    // pub fn par_build_raw_ext(
    //     self,
    //     context: &(dyn CellContext + Send + Sync),
    //     par_cells: &ahash::HashSet<HashBytes>,
    // ) -> Result<Cell, Error> {
    //     BuilderImpl::<ahash::RandomState> {
    //         root: self.root,
    //         filter: &self.filter,
    //         cells: Default::default(),
    //         pruned_branches: None,
    //         context,
    //         allow_different_root: self.allow_different_root,
    //         prune_big_cells: self.prune_big_cells,
    //     }
    //     .par_build(par_cells)
    // }
}

impl<F> MerkleProofBuilder<'_, F>
where
    F: MerkleFilter + Send + Sync,
{
    /// Builds a Merkle proof using an empty cell context.
    pub fn build(self) -> Result<MerkleProof, Error> {
        self.build_ext(Cell::empty_context())
    }

    // /// TODO
    // pub fn par_build(self, par_cells: &ahash::HashSet<HashBytes>) -> Result<MerkleProof, Error> {
    //     self.par_build_ext(Cell::empty_context(), par_cells)
    // }
}

/// Helper struct to build a Merkle proof and keep track of all pruned cells.
pub struct MerkleProofExtBuilder<'a, F> {
    root: &'a DynCell,
    filter: F,
    allow_different_root: bool,
    prune_big_cells: bool,
}

impl<F> MerkleProofExtBuilder<'_, F> {
    /// Mark whether the different root is ok for this proof.
    pub fn allow_different_root(mut self, allow: bool) -> Self {
        self.allow_different_root = allow;
        self
    }

    /// Prune not visited ordinary cells without references based on
    /// their bit len.
    pub fn prune_big_cells(mut self, allow: bool) -> Self {
        self.prune_big_cells = allow;
        self
    }
}

impl<'a, F> MerkleProofExtBuilder<'a, F>
where
    F: MerkleFilter + Send + Sync,
{
    /// Builds a Merkle proof child cell using the specified cell context.
    pub fn build_raw_ext<'c: 'a>(
        self,
        context: &'c (dyn CellContext + Send + Sync),
    ) -> Result<(Cell, DashMap<&'a HashBytes, bool>), Error> {
        let pruned_branches = Default::default();
        let mut builder = BuilderImpl {
            root: self.root,
            filter: &self.filter,
            cells: Default::default(),
            pruned_branches: Some(&pruned_branches),
            context,
            allow_different_root: self.allow_different_root,
            prune_big_cells: self.prune_big_cells,
        };
        let cell = ok!(builder.build());
        Ok((cell, pruned_branches))
    }

    // /// TODO
    // pub fn par_build_raw_ext<'c: 'a>(
    //     self,
    //     context: &'c (dyn CellContext + Send + Sync),
    //     par_cells: &ahash::HashSet<HashBytes>,
    // ) -> Result<(Cell, DashMap<&'a HashBytes, bool>), Error> {
    //     let pruned_branches = Default::default();
    //     let builder = BuilderImpl {
    //         root: self.root,
    //         filter: &self.filter,
    //         cells: Default::default(),
    //         pruned_branches: Some(&pruned_branches),
    //         context,
    //         allow_different_root: self.allow_different_root,
    //         prune_big_cells: self.prune_big_cells,
    //     };
    //     let cell = ok!(builder.par_build(par_cells));
    //     Ok((cell, pruned_branches))
    // }
}

struct BuilderImpl<'a, 'b, 'c: 'a, S = ahash::RandomState> {
    root: &'a DynCell,
    filter: &'b (dyn MerkleFilter + Send + Sync),
    cells: DashMap<HashBytes, Cell, S>,
    pruned_branches: Option<&'b DashMap<&'a HashBytes, bool, S>>,
    context: &'c (dyn CellContext + Send + Sync),
    allow_different_root: bool,
    prune_big_cells: bool,
}

impl<S> BuilderImpl<'_, '_, '_, S>
where
    S: BuildHasher + Default + Clone + Send + Sync,
{
    fn build(&mut self) -> Result<Cell, Error> {
        const PRUNED_BITS_THRESHOLD: u16 = 288;

        struct Node<'a> {
            references: RefsIter<'a>,
            descriptor: CellDescriptor,
            merkle_depth: u8,
            children: ParCellRefsBuilder,
        }

        if !self.allow_different_root
            && self.filter.check(self.root.repr_hash()) == FilterAction::Skip
        {
            return Err(Error::EmptyProof);
        }

        let root_cell = rayon::scope(|s| {
            let mut stack = Vec::with_capacity(self.root.repr_depth() as usize);

            // Push root node
            let root_descriptor = self.root.descriptor();
            stack.push(Node {
                references: self.root.references(),
                descriptor: root_descriptor,
                merkle_depth: root_descriptor.is_merkle() as u8,
                children: ParCellRefsBuilder::default(),
            });

            while let Some(last) = stack.last_mut() {
                if let Some(child) = last.references.next() {
                    // Process children if they are left

                    let child_repr_hash = child.repr_hash();

                    let child = if let Some(child) = self.cells.get(child_repr_hash) {
                        // Reused processed cells
                        ParCell::Ordinary(child.clone())
                    } else {
                        // Fetch child descriptor
                        let descriptor = child.descriptor();

                        // Check if child is in a tree
                        match self.filter.check(child_repr_hash) {
                            // Included subtrees are used as is
                            FilterAction::IncludeSubtree => ParCell::Ordinary(
                                last.references.peek_prev_cloned().expect("mut not fail"),
                            ),
                            // Replace all skipped subtrees with pruned branch cells
                            FilterAction::Skip
                                if descriptor.reference_count() > 0
                                    || self.prune_big_cells
                                        && child.bit_len() > PRUNED_BITS_THRESHOLD =>
                            {
                                // Create pruned branch
                                let child = ok!(make_pruned_branch_cold(
                                    child,
                                    last.merkle_depth,
                                    self.context
                                ));

                                // Insert pruned branch for the current cell
                                if let Some(pruned_branch) = self.pruned_branches {
                                    pruned_branch.insert(child_repr_hash, false);
                                }

                                // Use new pruned branch as a child
                                ParCell::Ordinary(child)
                            }
                            // All other cells will be included in a different branch
                            _ => {
                                if child.repr_depth() < 5 {
                                    // Add merkle offset to the current merkle depth
                                    let merkle_depth =
                                        last.merkle_depth + descriptor.is_merkle() as u8;

                                    // Push child node and start processing its references
                                    stack.push(Node {
                                        references: child.references(),
                                        descriptor,
                                        merkle_depth,
                                        children: ParCellRefsBuilder::default(),
                                    });

                                    continue;
                                } else {
                                    let last_merkle_depth = last.merkle_depth;

                                    let (tx, rx) = mpsc::channel();

                                    let context = self.context;
                                    let ctx_filter = self.filter;
                                    let ctx_cells = &self.cells;
                                    let ctx_pruned_branches = &self.pruned_branches;
                                    let ctx_prune_big_cells = &self.prune_big_cells;

                                    struct Node<'a> {
                                        references: RefsIter<'a>,
                                        descriptor: CellDescriptor,
                                        merkle_depth: u8,
                                        children: CellRefsBuilder,
                                    }

                                    s.spawn(move |_| {
                                        let mut stack =
                                            Vec::with_capacity(child.repr_depth() as usize);

                                        // Fetch child descriptor
                                        let child_descriptor = child.descriptor();

                                        // Add merkle offset to the current merkle depth
                                        let merkle_depth =
                                            last_merkle_depth + child_descriptor.is_merkle() as u8;

                                        stack.push(Node {
                                            references: child.references(),
                                            descriptor: child_descriptor,
                                            merkle_depth,
                                            children: CellRefsBuilder::default(),
                                        });

                                        while let Some(last) = stack.last_mut() {
                                            if let Some(child) = last.references.next() {
                                                // Process children if they are left

                                                let child_repr_hash = child.repr_hash();
                                                let child = if let Some(child) =
                                                    ctx_cells.get(child_repr_hash)
                                                {
                                                    // Reused processed cells
                                                    child.clone()
                                                } else {
                                                    // Fetch child descriptor
                                                    let descriptor = child.descriptor();

                                                    // Check if child is in a tree
                                                    match ctx_filter.check(child_repr_hash) {
                                                        // Included subtrees are used as is
                                                        FilterAction::IncludeSubtree => last
                                                            .references
                                                            .peek_prev_cloned()
                                                            .expect("mut not fail"),
                                                        // Replace all skipped subtrees with pruned branch cells
                                                        FilterAction::Skip
                                                            if descriptor.reference_count() > 0
                                                                || *ctx_prune_big_cells
                                                                    && child.bit_len()
                                                                        > PRUNED_BITS_THRESHOLD =>
                                                        {
                                                            // Create pruned branch
                                                            let child = make_pruned_branch_cold(
                                                                child,
                                                                last.merkle_depth,
                                                                context,
                                                            )
                                                            .unwrap();

                                                            // Insert pruned branch for the current cell
                                                            if let Some(pruned_branch) =
                                                                ctx_pruned_branches
                                                            {
                                                                pruned_branch
                                                                    .insert(child_repr_hash, false);
                                                            }

                                                            // Use new pruned branch as a child
                                                            child
                                                        }
                                                        // All other cells will be included in a different branch
                                                        _ => {
                                                            // Add merkle offset to the current merkle depth
                                                            let merkle_depth = last.merkle_depth
                                                                + descriptor.is_merkle() as u8;

                                                            // Push child node and start processing its references
                                                            stack.push(Node {
                                                                references: child.references(),
                                                                descriptor,
                                                                merkle_depth,
                                                                children: CellRefsBuilder::default(
                                                                ),
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

                                                // Build the cell
                                                let mut builder = CellBuilder::new();
                                                builder.set_exotic(last.descriptor.is_exotic());
                                                _ = builder.store_cell_data(cell);
                                                builder.set_references(last.children);
                                                let proof_cell =
                                                    builder.build_ext(context).unwrap();

                                                // Save this cell as processed cell
                                                ctx_cells
                                                    .insert(*cell.repr_hash(), proof_cell.clone());

                                                match stack.last_mut() {
                                                    // Append this cell to the ancestor
                                                    Some(last) => {
                                                        _ = last
                                                            .children
                                                            .store_reference(proof_cell);
                                                    }
                                                    // Or return it as a result (for the root node)
                                                    None => tx.send(proof_cell).unwrap(),
                                                }
                                            }
                                        }
                                    });

                                    ParCell::Channel(rx)
                                }
                            }
                        }
                    };

                    // Add child to the references builder
                    _ = last.children.store_reference(child);
                } else if let Some(last) = stack.pop() {
                    // Build a new ParCell if there are no child nodes left to process

                    let cell = last.references.cell();

                    // Build the cell
                    let mut builder = CellDataBuilder::new();
                    builder.store_cell_data(cell)?;

                    let proof_cell = if last.children.is_ordinary() {
                        // Build ordinary cell
                        let mut builder = CellBuilder::new();
                        builder.set_exotic(last.descriptor.is_exotic());
                        _ = builder.store_cell_data(cell);
                        builder.set_references(last.children.children()?);
                        let proof_cell = ok!(builder.build_ext(self.context));

                        ParCell::Ordinary(proof_cell)
                    } else {
                        // Build the cell
                        let mut builder = CellDataBuilder::new();
                        builder.store_cell_data(cell)?;

                        let cell = ParCellParts {
                            data: builder,
                            is_exotic: last.descriptor.is_exotic(),
                            refs: last.children.0,
                        };

                        ParCell::Partial(Box::new(cell))
                    };

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
        })?;

        fn traverse(
            node: &ParCell,
            context: &(dyn CellContext + Send + Sync),
        ) -> Result<Cell, Error> {
            match node {
                ParCell::Ordinary(cell) => Ok(cell.clone()),
                ParCell::Channel(rx) => {
                    let cell = rx.recv().unwrap();
                    Ok(cell)
                }
                ParCell::Partial(node) => {
                    let mut refs_builder = CellRefsBuilder::default();

                    for child in node.refs.as_ref() {
                        let cell = traverse(child, context)?;
                        refs_builder.store_reference(cell)?;
                    }

                    let cell_builder =
                        CellBuilder::from_parts(node.is_exotic, node.data.clone(), refs_builder);

                    let cell = cell_builder.build_ext(context)?;
                    Ok(cell)
                }
            }
        }

        match root_cell {
            ParCell::Ordinary(cell) => Ok(cell),
            ParCell::Channel(rx) => Ok(rx.recv().unwrap()),
            ParCell::Partial(cell_parts) => traverse(&ParCell::Partial(cell_parts), self.context),
        }
    }

    // fn par_build(&self, par_cells: &ahash::HashSet<HashBytes>) -> Result<Cell, Error> {
    //     const PRUNED_BITS_THRESHOLD: u16 = 288;
    //
    //     struct Node<'a> {
    //         references: RefsIter<'a>,
    //         descriptor: CellDescriptor,
    //         merkle_depth: u8,
    //         children: CellRefsBuilder,
    //     }
    //
    //     fn build_cell<'a, 'b, S>(
    //         last: Node<'a>,
    //         ctx_builder: &BuilderImpl<'b, '_, '_, S>,
    //     ) -> Result<Cell, Error>
    //     where
    //         S: BuildHasher + Default + Clone + Send + Sync,
    //     {
    //         let cell = last.references.cell();
    //
    //         // Build the cell
    //         let mut builder = CellBuilder::new();
    //         builder.set_exotic(last.descriptor.is_exotic());
    //         _ = builder.store_cell_data(cell);
    //         builder.set_references(last.children);
    //         let proof_cell = ok!(builder.build_ext(ctx_builder.context));
    //
    //         // Save this cell as processed cell
    //         ctx_builder
    //             .cells
    //             .insert(*cell.repr_hash(), proof_cell.clone());
    //
    //         Ok(proof_cell)
    //     }
    //
    //     fn process_cell<'a, S>(
    //         child: &'a DynCell,
    //         last: &mut Node,
    //         ctx_builder: &BuilderImpl<'a, '_, '_, S>,
    //     ) -> Result<Option<Node<'a>>, Error>
    //     where
    //         S: BuildHasher + Default + Clone + Send + Sync,
    //     {
    //         let child_repr_hash = child.repr_hash();
    //
    //         let child = if let Some(child) = ctx_builder.cells.get(child_repr_hash) {
    //             // Reused processed cells
    //             child.clone()
    //         } else {
    //             // Fetch child descriptor
    //             let descriptor = child.descriptor();
    //
    //             // Check if child is in a tree
    //             match ctx_builder.filter.check(child_repr_hash) {
    //                 // Included subtrees are used as is
    //                 FilterAction::IncludeSubtree => {
    //                     last.references.peek_prev_cloned().expect("mut not fail")
    //                 }
    //                 // Replace all skipped subtrees with pruned branch cells
    //                 FilterAction::Skip
    //                     if descriptor.reference_count() > 0
    //                         || ctx_builder.prune_big_cells
    //                             && child.bit_len() > PRUNED_BITS_THRESHOLD =>
    //                 {
    //                     // Create pruned branch
    //                     let child = ok!(make_pruned_branch_cold(
    //                         child,
    //                         last.merkle_depth,
    //                         ctx_builder.context
    //                     ));
    //
    //                     // Insert pruned branch for the current cell
    //                     if let Some(pruned_branch) = ctx_builder.pruned_branches {
    //                         pruned_branch.insert(child_repr_hash, false);
    //                     }
    //
    //                     // Use new pruned branch as a child
    //                     child
    //                 }
    //                 // All other cells will be included in a different branch
    //                 _ => {
    //                     // Add merkle offset to the current merkle depth
    //                     let merkle_depth = last.merkle_depth + descriptor.is_merkle() as u8;
    //
    //                     return Ok(Some(Node {
    //                         references: child.references(),
    //                         descriptor,
    //                         merkle_depth,
    //                         children: CellRefsBuilder::default(),
    //                     }));
    //                 }
    //             }
    //         };
    //
    //         // Add child to the references builder
    //         _ = last.children.store_reference(child);
    //
    //         Ok(None)
    //     }
    //
    //     if !self.allow_different_root
    //         && self.filter.check(self.root.repr_hash()) == FilterAction::Skip
    //     {
    //         return Err(Error::EmptyProof);
    //     }
    //
    //     let par_buffer = DashMap::with_capacity(par_cells.len());
    //
    //     rayon::scope(|s| {
    //         let mut stack = Vec::with_capacity(self.root.repr_depth() as usize);
    //
    //         // Push root node
    //         let root_descriptor = self.root.descriptor();
    //         stack.push(Node {
    //             references: self.root.references(),
    //             descriptor: root_descriptor,
    //             merkle_depth: root_descriptor.is_merkle() as u8,
    //             children: CellRefsBuilder::default(),
    //         });
    //
    //         while let Some(last) = stack.last_mut() {
    //             if let Some(child) = last.references.next() {
    //                 // Process children if they are left
    //                 let child_repr_hash = child.repr_hash();
    //
    //                 if par_cells.contains(child_repr_hash) {
    //                     let last_merkle_depth = last.merkle_depth;
    //
    //                     let index = stack.len() - 1;
    //                     let buffer = &par_buffer;
    //                     s.spawn(move |_| {
    //                         let mut stack = Vec::with_capacity(child.repr_depth() as usize);
    //
    //                         // Fetch child descriptor
    //                         let child_descriptor = child.descriptor();
    //
    //                         // Add merkle offset to the current merkle depth
    //                         let merkle_depth =
    //                             last_merkle_depth + child_descriptor.is_merkle() as u8;
    //
    //                         stack.push(Node {
    //                             references: child.references(),
    //                             descriptor: child_descriptor,
    //                             merkle_depth,
    //                             children: CellRefsBuilder::default(),
    //                         });
    //
    //                         while let Some(last) = stack.last_mut() {
    //                             if let Some(child) = last.references.next() {
    //                                 // Process children if they are left
    //                                 if let Some(last) =
    //                                     process_cell(child, last, self).expect("todo")
    //                                 {
    //                                     stack.push(last);
    //                                     continue;
    //                                 }
    //                             } else if let Some(last) = stack.pop() {
    //                                 // Build a new cell if there are no child nodes left to process
    //                                 let proof_cell = build_cell(last, self).expect("todo");
    //
    //                                 match stack.last_mut() {
    //                                     // Append this cell to the ancestor
    //                                     Some(last) => {
    //                                         _ = last.children.store_reference(proof_cell);
    //                                     }
    //                                     // Or return it as a result (for the root node)
    //                                     None => {
    //                                         buffer.insert(index, proof_cell);
    //                                     }
    //                                 }
    //                             }
    //                         }
    //                     });
    //                 } else if let Some(last) = process_cell(child, last, self)? {
    //                     stack.push(last);
    //                     continue;
    //                 }
    //             } else if let Some(last) = stack.pop() {
    //                 // Build a new cell if there are no child nodes left to process
    //                 let proof_cell = build_cell(last, self)?;
    //
    //                 match stack.last_mut() {
    //                     // Append this cell to the ancestor
    //                     Some(last) => {
    //                         _ = last.children.store_reference(proof_cell);
    //                     }
    //                     // Or return it as a result (for the root node)
    //                     None => return Ok(proof_cell),
    //                 }
    //             }
    //         }
    //
    //         Err(Error::EmptyProof)
    //     })
    // }
}

#[cold]
fn make_pruned_branch_cold(
    cell: &DynCell,
    merkle_depth: u8,
    context: &dyn CellContext,
) -> Result<Cell, Error> {
    make_pruned_branch(cell, merkle_depth, context)
}
