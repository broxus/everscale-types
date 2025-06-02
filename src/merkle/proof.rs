use std::collections::HashMap;
use std::hash::BuildHasher;

#[cfg(feature = "rayon")]
use dashmap::DashMap;

use super::{make_pruned_branch, FilterAction, MerkleFilter};
use crate::cell::*;
use crate::error::Error;
#[cfg(feature = "rayon")]
use crate::merkle::utils::CondVar;
use crate::util::unlikely;
#[cfg(feature = "rayon")]
use crate::util::ArrayVec;

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
    F: MerkleFilter,
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
    pub fn build_ext(self, context: &dyn CellContext) -> Result<MerkleProof, Error> {
        let root = self.root;
        let cell = ok!(self.build_raw_ext(context));
        Ok(MerkleProof {
            hash: *root.repr_hash(),
            depth: root.repr_depth(),
            cell,
        })
    }

    /// Builds a Merkle proof child cell using the specified cell context.
    pub fn build_raw_ext(self, context: &dyn CellContext) -> Result<Cell, Error> {
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
}

#[cfg(feature = "rayon")]
impl<'a, F> MerkleProofBuilder<'a, F>
where
    F: MerkleFilter + Send + Sync,
{
    /// Multithread build a Merkle proof using the specified cell context
    /// and set of cells which handle in parallel.
    pub fn rayon_build_ext(
        self,
        context: &(dyn CellContext + Send + Sync),
        split_at: ahash::HashSet<HashBytes>,
    ) -> Result<MerkleProof, Error> {
        let root = self.root;
        let cell = ok!(self.rayon_build_raw_ext(context, split_at));
        Ok(MerkleProof {
            hash: *root.repr_hash(),
            depth: root.repr_depth(),
            cell,
        })
    }

    /// Multithread build a Merkle proof child cell using the specified cell context.
    pub fn rayon_build_raw_ext(
        self,
        context: &(dyn CellContext + Send + Sync),
        split_at: ahash::HashSet<HashBytes>,
    ) -> Result<Cell, Error> {
        RayonBuilderImpl::<ahash::RandomState> {
            root: self.root,
            filter: &self.filter,
            cells: Default::default(),
            pruned_branches: None,
            context,
            split_at,
            allow_different_root: self.allow_different_root,
            prune_big_cells: self.prune_big_cells,
        }
        .build()
    }
}

impl<F> MerkleProofBuilder<'_, F>
where
    F: MerkleFilter,
{
    /// Builds a Merkle proof using an empty cell context.
    pub fn build(self) -> Result<MerkleProof, Error> {
        self.build_ext(Cell::empty_context())
    }
}

#[cfg(feature = "rayon")]
impl<F> MerkleProofBuilder<'_, F>
where
    F: MerkleFilter + Send + Sync,
{
    /// Multithreaded build a Merkle proof using an empty cell context.
    #[cfg(feature = "rayon")]
    pub fn rayon_build(self, split_at: ahash::HashSet<HashBytes>) -> Result<MerkleProof, Error> {
        self.rayon_build_ext(Cell::empty_context(), split_at)
    }
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
    F: MerkleFilter,
{
    /// Builds a Merkle proof child cell using the specified cell context.
    pub fn build_raw_ext<'c: 'a>(
        self,
        context: &'c dyn CellContext,
    ) -> Result<(Cell, ahash::HashMap<&'a HashBytes, bool>), Error> {
        let mut pruned_branches = Default::default();
        let mut builder = BuilderImpl {
            root: self.root,
            filter: &self.filter,
            cells: Default::default(),
            pruned_branches: Some(&mut pruned_branches),
            context,
            allow_different_root: self.allow_different_root,
            prune_big_cells: self.prune_big_cells,
        };
        let cell = ok!(builder.build());
        Ok((cell, pruned_branches))
    }
}

impl<'a, F> MerkleProofExtBuilder<'a, F>
where
    F: MerkleFilter + Send + Sync,
{
    /// Multithreaded build a Merkle proof child cell using the specified cell context.
    #[cfg(feature = "rayon")]
    pub fn rayon_build_raw_ext<'c: 'a>(
        self,
        context: &'c (dyn CellContext + Send + Sync),
        split_at: ahash::HashSet<HashBytes>,
    ) -> Result<(Cell, DashMap<&'a HashBytes, bool>), Error> {
        let pruned_branches = Default::default();
        let builder = RayonBuilderImpl {
            root: self.root,
            filter: &self.filter,
            cells: Default::default(),
            pruned_branches: Some(&pruned_branches),
            context,
            split_at,
            allow_different_root: self.allow_different_root,
            prune_big_cells: self.prune_big_cells,
        };
        let cell = ok!(builder.build());
        Ok((cell, pruned_branches))
    }
}

struct BuilderImpl<'a, 'b, 'c: 'a, S = ahash::RandomState> {
    root: &'a DynCell,
    filter: &'b dyn MerkleFilter,
    cells: HashMap<&'a HashBytes, Cell, S>,
    pruned_branches: Option<&'b mut HashMap<&'a HashBytes, bool, S>>,
    context: &'c dyn CellContext,
    allow_different_root: bool,
    prune_big_cells: bool,
}

impl<S> BuilderImpl<'_, '_, '_, S>
where
    S: BuildHasher + Default,
{
    fn build(&mut self) -> Result<Cell, Error> {
        const PRUNED_BITS_THRESHOLD: u16 = 288;

        struct Node<'a> {
            references: RefsIter<'a>,
            descriptor: CellDescriptor,
            merkle_depth: u8,
            children: CellRefsBuilder,
        }

        if !self.allow_different_root
            && self.filter.check(self.root.repr_hash()) == FilterAction::Skip
        {
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

                // Build the cell
                let mut builder = CellBuilder::new();
                builder.set_exotic(last.descriptor.is_exotic());
                _ = builder.store_cell_data(cell);
                builder.set_references(last.children);
                let proof_cell = ok!(builder.build_ext(self.context));

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

#[cfg(feature = "rayon")]
struct RayonBuilderImpl<'a, 'b, 'c: 'a, S = ahash::RandomState> {
    root: &'a DynCell,
    filter: &'b (dyn MerkleFilter + Send + Sync),
    cells: DashMap<&'a HashBytes, Cell, S>,
    pruned_branches: Option<&'b DashMap<&'a HashBytes, bool, S>>,
    context: &'c (dyn CellContext + Send + Sync),
    split_at: ahash::HashSet<HashBytes>,
    allow_different_root: bool,
    prune_big_cells: bool,
}

#[cfg(feature = "rayon")]
impl<'a, S> RayonBuilderImpl<'a, '_, '_, S>
where
    S: BuildHasher + Default + Clone + Send + Sync,
{
    const PRUNED_BITS_THRESHOLD: u16 = 288;

    fn build(&self) -> Result<Cell, Error> {
        struct Node<'a> {
            references: RefsIter<'a>,
            descriptor: CellDescriptor,
            merkle_depth: u8,
            children: ChildrenBuilder,
        }

        if !self.allow_different_root
            && self.filter.check(self.root.repr_hash()) == FilterAction::Skip
        {
            return Err(Error::EmptyProof);
        }

        let root_cell = rayon::scope(|scope| {
            let mut stack = Vec::with_capacity(self.root.repr_depth() as usize);

            // Push root node
            let root_descriptor = self.root.descriptor();
            stack.push(Node {
                references: self.root.references(),
                descriptor: root_descriptor,
                merkle_depth: root_descriptor.is_merkle() as u8,
                children: Default::default(),
            });

            while let Some(last) = stack.last_mut() {
                if let Some(child) = last.references.next() {
                    // Process children if they are left
                    let child_repr_hash = child.repr_hash();

                    let child = if let Some(child) = self.cells.get(child_repr_hash) {
                        // Reused processed cells
                        ExtCell::Ordinary(child.clone())
                    } else {
                        // Fetch child descriptor
                        let descriptor = child.descriptor();

                        // Check if child is in a tree
                        match self.filter.check(child_repr_hash) {
                            // Included subtrees are used as is
                            FilterAction::IncludeSubtree => ExtCell::Ordinary(
                                last.references.peek_prev_cloned().expect("mut not fail"),
                            ),
                            // Replace all skipped subtrees with pruned branch cells
                            FilterAction::Skip
                                if descriptor.reference_count() > 0
                                    || self.prune_big_cells
                                        && child.bit_len() > Self::PRUNED_BITS_THRESHOLD =>
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
                                ExtCell::Ordinary(child)
                            }
                            // All other cells will be included in a different branch
                            _ => {
                                if !self.split_at.contains(child_repr_hash) {
                                    // Add merkle offset to the current merkle depth
                                    let merkle_depth =
                                        last.merkle_depth + descriptor.is_merkle() as u8;

                                    // Push child node and start processing its references
                                    stack.push(Node {
                                        references: child.references(),
                                        descriptor,
                                        merkle_depth,
                                        children: Default::default(),
                                    });

                                    continue;
                                } else {
                                    let cv =
                                        self.spawn_build_subtree(child, last.merkle_depth, scope);

                                    ExtCell::Channel(cv)
                                }
                            }
                        }
                    };

                    // Add child to the references builder
                    last.children.store_reference(child)?;
                } else if let Some(last) = stack.pop() {
                    // Build a new ExtCell if there are no child nodes left to process

                    let cell = last.references.cell();

                    // Build the cell
                    let mut builder = CellDataBuilder::new();
                    builder.store_cell_data(cell)?;

                    let proof_cell = match last.children {
                        ChildrenBuilder::Ordinary(children) => {
                            let mut builder = CellBuilder::new();
                            builder.set_exotic(last.descriptor.is_exotic());
                            _ = builder.store_cell_data(cell);
                            builder.set_references(children);
                            let proof_cell = ok!(builder.build_ext(self.context));

                            ExtCell::Ordinary(proof_cell)
                        }
                        ChildrenBuilder::Extended(children) => {
                            let mut builder = CellDataBuilder::new();
                            builder.store_cell_data(cell)?;

                            let cell = CellPart {
                                data: builder,
                                is_exotic: last.descriptor.is_exotic(),
                                refs: children.0,
                            };

                            ExtCell::Partial(Box::new(cell))
                        }
                    };

                    match stack.last_mut() {
                        // Append this cell to the ancestor
                        Some(last) => {
                            last.children.store_reference(proof_cell)?;
                        }
                        // Or return it as a result (for the root node)
                        None => return Ok(proof_cell),
                    }
                }
            }

            // Something is wrong if we are here
            Err(Error::EmptyProof)
        })?;

        fn resolve(
            cell: &ExtCell,
            context: &(dyn CellContext + Send + Sync),
        ) -> Result<Cell, Error> {
            match cell {
                ExtCell::Ordinary(cell) => Ok(cell.clone()),
                ExtCell::Channel(rx) => rx.wait().map_err(|_| Error::Cancelled),
                ExtCell::Partial(node) => {
                    let mut refs_builder = CellRefsBuilder::default();

                    for child in node.refs.as_ref() {
                        let cell = resolve(child, context)?;
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
            ExtCell::Ordinary(cell) => Ok(cell),
            ExtCell::Channel(rx) => Ok(rx.wait()?),
            ExtCell::Partial(cell_parts) => resolve(&ExtCell::Partial(cell_parts), self.context),
        }
    }

    fn spawn_build_subtree<'scope>(
        &'scope self,
        child: &'a DynCell,
        parent_merkle_depth: u8,
        scope: &rayon::Scope<'scope>,
    ) -> CondVar<Cell> {
        let condvar = CondVar::new();
        let tx = condvar.clone();

        let cells = &self.cells;
        let filter = self.filter;
        let context = self.context;
        let pruned_branches = self.pruned_branches;
        let prune_big_cells = self.prune_big_cells;

        scope.spawn(move |_| {
            struct Node<'a> {
                references: RefsIter<'a>,
                descriptor: CellDescriptor,
                merkle_depth: u8,
                children: CellRefsBuilder,
            }

            let mut stack = Vec::with_capacity(child.repr_depth() as usize);

            // Fetch child descriptor
            let child_descriptor = child.descriptor();

            // Add merkle offset to the current merkle depth
            let merkle_depth = parent_merkle_depth + child_descriptor.is_merkle() as u8;

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
                    let child = if let Some(child) = cells.get(child_repr_hash) {
                        // Reused processed cells
                        child.clone()
                    } else {
                        // Fetch child descriptor
                        let descriptor = child.descriptor();

                        // Check if child is in a tree
                        match filter.check(child_repr_hash) {
                            // Included subtrees are used as is
                            FilterAction::IncludeSubtree => {
                                last.references.peek_prev_cloned().expect("mut not fail")
                            }
                            // Replace all skipped subtrees with pruned branch cells
                            FilterAction::Skip
                                if descriptor.reference_count() > 0
                                    || prune_big_cells
                                        && child.bit_len() > Self::PRUNED_BITS_THRESHOLD =>
                            {
                                // Create pruned branch
                                let child =
                                    make_pruned_branch_cold(child, last.merkle_depth, context)
                                        .expect("failed to create pruned branch");

                                // Insert pruned branch for the current cell
                                if let Some(pruned_branch) = pruned_branches {
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

                    // Build the cell
                    let mut builder = CellBuilder::new();
                    builder.set_exotic(last.descriptor.is_exotic());
                    _ = builder.store_cell_data(cell);
                    builder.set_references(last.children);
                    let proof_cell = builder.build_ext(context).expect("failed to build ExtCell");

                    // Save this cell as processed cell
                    cells.insert(cell.repr_hash(), proof_cell.clone());

                    match stack.last_mut() {
                        // Append this cell to the ancestor
                        Some(last) => {
                            _ = last.children.store_reference(proof_cell);
                        }
                        // Or return it as a result (for the root node)
                        None => tx.send(proof_cell).expect("failed to send proof_cell"),
                    }
                }
            }
        });

        condvar
    }
}

#[cold]
fn make_pruned_branch_cold(
    cell: &DynCell,
    merkle_depth: u8,
    context: &dyn CellContext,
) -> Result<Cell, Error> {
    make_pruned_branch(cell, merkle_depth, context)
}

#[cfg(feature = "rayon")]
enum ExtCell {
    Ordinary(Cell),
    Partial(Box<CellPart>),
    Channel(CondVar<Cell>),
}

#[cfg(feature = "rayon")]
struct CellPart {
    pub data: CellDataBuilder,
    pub is_exotic: bool,
    pub refs: ArrayVec<ExtCell, MAX_REF_COUNT>,
}

/// Builder for constructing `ExtCell` references array.
#[cfg(feature = "rayon")]
#[derive(Default)]
#[repr(transparent)]
struct ExtCellRefsBuilder(ArrayVec<ExtCell, MAX_REF_COUNT>);

#[cfg(feature = "rayon")]
impl ExtCellRefsBuilder {
    /// Tries to store a child in the cell,
    /// returning `false` if there is not enough remaining capacity.
    pub fn store_reference(&mut self, cell: ExtCell) -> Result<(), Error> {
        if self.0.len() < MAX_REF_COUNT {
            // SAFETY: reference count is in the valid range
            unsafe { self.0.push(cell) }
            Ok(())
        } else {
            Err(Error::CellOverflow)
        }
    }
}

#[cfg(feature = "rayon")]
enum ChildrenBuilder {
    Ordinary(CellRefsBuilder),
    Extended(ExtCellRefsBuilder),
}

#[cfg(feature = "rayon")]
impl ChildrenBuilder {
    fn store_reference(&mut self, raw_cell: ExtCell) -> Result<(), Error> {
        match (&raw_cell, &mut *self) {
            (ExtCell::Ordinary(cell), ChildrenBuilder::Ordinary(builder)) => {
                builder.store_reference(cell.clone())?;
            }
            (ExtCell::Ordinary(_), ChildrenBuilder::Extended(builder)) => {
                builder.store_reference(raw_cell)?;
            }
            (ExtCell::Partial(_) | ExtCell::Channel(_), ChildrenBuilder::Extended(builder)) => {
                builder.store_reference(raw_cell)?;
            }

            (ExtCell::Partial(_) | ExtCell::Channel(_), ChildrenBuilder::Ordinary(refs)) => {
                let mut new_builder = ExtCellRefsBuilder::default();

                for cell in refs.0.as_ref() {
                    new_builder.store_reference(ExtCell::Ordinary(cell.clone()))?;
                }

                new_builder.store_reference(raw_cell)?;

                *self = ChildrenBuilder::Extended(new_builder);
            }
        }

        Ok(())
    }
}

#[cfg(feature = "rayon")]
impl Default for ChildrenBuilder {
    fn default() -> Self {
        Self::Ordinary(Default::default())
    }
}
