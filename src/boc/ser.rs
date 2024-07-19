use std::collections::HashMap;
use std::hash::BuildHasher;

use super::BocTag;
use crate::cell::{CellDescriptor, DynCell, HashBytes};

/// Intermediate BOC serializer state.
pub struct BocHeader<'a, S = ahash::RandomState> {
    root_rev_indices: Vec<u32>,
    rev_indices: HashMap<&'a HashBytes, u32, S>,
    rev_cells: Vec<&'a DynCell>,
    total_data_size: u64,
    reference_count: u64,
    cell_count: u32,
    without_hashes: bool,
    include_crc: bool,
}

impl<S: BuildHasher + Default> Default for BocHeader<'_, S> {
    #[inline]
    fn default() -> Self {
        Self {
            root_rev_indices: Default::default(),
            rev_indices: Default::default(),
            rev_cells: Default::default(),
            total_data_size: 0,
            reference_count: 0,
            cell_count: 0,
            without_hashes: false,
            include_crc: false,
        }
    }
}

impl<'a, S> BocHeader<'a, S>
where
    S: BuildHasher + Default,
{
    /// Creates an intermediate BOC serializer state with a single root.
    pub fn with_root(root: &'a DynCell) -> Self {
        let mut res = Self::default();
        res.add_root(root);
        res
    }

    /// Creates an empty intermediate BOC serializer state.
    /// Reserves space for the specified number of cells.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            root_rev_indices: Default::default(),
            rev_indices: HashMap::with_capacity_and_hasher(capacity, S::default()),
            rev_cells: Vec::with_capacity(capacity),
            total_data_size: 0,
            reference_count: 0,
            cell_count: 0,
            without_hashes: false,
            include_crc: false,
        }
    }

    /// Creates an intermediate BOC serializer state with a single root.
    /// Reserves space for the specified number of cells.
    pub fn with_capacity_and_root(capacity: usize, root: &'a DynCell) -> Self {
        let mut res = Self::with_capacity(capacity);
        res.add_root(root);
        res
    }
}

impl<'a, S> BocHeader<'a, S>
where
    S: BuildHasher,
{
    /// Clears the header, removing all cells. Keeps the allocated memory for reuse.
    pub fn clear(&mut self) {
        self.root_rev_indices.clear();
        self.rev_indices.clear();
        self.rev_cells.clear();
        self.total_data_size = 0;
        self.reference_count = 0;
        self.cell_count = 0;
    }

    /// Adds an additional root to the state.
    pub fn add_root(&mut self, root: &'a DynCell) {
        let root_rev_index = self.fill(root);
        self.root_rev_indices.push(root_rev_index);
    }

    /// Includes CRC bytes in the encoded BOC.
    #[inline]
    pub fn with_crc(mut self, include_ctc: bool) -> Self {
        self.include_crc = include_ctc;
        self
    }

    /// Prevents hashes from being stored in the encoded BOC.
    ///
    /// (overwrites descriptor flag `store_hashes` during serialization).
    #[inline]
    pub fn without_hashes(mut self, without_hashes: bool) -> Self {
        self.without_hashes = without_hashes;
        self
    }

    /// Encodes cell trees into bytes.
    pub fn encode(&self, target: &mut Vec<u8>) {
        let target_len_before = target.len();
        let header = self.encode_header(target);
        self.encode_cells_chunk(&self.rev_cells, header.ref_size, target);
        self.encode_crc(target_len_before, target);

        debug_assert_eq!(
            target.len() as u64,
            target_len_before as u64 + header.total_size
        );
    }

    /// Encodes cell trees into bytes.
    /// Uses `rayon` under the hood.
    #[cfg(feature = "rayon")]
    pub fn encode_rayon(&self, target: &mut Vec<u8>)
    where
        S: Send + Sync,
    {
        use rayon::iter::{IndexedParallelIterator, ParallelIterator};
        use rayon::slice::ParallelSlice;

        const CELLS_CHUNK_SIZE: usize = 5_000;

        let target_len_before = target.len();
        let header = self.encode_header(target);

        if self.rev_cells.len() < CELLS_CHUNK_SIZE * 2 {
            self.encode_cells_chunk(&self.rev_cells, header.ref_size, target);
        } else {
            let mut chunks = Vec::new();
            self.rev_cells
                .par_rchunks(CELLS_CHUNK_SIZE)
                .map(|chunk| {
                    let mut target = Vec::with_capacity(chunk.len() * 256);
                    self.encode_cells_chunk(chunk, header.ref_size, &mut target);
                    target
                })
                .collect_into_vec(&mut chunks);
            for chunk in chunks {
                target.extend_from_slice(&chunk);
            }
        }

        self.encode_crc(target_len_before, target);

        debug_assert_eq!(
            target.len() as u64,
            target_len_before as u64 + header.total_size
        );
    }

    #[inline]
    fn encode_header(&self, target: &mut Vec<u8>) -> EncodedHeader {
        let root_count = self.root_rev_indices.len();

        let ref_size = number_of_bytes_to_fit(self.cell_count as u64);
        // NOTE: `ref_size` will be in range 1..=4 because `self.cell_count`
        // is `u32`, and there is at least one cell (see Self::new)
        debug_assert!((1..=4).contains(&ref_size));

        let total_cells_size: u64 = self.total_data_size
            + (self.cell_count as u64 * 2) // all descriptor bytes
            + (ref_size as u64 * self.reference_count);
        let offset_size = number_of_bytes_to_fit(total_cells_size);

        // NOTE: `offset_size` will be in range 1..=8 because `self.cell_count`
        // is at least 1, and `total_cells_size` is `u64`
        debug_assert!((1..=8).contains(&offset_size));

        let flags = (ref_size as u8) | (u8::from(self.include_crc) * 0b0100_0000);

        // 4 bytes - BOC tag
        // 1 byte - flags
        // 1 byte - offset size
        // {ref_size} - cell count
        // {ref_size} - root count
        // {ref_size} - absent cell count
        // {offset_size} - total cells size
        // root_count * {ref_size} - root indices
        // {total_cells_size} - cells
        // include_crc * 4 - optional CRC32
        let total_size = 4
            + 2
            + (ref_size as u64) * (3 + root_count as u64)
            + (offset_size as u64)
            + total_cells_size
            + u64::from(self.include_crc) * 4;
        target.reserve(total_size as usize);

        target.extend_from_slice(&BocTag::GENERIC);
        target.extend_from_slice(&[flags, offset_size as u8]);
        target.extend_from_slice(&self.cell_count.to_be_bytes()[4 - ref_size..]);
        target.extend_from_slice(&(root_count as u32).to_be_bytes()[4 - ref_size..]);
        target.extend_from_slice(&[0; 4][4 - ref_size..]);
        target.extend_from_slice(&total_cells_size.to_be_bytes()[8 - offset_size..]);

        for rev_index in &self.root_rev_indices {
            let root_index = self.cell_count - rev_index - 1;
            target.extend_from_slice(&root_index.to_be_bytes()[4 - ref_size..]);
        }

        EncodedHeader {
            ref_size,
            total_size,
        }
    }

    #[inline]
    fn encode_cells_chunk(&self, chunk: &[&DynCell], ref_size: usize, target: &mut Vec<u8>) {
        let descriptor_mask = !(u8::from(self.without_hashes) * CellDescriptor::STORE_HASHES_MASK);

        for cell in chunk.iter().rev() {
            let mut descriptor = cell.descriptor();
            descriptor.d1 &= descriptor_mask;
            target.extend_from_slice(&[descriptor.d1, descriptor.d2]);
            if descriptor.store_hashes() {
                let level_mask = descriptor.level_mask();
                for level in level_mask {
                    target.extend_from_slice(cell.hash(level).as_ref());
                }
                for level in level_mask {
                    target.extend_from_slice(&cell.depth(level).to_be_bytes());
                }
            }
            target.extend_from_slice(cell.data());
            for child in cell.references() {
                if let Some(rev_index) = self.rev_indices.get(child.repr_hash()) {
                    let rev_index = self.cell_count - *rev_index - 1;
                    target.extend_from_slice(&rev_index.to_be_bytes()[4 - ref_size..]);
                } else {
                    debug_assert!(false, "child not found");
                }
            }
        }
    }

    #[inline]
    fn encode_crc(&self, target_len_before: usize, target: &mut Vec<u8>) {
        if self.include_crc {
            let target_len_after = target.len();
            debug_assert!(target_len_before < target_len_after);

            let crc = crc32c::crc32c(&target[target_len_before..target_len_after]);
            target.extend_from_slice(&crc.to_le_bytes());
        }
    }

    fn fill(&mut self, root: &'a DynCell) -> u32 {
        const SAFE_DEPTH: u16 = 128;

        if let Some(index) = self.rev_indices.get(root.repr_hash()) {
            return *index;
        }

        let repr_depth = root.repr_depth();
        if repr_depth <= SAFE_DEPTH {
            self.fill_recursive(root);
        } else {
            self.fill_deep(root, repr_depth);
        }

        debug_assert!(self.cell_count > 0);
        self.cell_count - 1
    }

    fn fill_recursive(&mut self, cell: &'a DynCell) {
        for child in cell.references() {
            if !self.rev_indices.contains_key(child.repr_hash()) {
                self.fill_recursive(child);
            }
        }

        self.rev_indices.insert(cell.repr_hash(), self.cell_count);
        self.rev_cells.push(cell);

        let descriptor = cell.descriptor();
        self.total_data_size += descriptor.byte_len_full(self.without_hashes);
        self.reference_count += descriptor.reference_count() as u64;
        self.cell_count += 1;
    }

    #[cold]
    fn fill_deep(&mut self, root: &'a DynCell, repr_depth: u16) {
        const MAX_DEFAULT_CAPACITY: u16 = 256;

        let mut stack = Vec::with_capacity(repr_depth.min(MAX_DEFAULT_CAPACITY) as usize);
        stack.push(root.references());

        while let Some(children) = stack.last_mut() {
            if let Some(cell) = children.next() {
                if !self.rev_indices.contains_key(cell.repr_hash()) {
                    stack.push(cell.references());
                }
            } else {
                let cell = children.cell();

                self.rev_indices.insert(cell.repr_hash(), self.cell_count);
                self.rev_cells.push(cell);

                let descriptor = cell.descriptor();
                self.total_data_size += descriptor.byte_len_full(self.without_hashes);
                self.reference_count += descriptor.reference_count() as u64;
                self.cell_count += 1;

                stack.pop();
            }
        }
    }
}

impl CellDescriptor {
    fn byte_len_full(self, without_hashes: bool) -> u64 {
        let mut byte_len = self.byte_len() as u64;
        if !without_hashes && self.store_hashes() {
            byte_len += (self.level_mask().level() + 1) as u64 * (32 + 2);
        }
        byte_len
    }
}

#[derive(Copy, Clone)]
struct EncodedHeader {
    ref_size: usize,
    total_size: u64,
}

fn number_of_bytes_to_fit(l: u64) -> usize {
    (8 - l.leading_zeros() / 8) as usize
}
