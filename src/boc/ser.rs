use std::collections::HashMap;
use std::hash::BuildHasher;

use super::BocTag;
use crate::cell::{Cell, CellDescriptor, CellFamily, CellHash};

/// Intermediate BOC serializer state.
pub struct BocHeader<'a, C, S = ahash::RandomState> {
    root_rev_indices: Vec<u32>,
    rev_indices: HashMap<CellHash, u32, S>,
    rev_cells: Vec<&'a dyn Cell<C>>,
    total_data_size: u64,
    reference_count: u64,
    cell_count: u32,
    without_hashes: bool,
    include_crc: bool,
}

impl<'a, C: CellFamily, S> BocHeader<'a, C, S>
where
    S: BuildHasher + Default,
{
    /// Creates an intermediate BOC serializer state with a single root.
    pub fn new(root: &'a dyn Cell<C>) -> Self {
        let mut res = Self {
            root_rev_indices: Default::default(),
            rev_indices: Default::default(),
            rev_cells: Default::default(),
            total_data_size: 0,
            reference_count: 0,
            cell_count: 0,
            without_hashes: false,
            include_crc: false,
        };
        res.add_root(root);
        res
    }
}

impl<'a, C: CellFamily, S> BocHeader<'a, C, S>
where
    S: BuildHasher,
{
    /// Adds an additional root to the state.
    pub fn add_root(&mut self, root: &'a dyn Cell<C>) {
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
    pub fn encode(self, target: &mut Vec<u8>) {
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

        for rev_index in self.root_rev_indices {
            let root_index = self.cell_count - rev_index - 1;
            target.extend_from_slice(&root_index.to_be_bytes()[4 - ref_size..]);
        }

        for cell in self.rev_cells.into_iter().rev() {
            let mut descriptor = cell.descriptor();
            descriptor.d1 &= !(u8::from(self.without_hashes) * CellDescriptor::STORE_HASHES_MASK);
            target.extend_from_slice(&[descriptor.d1, descriptor.d2]);
            if descriptor.store_hashes() {
                let hash_count = descriptor.level_mask().level() + 1;
                for level in 0..hash_count {
                    target.extend_from_slice(cell.hash(level));
                }
                for level in 0..hash_count {
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

    fn fill(&mut self, root: &'a dyn Cell<C>) -> u32 {
        if let Some(index) = self.rev_indices.get(root.repr_hash()) {
            return *index;
        }

        for child in root.references() {
            self.fill_iter(child);
        }

        let index = self.cell_count;
        self.rev_indices.insert(*root.repr_hash(), index);
        self.rev_cells.push(root);

        let descriptor = root.descriptor();
        self.total_data_size += descriptor.byte_len_full(self.without_hashes);
        self.reference_count += descriptor.reference_count() as u64;
        self.cell_count += 1;

        index
    }

    // NOTE: Duplicate iteration method to reduce operations per child
    fn fill_iter(&mut self, cell: &'a dyn Cell<C>) {
        if self.rev_indices.contains_key(cell.repr_hash()) {
            return;
        }

        for child in cell.references() {
            self.fill_iter(child);
        }

        self.rev_indices.insert(*cell.repr_hash(), self.cell_count);
        self.rev_cells.push(cell);

        let descriptor = cell.descriptor();
        self.total_data_size += descriptor.byte_len_full(self.without_hashes);
        self.reference_count += descriptor.reference_count() as u64;
        self.cell_count += 1;
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

fn number_of_bytes_to_fit(l: u64) -> usize {
    (8 - l.leading_zeros() / 8) as usize
}
