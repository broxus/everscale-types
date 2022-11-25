use std::ops::Deref;

use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use super::BocTag;
use crate::cell::descriptor::Descriptor;
use crate::cell::level_mask::LevelMask;
use crate::cell::{ArcCell, Cell, CellFinalizer, CellTreeStats, FinalizerContext};
use crate::error::{invalid_data, unexpected_eof, unsupported};
use crate::util::{unlikely, ArrayVec};

#[derive(Debug, Default, Clone)]
pub struct Options {
    /// The minimum allowed root count
    pub min_roots: Option<usize>,
    /// The maximum allowed root count
    pub max_roots: Option<usize>,
}

/// Parsed BOC header
pub struct BocHeader<'a> {
    ref_size: usize,
    cells: SmallVec<[&'a [u8]; CELLS_ON_STACK]>,
    roots: SmallVec<[u32; ROOTS_ON_STACK]>,
}

impl<'a> BocHeader<'a> {
    pub fn deserialize(data: &'a [u8], options: &Options) -> std::io::Result<Self> {
        let mut reader = BocReader::new(data.len());

        // 4 bytes - tag
        // 1 byte - flags
        // 1 byte - offset size
        if unlikely(!reader.require(6)) {
            return Err(unexpected_eof("invalid BOC header"));
        }
        debug_assert!(data.len() >= 6);

        let [flags, offset_size] = unsafe { *(data.as_ptr().add(4) as *const [u8; 2]) };

        let has_index;
        let has_crc;
        let has_cache_bits;
        let ref_size;
        let supports_multiple_roots;

        match BocTag::from_bytes(data[0..4].try_into().unwrap()) {
            Some(BocTag::Indexed) => {
                has_index = false;
                has_crc = false;
                has_cache_bits = false;
                ref_size = flags as usize;
                supports_multiple_roots = false;
            }
            Some(BocTag::IndexedCrc32) => {
                has_index = true;
                has_crc = true;
                has_cache_bits = false;
                ref_size = flags as usize;
                supports_multiple_roots = false;
            }
            Some(BocTag::Generic) => {
                has_index = flags & 0b1000_0000 != 0;
                has_crc = flags & 0b0100_0000 != 0;
                has_cache_bits = flags & 0b0010_0000 != 0;
                ref_size = (flags & 0b0000_0111) as usize;
                supports_multiple_roots = true;
            }
            None => return Err(invalid_data("unknown BOC tag")),
        }

        if unlikely(has_cache_bits && !has_index) {
            return Err(invalid_data("invalid header"));
        }
        if unlikely(ref_size == 0 || ref_size > std::mem::size_of::<u32>()) {
            return Err(invalid_data("ref index does not fit in `u32` type"));
        }
        debug_assert!((1..=4).contains(&ref_size));

        let offset_size = offset_size as usize;
        if unlikely(offset_size == 0 || offset_size > std::mem::size_of::<usize>()) {
            return Err(invalid_data("cell offset does not fit in `usize` type"));
        }
        debug_assert!((1..=8).contains(&offset_size));

        reader.advance(6);

        // {ref_size} bytes - cell count
        // {ref_size} bytes - root count
        // {ref_size} bytes - absent cell count
        // {offset_size} bytes - total cells size
        if unlikely(!reader.require(ref_size * 3 + offset_size)) {
            return Err(invalid_data("invalid BOC header"));
        }
        debug_assert!(data.len() >= (6 + ref_size * 3 + offset_size));

        // SAFETY: we have already requested more than {ref_size}*3
        // and {ref_size} is in range 1..=4
        let (cell_count, root_count, absent_count) = unsafe {
            (
                reader.read_next_be_uint_fast(data, ref_size),
                reader.read_next_be_uint_fast(data, ref_size),
                reader.read_next_be_uint_fast(data, ref_size),
            )
        };

        // Validate root or absent cells
        if unlikely(root_count == 0) {
            return Err(invalid_data("root cells not found"));
        }
        if unlikely(!supports_multiple_roots && root_count > 1) {
            return Err(invalid_data("unexpected multiple roots"));
        }
        if unlikely(root_count.saturating_add(absent_count) > cell_count) {
            return Err(invalid_data("too many root or absent cells"));
        }
        if unlikely(absent_count > 0) {
            return Err(unsupported("absent cells are not supported"));
        }
        if let Some(min_roots) = options.min_roots {
            if unlikely(root_count < min_roots) {
                return Err(invalid_data("too few root cells"));
            }
        }
        if unlikely(root_count > options.max_roots.unwrap_or(MAX_ROOTS)) {
            return Err(invalid_data("more root cells than expected"));
        }
        debug_assert!(absent_count == 0 && (1..=MAX_ROOTS).contains(&root_count));

        // SAFETY: we have already requested at least {ref_size}*3+{offset_size}
        // and {ref_size} is in range 1..=8
        let total_cells_size = unsafe { reader.read_next_be_uint_full(data, offset_size) };

        const MIN_CELL_SIZE: u64 = 2; // [d1, d2]

        // NOTE: `cell_count` is guaranteed to be in range of `u32`, so
        // `u32::MAX * (2 + 4)` fits into u64 and doesn't require saturating/checked mul,
        // `root_count` <= `cell_count` so this expression doesn't overflow
        let min_total_cell_size = (cell_count as u64) * (MIN_CELL_SIZE + ref_size as u64)
            - (root_count * ref_size) as u64;
        if unlikely(total_cells_size < min_total_cell_size) {
            return Err(invalid_data("invalid total cells size"));
        }

        // NOTE: `cell_count` is guaranteed to be in range of `u32`, so
        // `u32::MAX * 282` fits into u64 and doesn't require saturating/checked mul
        // 2 bytes - descriptor
        // 4 * (2 + 32) - inline hashes and depths if presented
        // 128 - max data length
        // 4*{ref_size} - max references
        let max_cell_size = 2 + 4 * (2 + 32) + 128 + 4 * ref_size as u64; // ~282 bytes
        if unlikely(total_cells_size > (cell_count as u64) * max_cell_size) {
            return Err(invalid_data("invalid total cells size"));
        }

        // NOTE: `root_count` is in range ..=u32::MAX and `ref_size` is in range 1..=4
        if unlikely(!reader.require(root_count * ref_size)) {
            return Err(unexpected_eof("expected list of roots"));
        }
        debug_assert!(data.len() >= (6 + ref_size * 3 + offset_size + root_count * ref_size));

        let roots = SmallVec::with_capacity(root_count);
        for _ in 0..root_count {
            // SAFETY: we have already requested for {root_count}*{ref_size}
            let root_index = unsafe { reader.read_next_be_uint_fast(data, ref_size) };
            if unlikely(root_index >= cell_count) {
                return Err(invalid_data("root index out of bounds"));
            }
            roots.push(root_index as u32);
        }

        // NOTE: `cell_count` is in range ..=u32::MAX, `offset_size` is in range 1..=8
        let index_size = has_index as u64 * cell_count as u64 * offset_size as u64;
        if unlikely(!reader.require((index_size + total_cells_size + has_crc as u64 * 4) as usize))
        {
            return Err(unexpected_eof("missing the rest of the BOC"));
        }

        if has_index {
            reader.advance(cell_count * offset_size);
        }

        let mut cells = SmallVec::with_capacity(cell_count);

        let data_ptr = data.as_ptr();
        for _ in 0..cell_count {
            if unlikely(!reader.require(2)) {
                return Err(unexpected_eof("expected descriptor bytes"));
            }

            // SAFETY: there are manual bounds checks for bytes offset
            let start_ptr = unsafe { data_ptr.add(reader.offset) };

            // SAFETY: we have already checked the reader has 2 bytes
            let descriptor = unsafe { reader.read_cell_descriptor(data) };
            if unlikely(descriptor.is_absent()) {
                return Err(unsupported("absent cells are not supported"));
            }

            // 0b11111111 -> 0b01111111 + 1 = 0b10000000 = byte len 128, max bit len = 1023
            // 0b11111110 -> 0b01111111 = byte len 127, bit len = 1016
            let data_len = descriptor.byte_len() as usize;
            let ref_count = descriptor.reference_count() as usize;
            if unlikely(ref_count > 4) {
                return Err(invalid_data("cell ref count not in range 0..=4"));
            }

            // TODO: handle store hashes (skipped by now)
            if unlikely(descriptor.store_hashes()) {
                return Err(unsupported("store hashes flags is not supported"));
            }

            let total_len = 2 + data_len + ref_count * ref_size;
            if unlikely(!reader.require(total_len)) {
                return Err(unexpected_eof("expected cell data and references"));
            }

            if data_len > 0 && !descriptor.is_aligned() {
                // SAFETY: we have already requested 2+{data_len} bytes
                let byte_with_tag = unsafe { reader.read_cell_tag(data, data_len) };
                if unlikely(byte_with_tag & 0x7f == 0) {
                    return Err(invalid_data("unnormalized cell"));
                }
            }
            reader.advance(total_len);

            // SAFETY: We have already requested {total_len} bytes
            let cell = unsafe { std::slice::from_raw_parts(start_ptr, total_len) };
            cells.push(cell);
        }

        Ok(Self {
            ref_size,
            cells,
            roots,
        })
    }

    pub fn finalize<R, F>(&self, mut finalizer: F) -> std::io::Result<FxHashMap<u32, R>>
    where
        R: AsRef<dyn Cell> + Clone,
        F: CellFinalizer<R>,
    {
        let ref_size = self.ref_size;
        let cell_count = self.cells.len();

        let mut res = FxHashMap::<u32, R>::with_capacity_and_hasher(cell_count, Default::default());

        let mut index = cell_count;
        for cell in self.cells().iter().rev() {
            index -= 1;

            // SAFETY: cell data structure was already validated before
            unsafe {
                let cell_ptr = cell.as_ptr();

                let descriptor = Descriptor::new(*(cell_ptr as *const [u8; 2]));
                let byte_len = descriptor.byte_len() as usize;

                let mut data_ptr = cell_ptr.add(2);
                let data = std::slice::from_raw_parts(data_ptr, byte_len);
                data_ptr.add(byte_len);

                let bit_len = if descriptor.is_aligned() {
                    (byte_len * 8) as u16
                } else if let Some(data) = data.last() {
                    8 - data.trailing_zeros() as u16
                } else {
                    0
                };

                let mut refs = ArrayVec::<R, 4>::default();
                let mut children_mask = LevelMask::EMPTY;
                let mut stats = CellTreeStats {
                    bit_count: bit_len as u64,
                    cell_count: 1,
                };

                for _ in 0..descriptor.reference_count() {
                    let child_index = read_be_uint_fast(data_ptr, 0, ref_size);
                    let child = match res.get(&child_index) {
                        Some(child) => child.clone(),
                        None => return Err(invalid_data("invalid children order")),
                    };

                    {
                        let child = child.as_ref();
                        children_mask |= child.descriptor().level_mask();
                        stats += child.stats();
                    }
                    refs.push(child);

                    data_ptr = data_ptr.add(ref_size);
                }

                let ctx = FinalizerContext {
                    stats,
                    bit_len,
                    descriptor,
                    children_mask,
                    references: refs.into_inner(),
                    data,
                };
                let cell = ok!(finalizer.finalize_cell(ctx));
                res.insert(index as u32, cell);
            }
        }

        Ok(res)
    }

    /// Cell index size in bytes. Guaranteed to be 4 at max
    pub fn ref_size(&self) -> usize {
        self.ref_size
    }

    /// Slices of the unique cells
    pub fn cells(&self) -> &[&'a [u8]] {
        &self.cells
    }

    /// Root indices
    pub fn roots(&self) -> &[u32] {
        &self.roots
    }
}

/// Wrapper around indexed bytes slice access
/// to eliminate bounds check
struct BocReader {
    len: usize,
    offset: usize,
}

impl BocReader {
    #[inline(always)]
    const fn new(len: usize) -> Self {
        Self { len, offset: 0 }
    }

    #[inline(always)]
    const fn require(&self, len: usize) -> bool {
        self.offset + len <= self.len
    }

    #[inline(always)]
    fn advance(&mut self, bytes: usize) {
        self.offset += bytes;
    }

    /// # Safety
    ///
    /// - size must be in range 1..=4
    /// - data must be at least `self.offset + size` bytes long
    #[inline(always)]
    unsafe fn read_next_be_uint_fast(&mut self, data: &[u8], size: usize) -> usize {
        let res = read_be_uint_fast(data.as_ptr(), self.offset, size) as usize;
        self.advance(size);
        res
    }

    /// # Safety
    ///
    /// - size must be in range 1..=8
    /// - data must be at least `self.offset + size` bytes long
    #[inline(always)]
    unsafe fn read_next_be_uint_full(&mut self, data: &[u8], size: usize) -> u64 {
        let res = match size {
            1..=4 => read_be_uint_fast(data.as_ptr(), self.offset, size) as u64,
            5..=8 => {
                let mut bytes = [0u8; 8];
                std::ptr::copy_nonoverlapping(
                    data.as_ptr().add(self.offset),
                    bytes.as_mut_ptr().add(8 - size),
                    size,
                );
                u64::from_be_bytes(bytes)
            }
            _ => std::hint::unreachable_unchecked(),
        };
        self.advance(size);
        res
    }

    #[inline(always)]
    unsafe fn read_cell_descriptor(&self, data: &[u8]) -> Descriptor {
        const _: () = assert!(std::mem::size_of::<Descriptor>() == 2);
        *(data.as_ptr().add(self.offset) as *const Descriptor)
    }

    #[inline(always)]
    unsafe fn read_cell_tag(&self, data: &[u8], data_len: usize) -> u8 {
        *data.as_ptr().add(self.offset + 2 + data_len - 1)
    }
}

impl Deref for BocReader {
    type Target = usize;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.offset
    }
}

#[inline(always)]
unsafe fn read_be_uint_fast(data_ptr: *const u8, offset: usize, size: usize) -> u32 {
    match size {
        1 => *data_ptr as u32,
        2 => u16::from_be_bytes(*(data_ptr.add(offset) as *const [u8; 2])) as u32,
        3 => {
            let mut bytes = [0u8; 4];
            std::ptr::copy_nonoverlapping(data_ptr.add(offset), bytes.as_mut_ptr().add(1), 3);
            u32::from_be_bytes(bytes) as u32
        }
        4 => u32::from_be_bytes(*(data_ptr.add(offset) as *const [u8; 4])) as u32,
        _ => std::hint::unreachable_unchecked(),
    }
}

const CELLS_ON_STACK: usize = 32;
const ROOTS_ON_STACK: usize = 2;

const MAX_ROOTS: usize = 32;
