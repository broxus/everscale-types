use std::alloc::Layout;
use std::mem::MaybeUninit;
use std::sync::atomic::AtomicUsize;
use std::sync::Arc;

use rustc_hash::FxHashMap;
use sha2::Digest;
use smallvec::SmallVec;

use super::descriptor::CellDescriptor;
use super::{ArcCell, Cell, CellHash, CellType, LevelMask};
use crate::boc::{BocReader, BocTag};
use crate::util::unlikely;

/// Tightly packed cell representation
#[repr(C)]
struct GenericCell<T: ?Sized, R> {
    header: CellHeader<R>,
    data: T,
}

// TODO: merge VTables for different data array sizes
impl<const N: usize> Cell for GenericCell<[u8; N], ArcCell> {
    fn cell_type(&self) -> CellType {
        if unlikely(self.header.descriptor.is_exotic()) {
            match self.data().first().copied() {
                Some(CellType::PRUNED_BRANCH) => CellType::PrunedBranch,
                Some(CellType::LIBRARY_REFERENCE) => CellType::LibraryReference,
                Some(CellType::MERKLE_PROOF) => CellType::MerkleProof,
                Some(CellType::MERKLE_UPDATE) => CellType::MerkleUpdate,
                // SAFETY: header is initialized
                _ => debug_unreachable!(),
            }
        } else {
            CellType::Ordinary
        }
    }

    fn level_mask(&self) -> LevelMask {
        self.header.descriptor.level_mask()
    }

    fn data(&self) -> &[u8] {
        let data_ptr = std::ptr::addr_of!(self.data) as *const u8;
        let data_len = self.header.descriptor.byte_len() as usize;
        // SAFETY: header is initialized
        unsafe { std::slice::from_raw_parts(data_ptr, data_len) }
    }

    fn bit_len(&self) -> u16 {
        // TODO: use short path and use only the last byte
        compute_bit_len(self.data(), self.header.descriptor.is_aligned())
    }

    fn reference_count(&self) -> usize {
        self.header.descriptor.reference_count()
    }

    fn reference(&self, index: u8) -> Option<&dyn Cell> {
        Some(self.header.reference(index)?.as_ref())
    }

    fn reference_cloned(&self, index: u8) -> Option<ArcCell> {
        Some(self.header.reference(index)?.clone())
    }

    fn hash(&self, level: u8) -> CellHash {
        self.header.level_descr(level).0
    }

    fn depth(&self, level: u8) -> u16 {
        self.header.level_descr(level).1
    }

    fn tree_bit_count(&self) -> u64 {
        self.header.tree_bit_count
    }

    fn tree_cell_count(&self) -> u64 {
        self.header.tree_cell_count
    }
}

struct CellHeader<R> {
    tree_bit_count: u64,
    tree_cell_count: u64,
    hashes: Vec<(CellHash, u16)>,
    descriptor: CellDescriptor,
    references: [MaybeUninit<R>; 4],
}

impl<R> CellHeader<R> {
    unsafe fn new_partial(descriptor: CellDescriptor, refs: RefsBuilder<R>) -> Self {
        Self {
            tree_bit_count: 0,
            tree_cell_count: 0,
            hashes: Default::default(),
            descriptor,
            references: refs.build(),
        }
    }

    fn level_descr(&self, level: u8) -> &(CellHash, u16) {
        let hash_index = self.descriptor.level_mask().hash_index(level);
        // SAFETY: hash index is in range 0..=3
        unsafe { self.hashes.get_unchecked(hash_index as usize) }
    }

    fn reference(&self, i: u8) -> Option<&R> {
        if i < self.descriptor.reference_count() as u8 {
            // SAFETY: Item is initialized
            let child = unsafe { self.references.get_unchecked(i as usize).assume_init_ref() };
            Some(child)
        } else {
            None
        }
    }

    unsafe fn references(&self) -> &[R] {
        std::slice::from_raw_parts(
            self.references.as_ptr() as *const R,
            self.descriptor.reference_count(),
        )
    }
}

impl<R> Drop for CellHeader<R> {
    fn drop(&mut self) {
        let references_ptr = self.references.as_mut_ptr() as *mut R;
        for i in 0..self.descriptor.reference_count() {
            // SAFETY: references were initialized
            unsafe { std::ptr::drop_in_place(references_ptr.add(i)) };
        }
    }
}

struct RefsBuilder<R> {
    inner: [MaybeUninit<R>; 4],
    len: u8,
}

impl<R> Default for RefsBuilder<R> {
    #[inline(always)]
    fn default() -> Self {
        Self {
            // SAFETY: An uninitialized `[MaybeUninit<_>; LEN]` is valid.
            inner: unsafe { MaybeUninit::<[MaybeUninit<_>; 4]>::uninit().assume_init() },
            len: 0,
        }
    }
}

impl<R> RefsBuilder<R> {
    #[inline(always)]
    unsafe fn push(&mut self, child: R) {
        *self.inner.get_unchecked_mut(self.len as usize) = MaybeUninit::new(child);
        self.len += 1;
    }

    #[inline(always)]
    unsafe fn build(self) -> [MaybeUninit<R>; 4] {
        let this = std::mem::ManuallyDrop::new(self);
        std::ptr::read(&this.inner)
    }
}

impl<R> Drop for RefsBuilder<R> {
    fn drop(&mut self) {
        let references_ptr = self.inner.as_mut_ptr() as *mut R;
        for i in 0..self.len {
            // SAFETY: len references were initialized
            unsafe { std::ptr::drop_in_place(references_ptr.add(i as usize)) };
        }
    }
}

type EmptyCell = GenericCell<[u8; 0], ArcCell>;

fn make_arc_cell(header: CellHeader<ArcCell>, data: &[u8]) -> ArcCell {
    #[repr(C)]
    struct ArcInner<A, T: ?Sized> {
        strong: A,
        weak: A,
        obj: T,
    }

    pub fn compute_data_len(len: usize) -> (usize, usize) {
        let len = std::cmp::min(len, 128) as u8;
        let target = if len == 0 {
            0
        } else {
            std::cmp::max(len, 8).next_power_of_two() as usize
        };
        (len as usize, target)
    }

    /// # Safety
    /// `len` must be a power of two
    pub unsafe fn get_vtable(len: usize) -> *const () {
        *VTABLES.get_unchecked(if len == 0 {
            0
        } else {
            1 + len.trailing_zeros() as usize
        })
    }

    const fn gen_vtable_ptr<const N: usize>() -> *const () {
        let uninit = std::mem::MaybeUninit::<GenericCell<[u8; N], ArcCell>>::uninit();
        let fat_ptr = uninit.as_ptr() as *const dyn Cell;
        let [_, vtable] = unsafe { std::mem::transmute::<_, [*const (); 2]>(fat_ptr) };
        vtable
    }

    const VTABLES: [*const (); 9] = [
        gen_vtable_ptr::<0>(),
        gen_vtable_ptr::<8>(), // 1, aligned to 8
        gen_vtable_ptr::<8>(), // 2, aligned to 8
        gen_vtable_ptr::<8>(), // 4, aligned to 8
        gen_vtable_ptr::<8>(),
        gen_vtable_ptr::<16>(),
        gen_vtable_ptr::<32>(),
        gen_vtable_ptr::<64>(),
        gen_vtable_ptr::<128>(),
    ];

    const _: () = assert!(std::mem::size_of::<AtomicUsize>() == std::mem::size_of::<usize>());
    const ALIGN: usize = std::mem::align_of::<ArcInner<AtomicUsize, EmptyCell>>();

    const ARC_DATA_OFFSET: usize =
        offset_of!(ArcInner<usize, EmptyCell>, obj) + offset_of!(EmptyCell, data);

    let (raw_data_len, target_data_len) = compute_data_len(data.len());

    let size = (ARC_DATA_OFFSET + target_data_len + ALIGN - 1) & !(ALIGN - 1);

    unsafe {
        let layout = Layout::from_size_align_unchecked(size, ALIGN).pad_to_align();
        let buffer = std::alloc::alloc(layout);
        if buffer.is_null() {
            std::alloc::handle_alloc_error(layout);
        }

        let ptr = buffer as *mut ArcInner<AtomicUsize, EmptyCell>;
        std::ptr::write(&mut (*ptr).strong, AtomicUsize::new(1));
        std::ptr::write(&mut (*ptr).weak, AtomicUsize::new(1));
        std::ptr::write(&mut (*ptr).obj.header, header);
        std::ptr::copy_nonoverlapping(
            data.as_ptr(),
            std::ptr::addr_of_mut!((*ptr).obj.data) as *mut u8,
            raw_data_len,
        );

        let data = std::ptr::addr_of!((*ptr).obj) as *const ();
        let vtable = get_vtable(target_data_len);

        let ptr: *const dyn Cell = std::mem::transmute([data, vtable]);
        Arc::from_raw(ptr)
    }
}

pub fn deserialize(src: &[u8]) -> Result<ArcCell, std::io::Error> {
    let mut reader = BocReader::new(src.len());

    if unlikely(!reader.require(6)) {
        return Err(unexpected_eof("invalid BOC header"));
    }

    let [flags, offset_size] = unsafe { *(src.as_ptr().add(4) as *const [u8; 2]) };

    let has_index;
    let has_crc;
    let ref_size;
    let supports_multiple_roots;

    match BocTag::from_bytes(src[0..4].try_into().unwrap()) {
        Some(BocTag::Indexed) => {
            has_index = false;
            has_crc = false;
            ref_size = flags as usize;
            supports_multiple_roots = false;
        }
        Some(BocTag::IndexedCrc32) => {
            has_index = true;
            has_crc = true;
            ref_size = flags as usize;
            supports_multiple_roots = false;
        }
        Some(BocTag::Generic) => {
            has_index = flags & 0b1000_0000 != 0;
            has_crc = flags & 0b0100_0000 != 0;
            ref_size = (flags & 0b0000_0111) as usize;
            supports_multiple_roots = true;
        }
        None => return Err(invalid_data("unknown BOC tag")),
    }

    if unlikely(ref_size == 0 || ref_size > 4) {
        return Err(invalid_data("ref size not in range 0..=4"));
    }

    let offset_size = offset_size as usize;
    if unlikely(offset_size == 0 || offset_size > 8) {
        return Err(invalid_data("offset size not in range 0..=8"));
    }
    reader.advance(6);

    if unlikely(!reader.require(ref_size * 4 + offset_size)) {
        return Err(invalid_data("invalid BOC header"));
    }

    // SAFETY: we have already requested more than `ref_size*3`
    let (cell_count, root_count, absent_count) = unsafe {
        (
            reader.read_be_uint_fast(src, ref_size),
            reader.read_be_uint_fast(src, ref_size),
            reader.read_be_uint_fast(src, ref_size),
        )
    };

    if unlikely(!supports_multiple_roots && root_count > 1) {
        return Err(invalid_data("unexpected multiple roots"));
    }
    if unlikely(root_count + absent_count > cell_count) {
        return Err(invalid_data("invalid root or absent cell count"));
    }

    // SAFETY: we have already requested more than `ref_size*3+offset_size`
    let total_cells_size = unsafe { reader.read_be_uint_full(src, offset_size) };

    let min_cell_size = 2;
    if unlikely(total_cells_size < min_cell_size * cell_count as u64) {
        return Err(invalid_data("invalid total cells size"));
    }
    let max_cell_size = 2 + 4 * (2 + 32) + 128 + 4 * ref_size as u64;
    if total_cells_size > max_cell_size * cell_count as u64 {
        return Err(invalid_data("invalid total cells size"));
    }

    // SAFETY: we have already requested more than `ref`
    let root_index = unsafe { reader.read_be_uint_fast(src, ref_size) };
    if root_index >= cell_count {
        return Err(invalid_data("root index out of bounds"));
    }

    let index_size = has_index as u64 * cell_count as u64 * offset_size as u64;
    if unlikely(!reader.require((index_size + total_cells_size + has_crc as u64 * 4) as usize)) {
        return Err(unexpected_eof("missing the rest of the BOC"));
    }

    if has_index {
        reader.advance(cell_count * offset_size);
    }

    let mut intermediate = SmallVec::<[&[u8]; 32]>::with_capacity(cell_count);
    for _ in 0..cell_count {
        if unlikely(!reader.require(2)) {
            return Err(unexpected_eof("expected descriptor bytes"));
        }

        let start = reader.offset();

        // SAFETY: we have already checked the reader has 2 bytes
        let [d1, d2] = unsafe { reader.read_descriptor_bytes(src) };
        if d1 == ABSENT_D1 {
            return Err(unsupported("absent cells are not supported"));
        }

        // 0b11111111 -> 0b01111111 + 1 = 0b10000000 = byte len 128, max bit len = 1023
        // 0b11111110 -> 0b01111111 = byte len 127, bit len = 1016
        let data_len = ((d2 >> 1) + (d2 & 1)) as usize;
        let ref_count = (d1 & 0b111) as usize;
        if ref_count > 4 {
            return Err(invalid_data("cell ref count not in range 0..=4"));
        }

        reader.advance(2 + data_len + ref_count * ref_size);
        if unlikely(!reader.require(0)) {
            return Err(unexpected_eof("expected cell data and references"));
        }

        intermediate.push(&src[start..reader.offset()]);
    }

    let mut done_cells =
        FxHashMap::<u32, ArcCell>::with_capacity_and_hasher(cell_count, Default::default());

    let mut index = intermediate.len();
    for cell in intermediate.iter().rev() {
        index -= 1;

        // SAFETY: cell was already validated before
        unsafe {
            let cell_ptr = cell.as_ptr();

            let descriptor = CellDescriptor::new(*(cell_ptr as *const [u8; 2]));
            let byte_len = descriptor.byte_len() as usize;

            let mut data_ptr = cell_ptr.add(2);
            let data = std::slice::from_raw_parts(data_ptr, byte_len);

            let mut tree_bit_count = compute_bit_len(data, descriptor.is_aligned()) as u64;
            let mut tree_cell_count = 1;

            let mut references = RefsBuilder::default();
            data_ptr = data_ptr.add(byte_len);
            for _ in 0..descriptor.reference_count() {
                let child_index = match ref_size {
                    1 => *data_ptr as u32,
                    2 => u16::from_be_bytes(*(data_ptr as *const [u8; 2])) as u32,
                    3 => {
                        let mut bytes = [0u8; 4];
                        std::ptr::copy_nonoverlapping(data_ptr, bytes.as_mut_ptr().add(1), 3);
                        u32::from_be_bytes(bytes)
                    }
                    4 => u32::from_be_bytes(*(data_ptr as *const [u8; 4])),
                    _ => std::hint::unreachable_unchecked(),
                };

                let child = match done_cells.get(&child_index) {
                    Some(child) => child.clone(),
                    None => return Err(invalid_data("invalid children order")),
                };

                // TODO: use raw pointer
                tree_bit_count += child.tree_bit_count();
                tree_cell_count += child.tree_cell_count();
                references.push(child);

                data_ptr = data_ptr.add(ref_size);
            }

            done_cells.insert(
                index as u32,
                ok!(finalize_cell(
                    CellHeader {
                        tree_bit_count,
                        tree_cell_count,
                        hashes: Default::default(),
                        descriptor,
                        references: references.build(),
                    },
                    data,
                )),
            );
        }
    }

    match done_cells.get(&(root_index as u32)) {
        Some(cell) => Ok(cell.clone()),
        None => Err(invalid_data("root cell not found")),
    }
}

fn finalize_cell(mut header: CellHeader<ArcCell>, data: &[u8]) -> Result<ArcCell, std::io::Error> {
    const HASH_BITS: usize = 256;
    const DEPTH_BITS: usize = 16;

    let mut descriptor = header.descriptor;
    let level_mask = descriptor.level_mask();
    let level = level_mask.level() as usize;
    let bit_len = compute_bit_len(data, descriptor.is_aligned()) as usize;

    // SAFETY: all childer must be initialized
    let references = unsafe { header.references() };

    let mut children_mask = LevelMask::EMPTY;
    for child in references {
        children_mask |= child.level_mask();
    }

    // `hashes_len` is guaranteed to be in range 1..4
    let mut hashes_len = level + 1;

    let (cell_type, computed_level_mask) = if unlikely(descriptor.is_exotic()) {
        let Some(&first_byte) = data.first() else {
            return Err(unexpected_eof("empty data for exotic cell"))
        };

        match first_byte {
            // 8 bits type, 8 bits level mask, level x (hash, depth)
            CellType::PRUNED_BRANCH => {
                let expected_bit_len = 8 + 8 + level * (HASH_BITS + DEPTH_BITS);

                if unlikely(bit_len != expected_bit_len) {
                    return Err(invalid_data("pruned branch bit length mismatch"));
                } else if unlikely(!references.is_empty()) {
                    return Err(invalid_data("pruned branch contains references"));
                } else if unlikely(level_mask != data[1]) {
                    return Err(invalid_data("pruned branch level mask mismatch"));
                }

                hashes_len = 1;
                (CellType::PrunedBranch, level_mask)
            }
            // 8 bits type, hash, depth
            CellType::MERKLE_PROOF => {
                const EXPECTED_BIT_LEN: usize = 8 + HASH_BITS + DEPTH_BITS;
                if unlikely(bit_len != EXPECTED_BIT_LEN) {
                    return Err(invalid_data("merkle proof bit length mismatch"));
                } else if unlikely(references.len() != 1) {
                    return Err(invalid_data(
                        "merkle proof cell must contain exactly one reference",
                    ));
                }

                (CellType::MerkleProof, children_mask.virtualize(1))
            }
            // 8 bits type, 2 x (hash, depth)
            CellType::MERKLE_UPDATE => {
                const EXPECTED_BIT_LEN: usize = 8 + 2 * (HASH_BITS + DEPTH_BITS);
                if unlikely(bit_len != EXPECTED_BIT_LEN) {
                    return Err(invalid_data("merkle update bit length mismatch"));
                } else if unlikely(references.len() != 2) {
                    return Err(invalid_data(
                        "merkle update cell must contain exactly two references",
                    ));
                }

                (CellType::MerkleUpdate, children_mask.virtualize(1))
            }
            // 8 bits type, hash
            CellType::LIBRARY_REFERENCE => {
                const EXPECTED_BIT_LEN: usize = 8 + HASH_BITS;
                if unlikely(bit_len != EXPECTED_BIT_LEN) {
                    return Err(invalid_data("library reference cell bit length mismatch"));
                } else if unlikely(!references.is_empty()) {
                    return Err(invalid_data("library reference cell contains references"));
                }

                (CellType::LibraryReference, LevelMask::EMPTY)
            }
            _ => return Err(invalid_data("unknown cell type")),
        }
    } else {
        (CellType::Ordinary, children_mask)
    };

    if unlikely(computed_level_mask != level_mask) {
        return Err(invalid_data("level mask mismatch"));
    }

    let level_offset = cell_type.is_merkle() as u8;

    let mut hashes = Vec::<(CellHash, u16)>::with_capacity(hashes_len);
    for level in 0..hashes_len {
        let mut hasher = sha2::Sha256::new();

        let level_mask = if cell_type == CellType::PrunedBranch {
            level_mask
        } else {
            LevelMask::from_level(level as u8)
        };

        descriptor.d1 &= !(CellDescriptor::LEVEL_MASK | CellDescriptor::STORE_HASHES_MASK);
        descriptor.d1 |= u8::from(level_mask) << 5;
        hasher.update([descriptor.d1, descriptor.d2]);

        if level == 0 {
            hasher.update(data);
        } else {
            let prev_hash = unsafe { hashes.get_unchecked(level - 1) };
            hasher.update(prev_hash.0.as_slice());
        }

        let mut depth = 0;
        for child in references {
            let child_depth = child.depth(level as u8 + level_offset);

            // TODO: check depth overflow
            depth = std::cmp::max(depth, child_depth + 1);

            hasher.update(child_depth.to_be_bytes());
        }

        for child in references {
            let child_hash = child.hash(level as u8 + level_offset);
            hasher.update(child_hash.as_slice());
        }

        let hash = hasher.finalize().into();
        hashes.push((hash, depth));
    }

    header.hashes = hashes;
    Ok(make_arc_cell(header, data))
}

const ABSENT_D1: u8 = 0b0000_1111;

#[inline(never)]
pub fn compute_bit_len(data: &[u8], aligned: bool) -> u16 {
    let mut length = data.len() as u16 * 8;
    if aligned {
        return length;
    }

    for x in data.iter().rev() {
        if *x == 0 {
            length -= 8;
        } else {
            length -= 1 + x.trailing_zeros() as u16;
            break;
        }
    }
    length
}

fn unexpected_eof(reason: &'static str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::UnexpectedEof, reason)
}

fn invalid_data(reason: &'static str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidData, reason)
}

fn unsupported(reason: &'static str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::Unsupported, reason)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn correct_deserialization() {
        let data = base64::decode("te6ccgEBBAEAzwACg4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEAIBAEAAAAAAAAAAAAAAAAAAAAAAAAAAm2c6ClpzoTVSAHvzVQGDAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHKq1w7OAAkYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACRwAwBAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEljGP8=").unwrap();
        //let data = base64::decode("te6ccgEBAQEABgAACACrQTA=").unwrap();
        let cell = deserialize(&data).unwrap();
        println!("{}", cell.display_tree());
    }
}
