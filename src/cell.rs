use std::alloc::Layout;
use std::mem::MaybeUninit;
use std::ops::Deref;

use std::sync::atomic::AtomicUsize;
use std::sync::Arc;

use smallvec::SmallVec;

pub type Cell = GenericCell<[u8], CellRef>;

#[repr(transparent)]
#[derive(Clone)]
pub struct CellRef(pub Arc<Cell>);

impl Deref for CellRef {
    type Target = Cell;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

const _ASSERT: () = assert!(std::mem::size_of::<CellRef>() >= 4);

impl Cell {
    pub fn with_data(d1: u8, d2: u8, data: &[u8]) -> Arc<Self> {
        #[repr(C)]
        struct ArcInner<T: ?Sized> {
            strong: AtomicUsize,
            weak: AtomicUsize,
            data: T,
        }

        type EmptyData = GenericCell<[u8; 0], Arc<Cell>>;

        const ALIGN: usize = std::mem::align_of::<ArcInner<EmptyData>>() - 1;

        let bit_len = compute_bit_len(data, d2 & 1 == 0);
        let byte_len = ((bit_len + 7) / 8) as usize;

        let data_offset =
            crate::offset_of!(ArcInner<EmptyData>, data) + crate::offset_of!(EmptyData, data);

        let size = (data_offset + byte_len + ALIGN - 1) & !(ALIGN - 1);

        unsafe {
            let layout = Layout::from_size_align_unchecked(size, ALIGN);
            let buffer = std::alloc::alloc(layout);
            if buffer.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            let fake_slice = std::ptr::slice_from_raw_parts_mut(buffer, byte_len);
            let ptr = fake_slice as *mut ArcInner<Cell>;

            std::ptr::write(&mut (*ptr).strong, AtomicUsize::new(1));
            std::ptr::write(&mut (*ptr).weak, AtomicUsize::new(1));
            std::ptr::write(&mut (*ptr).data.bit_len, bit_len);
            std::ptr::write(&mut (*ptr).data.d1, d1);
            std::ptr::write(&mut (*ptr).data.d2, d2);
            std::ptr::write(&mut (*ptr).data.references, make_empty_references());
            std::ptr::copy_nonoverlapping(data.as_ptr(), (*ptr).data.data.as_mut_ptr(), byte_len);

            Arc::from_raw(std::ptr::addr_of_mut!((*ptr).data))
        }
    }

    pub fn reference(&self, i: u8) -> Option<&Arc<Self>> {
        if i < self.d1 & 7 {
            // SAFETY: Item is initialized
            let CellRef(c) = unsafe { self.references.get_unchecked(i as usize).assume_init_ref() };
            Some(c)
        } else {
            None
        }
    }

    pub fn deserialize(src: &[u8]) -> Option<Arc<Self>> {
        let mut index = Index {
            value_len: src.len(),
            offset: 0,
        };

        index.require(6)?;
        let flags = src[4];

        let has_index;
        let has_crc;
        let has_cache_bits;
        let ref_size;
        let supports_multiple_roots;
        match &src[0..4] {
            BOC_INDEXED_TAG => {
                has_index = false;
                has_crc = false;
                has_cache_bits = false;
                ref_size = flags as usize;
                supports_multiple_roots = false;
            }
            BOC_INDEXED_CRC32_TAG => {
                has_index = true;
                has_crc = true;
                has_cache_bits = false;
                ref_size = flags as usize;
                supports_multiple_roots = false;
            }
            BOC_GENERIC_TAG => {
                has_index = flags & 0b1000_0000 != 0;
                has_crc = flags & 0b0100_0000 != 0;
                has_cache_bits = flags & 0b0010_0000 != 0;
                ref_size = (flags & 0b0000_0111) as usize;
                supports_multiple_roots = true;
            }
            _ => return None,
        }
        if ref_size == 0 || ref_size > 4 {
            return None;
        }
        let offset_size = src[5] as usize;
        if offset_size == 0 || offset_size > 8 {
            return None;
        }
        index.advance(6);

        index.require(ref_size * 3 + offset_size)?;
        let (cell_count, root_count, absent_count) = unsafe {
            (
                index.read_be_uint_fast(src, ref_size),
                index.read_be_uint_fast(src, ref_size),
                index.read_be_uint_fast(src, ref_size),
            )
        };

        if !supports_multiple_roots && root_count > 1 {
            return None;
        }
        if root_count + absent_count > cell_count {
            return None;
        }

        index.require(offset_size)?;
        let total_cells_size = unsafe { index.read_be_uint_full(src, offset_size) };

        let min_cell_size = 2;
        if total_cells_size < min_cell_size * cell_count as u64 {
            return None;
        }
        let max_cell_size = 2 + 4 * (2 + 32) + 128 + 4 * ref_size as u64;
        if total_cells_size > max_cell_size * cell_count as u64 {
            return None;
        }

        let index_size = has_index as u64 * cell_count as u64 * offset_size as u64;
        index.require((index_size + total_cells_size + has_crc as u64 * 4) as usize)?;

        if has_index {
            index.advance(cell_count * offset_size);
        }

        let mut intermediate = SmallVec::<[IntermediateCell; 32]>::with_capacity(cell_count);
        for _ in 0..cell_count {
            index.require(2)?;
            let start = index.offset;

            let [d1, d2] = unsafe { index.read_descriptor_bytes(src) };
            if d1 == ABSENT_D1 {
                return None;
            }

            // 0b11111111 -> 0b01111111 + 1 = 0b10000000 = byte len 128, max bit len = 1023
            // 0b11111110 -> 0b01111111 = byte len 127, bit len = 1016
            let data_len = ((d2 >> 1) + (d2 & 1)) as usize;
            let ref_count = (d1 & 0b111) as usize;
            if ref_count > 4 {
                return None;
            }

            index.advance(data_len + ref_count * ref_size);
            index.require(0)?;

            intermediate.push(IntermediateCell {
                data: &src[start..index.offset],
            });
        }

        // let mut done_cells = FxHashMap::with_capacity_and_hasher(cell_count, Default::default());
        // for cell in intermediate.iter().rev() {
        //     // let [d1, d2] = unsafe { index.read };
        // }

        Some(todo!())
    }
}

struct IntermediateCell<'a> {
    data: &'a [u8],
}

const BOC_INDEXED_TAG: &[u8] = &[0x68, 0xff, 0x65, 0xf3];
const BOC_INDEXED_CRC32_TAG: &[u8] = &[0xac, 0xc3, 0xa7, 0x28];
const BOC_GENERIC_TAG: &[u8] = &[0xb5, 0xee, 0x9c, 0x72];

const ABSENT_D1: u8 = 0b0000_1111;

struct Index {
    value_len: usize,
    offset: usize,
}

impl Index {
    #[inline(always)]
    fn require(&self, len: usize) -> Option<()> {
        if self.offset + len < self.value_len {
            Some(())
        } else {
            None
        }
    }

    #[inline(always)]
    fn advance(&mut self, bytes: usize) {
        self.offset += bytes;
    }

    #[inline(always)]
    unsafe fn read_be_uint_fast(&mut self, data: &[u8], size: usize) -> usize {
        let res = read_be_uint_fast(data, self.offset, size);
        self.advance(size);
        res
    }

    #[inline(always)]
    unsafe fn read_be_uint_full(&mut self, data: &[u8], size: usize) -> u64 {
        let res = match size {
            1..=4 => read_be_uint_fast(data, self.offset, size) as u64,
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
    unsafe fn read_descriptor_bytes(&mut self, data: &[u8]) -> [u8; 2] {
        *(data.as_ptr().add(self.offset) as *const [u8; 2])
    }
}

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

#[inline(always)]
unsafe fn read_be_uint_fast(data: &[u8], offset: usize, size: usize) -> usize {
    match size {
        1 => *data.get_unchecked(offset) as usize,
        2 => u16::from_be_bytes(*(data.as_ptr().add(offset) as *const [u8; 2])) as usize,
        3 => {
            let mut bytes = [0u8; 4];
            std::ptr::copy_nonoverlapping(data.as_ptr().add(offset), bytes.as_mut_ptr().add(1), 3);
            u32::from_be_bytes(bytes) as usize
        }
        4 => u32::from_be_bytes(*(data.as_ptr().add(offset) as *const [u8; 4])) as usize,
        _ => std::hint::unreachable_unchecked(),
    }
}

impl Deref for Index {
    type Target = usize;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.offset
    }
}

pub struct GenericCell<T: ?Sized, R> {
    bit_len: u16,
    d1: u8,
    d2: u8,
    references: [MaybeUninit<R>; 4],
    data: T,
}

#[inline(always)]
fn make_empty_references<R>() -> [MaybeUninit<R>; 4] {
    // SAFETY: An uninitialized `[MaybeUninit<_>; LEN]` is valid.
    unsafe { MaybeUninit::<[MaybeUninit<_>; 4]>::uninit().assume_init() }
}

// impl<T> FromIterator<T> for Refs<T> {
//     #[inline(always)]
//     fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
//         let mut refs = Self::default();
//
//         for item in iter.into_iter().take(4) {
//             refs.references[refs.len as usize].write(item);
//             refs.len += 1;
//         }
//
//         refs
//     }
// }

/// Brings [unlikely](core::intrinsics::unlikely) to stable rust.
#[inline(always)]
const fn unlikely(b: bool) -> bool {
    #[allow(clippy::needless_bool)]
    if (1i32).checked_div(if b { 0 } else { 1 }).is_none() {
        true
    } else {
        false
    }
}

#[macro_export]
macro_rules! offset_of {
    ($ty: path, $field: tt) => {{
        let uninit = <::core::mem::MaybeUninit<$ty>>::uninit();
        let base_ptr: *const $ty = uninit.as_ptr();
        let field_ptr = unsafe { ::core::ptr::addr_of!((*base_ptr).$field) };
        (field_ptr as usize) - (base_ptr as usize)
    }};
}
