use std::alloc::Layout;
use std::mem::MaybeUninit;
use std::ops::Deref;
use std::sync::atomic::AtomicUsize;
use std::sync::Arc;

use super::{ArcCell, Cell, CellType, LevelMask};

pub fn make_arc_cell(header: CellHeader<ArcCell>, data: &[u8]) -> ArcCell {
    #[repr(C)]
    struct ArcInner<A, T: ?Sized> {
        strong: A,
        weak: A,
        obj: T,
    }

    type EmptyData = GenericCell<[u8; 0], ArcCell>;

    pub fn compute_data_len(len: usize) -> (usize, usize) {
        let len = std::cmp::min(len, 128) as u8;
        let target = if len == 0 {
            0
        } else {
            len.next_power_of_two() as usize
        };
        (len as usize, target)
    }

    /// # Safety
    /// `len` must be a power of two
    pub unsafe fn get_vtable(len: usize) -> usize {
        let vtable_ptr = *VTABLES.get_unchecked(if len == 0 {
            0
        } else {
            1 + len.trailing_zeros() as usize
        });

        // Cast vtable pointer to usize
        std::mem::transmute(vtable_ptr)
    }

    const fn gen_vtable_ptr<const N: usize>() -> *const () {
        let uninit = std::mem::MaybeUninit::<GenericCell<[u8; N], ArcCell>>::uninit();
        let fat_ptr = uninit.as_ptr() as *const dyn Cell;
        let [_, vtable] = unsafe { std::mem::transmute::<_, [*const (); 2]>(fat_ptr) };
        vtable
    }

    const VTABLES: [*const (); 9] = [
        gen_vtable_ptr::<0>(),
        gen_vtable_ptr::<1>(),
        gen_vtable_ptr::<2>(),
        gen_vtable_ptr::<4>(),
        gen_vtable_ptr::<8>(),
        gen_vtable_ptr::<16>(),
        gen_vtable_ptr::<32>(),
        gen_vtable_ptr::<64>(),
        gen_vtable_ptr::<128>(),
    ];

    const _: () = assert!(std::mem::size_of::<AtomicUsize>() == std::mem::size_of::<usize>());
    const ALIGN: usize = std::mem::align_of::<ArcInner<AtomicUsize, EmptyData>>();
    const DATA_OFFSET: usize =
        offset_of!(ArcInner<usize, EmptyData>, obj) + offset_of!(EmptyData, data);

    let (raw_data_len, target_data_len) = compute_data_len(data.len());

    let size = (DATA_OFFSET + target_data_len + ALIGN - 1) & !(ALIGN - 1);

    unsafe {
        let layout = Layout::from_size_align_unchecked(size, ALIGN).pad_to_align();
        let buffer = std::alloc::alloc(layout);
        if buffer.is_null() {
            std::alloc::handle_alloc_error(layout);
        }

        let ptr = buffer as *mut ArcInner<AtomicUsize, EmptyData>;

        std::ptr::write(&mut (*ptr).strong, AtomicUsize::new(1));
        std::ptr::write(&mut (*ptr).weak, AtomicUsize::new(1));
        std::ptr::write(&mut (*ptr).obj.header, header);
        std::ptr::copy_nonoverlapping(data.as_ptr(), (*ptr).obj.data.as_mut_ptr(), raw_data_len);

        let data = std::ptr::addr_of!((*ptr).obj);
        let vtable = get_vtable(target_data_len);

        let ptr: *const dyn Cell = std::mem::transmute(std::slice::from_raw_parts(data, vtable));
        Arc::from_raw(ptr)
    }
}

impl<const N: usize> Cell for GenericCell<[u8; N], ArcCell> {
    fn cell_type(&self) -> CellType {
        if (&self.header.d1 & 0b1000) == 0 {
            CellType::Ordinary
        } else {
            todo!()
        }
    }

    fn level_mask(&self) -> LevelMask {
        // SAFETY: `u8 >> 5` is always 3 bits long
        unsafe { LevelMask::new_unchecked(self.header.d1 >> 5) }
    }

    fn data(&self) -> &[u8] {
        &self.data
    }

    fn bit_len(&self) -> u16 {
        // TODO: use short path and use only the last byte
        compute_bit_len(&self.data, self.header.d2 & 1 == 0)
    }

    fn reference_count(&self) -> usize {
        (self.header.d1 & 0b111) as usize
    }

    fn reference(&self, i: u8) -> Option<&dyn Cell> {
        if i < self.header.d1 & 7 {
            // SAFETY: Item is initialized
            let child = unsafe {
                self.header
                    .references
                    .get_unchecked(i as usize)
                    .assume_init_ref()
            };
            Some(child.as_ref())
        } else {
            None
        }
    }

    fn tree_bit_count(&self) -> u64 {
        self.header.tree_bit_count
    }

    fn tree_cell_count(&self) -> u64 {
        self.header.tree_cell_count
    }
}

struct IntermediateCell<'a> {
    data: &'a [u8],
}

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

#[repr(C)]
pub struct GenericCell<T: ?Sized, R> {
    header: CellHeader<R>,
    data: T,
}

pub struct CellHeader<R> {
    tree_bit_count: u64,
    tree_cell_count: u64,
    depth: u16,
    d1: u8,
    d2: u8,
    references: [MaybeUninit<R>; 4],
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
