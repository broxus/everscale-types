use crate::cell::finalizer::{Finalizer, PartialCell};
use crate::cell::{Cell, CellContainer, CellFamily, LevelMask, MAX_BIT_LEN, MAX_REF_COUNT};
use crate::util::ArrayVec;
use crate::CellDescriptor;

use super::CellTreeStats;

pub struct CellBuilder<C: CellFamily> {
    data: [u8; 128],
    level_mask: Option<LevelMask>,
    bit_len: u16,
    references: ArrayVec<CellContainer<C>, MAX_REF_COUNT>,
}

impl<C: CellFamily> Default for CellBuilder<C> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<C: CellFamily> CellBuilder<C> {
    pub fn new() -> Self {
        Self {
            data: [0; 128], // TODO: use uninit
            level_mask: None,
            bit_len: 0,
            references: Default::default(),
        }
    }
}

macro_rules! impl_store_uint {
    ($self:ident, $value:ident, bytes: $bytes:literal, bits: $bits:literal) => {
        if $self.bit_len + $bits <= MAX_BIT_LEN {
            let q = ($self.bit_len / 8) as usize;
            let r = $self.bit_len % 8;
            unsafe {
                let data_ptr = $self.data.as_mut_ptr().add(q);
                if r == 0 {
                    let value = $value.to_be_bytes();
                    std::ptr::copy_nonoverlapping(value.as_ptr(), data_ptr, $bytes);
                } else {
                    *data_ptr |= ($value >> ($bits - 8 + r)) as u8;

                    let value: [u8; $bytes] = ($value << (8 - r)).to_be_bytes();
                    std::ptr::copy_nonoverlapping(value.as_ptr(), data_ptr.add(1), $bytes);
                }
            };
            $self.bit_len += $bits;
            true
        } else {
            false
        }
    };
}

impl<C: CellFamily> CellBuilder<C>
where
    CellContainer<C>: AsRef<dyn Cell<C>>,
{
    /// Computes the cell level from the level mask.
    pub fn compute_level(&self) -> u8 {
        self.compute_level_mask().level()
    }

    // Computes the cell level mask from children
    pub fn compute_level_mask(&self) -> LevelMask {
        if let Some(level_mask) = self.level_mask {
            level_mask
        } else {
            let mut children_mask = LevelMask::EMPTY;
            for child in self.references.as_ref() {
                children_mask |= child.as_ref().descriptor().level_mask();
            }
            children_mask
        }
    }

    /// Returns the data size of this cell in bits.
    #[inline]
    pub fn bit_len(&self) -> u16 {
        self.bit_len
    }

    #[inline]
    pub fn spare_bits_capacity(&self) -> u16 {
        MAX_BIT_LEN - self.bit_len
    }

    #[inline]
    pub fn spare_refs_capacity(&self) -> u8 {
        (MAX_REF_COUNT - self.references.len()) as u8
    }

    #[inline]
    pub fn with_level_mask(mut self, level_mask: LevelMask) -> Self {
        self.level_mask = Some(level_mask);
        self
    }

    #[inline]
    pub fn set_level_mask(&mut self, level_mask: LevelMask) {
        self.level_mask = Some(level_mask);
    }

    pub fn store_zeroes(&mut self, bits: u16) -> bool {
        if self.bit_len + bits <= MAX_BIT_LEN {
            self.bit_len += bits;
            true
        } else {
            false
        }
    }

    pub fn store_bit_zero(&mut self) -> bool {
        let fits = self.bit_len < MAX_BIT_LEN;
        self.bit_len += fits as u16;
        fits
    }

    pub fn store_bit_true(&mut self) -> bool {
        if self.bit_len < MAX_BIT_LEN {
            let q = (self.bit_len / 8) as usize;
            let r = self.bit_len % 8;
            unsafe { *self.data.get_unchecked_mut(q) |= 1 << (7 - r) };
            self.bit_len += 1;
            true
        } else {
            false
        }
    }

    pub fn store_u8(&mut self, value: u8) -> bool {
        if self.bit_len + 8 <= MAX_BIT_LEN {
            let q = (self.bit_len / 8) as usize;
            let r = self.bit_len % 8;
            unsafe {
                if r == 0 {
                    // xxxxxxxx
                    *self.data.get_unchecked_mut(q) = value;
                } else {
                    // yyyxxxxx|xxx00000
                    *self.data.get_unchecked_mut(q) |= value >> r;
                    *self.data.get_unchecked_mut(q + 1) = value << (8 - r);
                }
            };
            self.bit_len += 8;
            true
        } else {
            false
        }
    }

    pub fn store_u16(&mut self, value: u16) -> bool {
        impl_store_uint!(self, value, bytes: 2, bits: 16)
    }

    pub fn store_u32(&mut self, value: u32) -> bool {
        impl_store_uint!(self, value, bytes: 4, bits: 32)
    }

    pub fn store_u64(&mut self, value: u64) -> bool {
        impl_store_uint!(self, value, bytes: 8, bits: 64)
    }

    pub fn store_u128(&mut self, value: u128) -> bool {
        impl_store_uint!(self, value, bytes: 16, bits: 128)
    }

    #[inline]
    pub fn references(&self) -> &[CellContainer<C>] {
        self.references.as_ref()
    }

    pub fn store_reference(&mut self, cell: CellContainer<C>) -> bool {
        if self.references.len() < MAX_REF_COUNT {
            // SAFETY: reference count is in the valid range
            unsafe { self.references.push(cell) }
            true
        } else {
            false
        }
    }

    pub fn build(self) -> Option<CellContainer<C>> {
        self.build_ext(&mut C::default_finalizer())
    }

    pub fn build_ext(mut self, finalizer: &mut dyn Finalizer<C>) -> Option<CellContainer<C>> {
        debug_assert!(self.bit_len <= MAX_BIT_LEN);
        debug_assert!(self.references.len() <= MAX_REF_COUNT);

        let mut stats = CellTreeStats {
            bit_count: self.bit_len as u64,
            cell_count: 1,
        };

        let mut children_mask = LevelMask::EMPTY;
        for child in self.references.as_ref() {
            let child = child.as_ref();
            children_mask |= child.descriptor().level_mask();
            stats += child.stats();
        }

        let is_exotic = self.level_mask.is_some();
        let level_mask = self.level_mask.unwrap_or(children_mask);

        let d1 = CellDescriptor::compute_d1(level_mask, is_exotic, self.references.len() as u8);
        let d2 = CellDescriptor::compute_d2(self.bit_len);

        let rem = self.bit_len % 8;
        let last_byte = (self.bit_len / 8) as usize;
        if rem > 0 {
            // SAFETY: `last_byte` is in the valid range
            let last_byte = unsafe { self.data.get_unchecked_mut(last_byte) };

            // x0000000 - rem=1, tag_mask=01000000, data_mask=11000000
            // xx000000 - rem=2, tag_mask=00100000, data_mask=11100000
            // xxx00000 - rem=3, tag_mask=00010000, data_mask=11110000
            // xxxx0000 - rem=4, tag_mask=00001000, data_mask=11111000
            // xxxxx000 - rem=5, tag_mask=00000100, data_mask=11111100
            // xxxxxx00 - rem=6, tag_mask=00000010, data_mask=11111110
            // xxxxxxx0 - rem=7, tag_mask=00000001, data_mask=11111111
            let tag_mask: u8 = 1 << (7 - rem);
            let data_mask = !(tag_mask - 1);

            // xxxxyyyy & data_mask -> xxxxy000 | tag_mask -> xxxx1000
            *last_byte = (*last_byte & data_mask) | tag_mask;
        }

        let byte_len = (self.bit_len + 7) / 8;
        let data = &self.data[..std::cmp::min(byte_len as usize, 128)];

        let partial_cell: PartialCell<C> = PartialCell {
            stats,
            bit_len: self.bit_len,
            descriptor: CellDescriptor { d1, d2 },
            children_mask,
            references: self.references,
            data,
        };
        finalizer.finalize_cell(partial_cell)
    }
}
