use std::mem::MaybeUninit;

use crate::cell::finalizer::{CellParts, DefaultFinalizer, Finalizer};
use crate::cell::{CellContainer, CellFamily, LevelMask, MAX_BIT_LEN, MAX_REF_COUNT};
use crate::util::ArrayVec;
use crate::{CellDescriptor, CellSlice};

use super::CellTreeStats;

pub trait Store<C: CellFamily> {
    fn store_into(&self, builder: &mut CellBuilder<C>) -> bool;
}

impl<C: CellFamily, T: Store<C> + ?Sized> Store<C> for &T {
    #[inline]
    fn store_into(&self, builder: &mut CellBuilder<C>) -> bool {
        <T as Store<C>>::store_into(self, builder)
    }
}

/// Builder for constructing cells with densely packed data.
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

impl<C: CellFamily> Clone for CellBuilder<C>
where
    CellContainer<C>: Clone,
{
    fn clone(&self) -> Self {
        Self {
            data: self.data,
            level_mask: self.level_mask,
            bit_len: self.bit_len,
            references: self.references.clone(),
        }
    }
}

macro_rules! impl_store_uint {
    ($self:ident, $value:ident, bytes: $bytes:literal, bits: $bits:literal) => {
        if $self.bit_len + $bits <= MAX_BIT_LEN {
            let q = ($self.bit_len / 8) as usize;
            let r = $self.bit_len % 8;
            // SAFETY: q is in range 0..=127, r is in range 0..=7
            unsafe {
                let data_ptr = $self.data.as_mut_ptr().add(q);
                debug_assert!(q + $bytes + usize::from(r > 0) <= 128);
                if r == 0 {
                    // Just append data
                    let value = $value.to_be_bytes();
                    std::ptr::copy_nonoverlapping(value.as_ptr(), data_ptr, $bytes);
                } else {
                    // Append high bits to the last byte
                    *data_ptr |= ($value >> ($bits - 8 + r)) as u8;
                    // Make shifted bytes
                    let value: [u8; $bytes] = ($value << (8 - r)).to_be_bytes();
                    // Write shifted bytes
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

impl<C: CellFamily> CellBuilder<C> {
    /// Creates an empty cell builder.
    pub fn new() -> Self {
        Self {
            data: [0; 128],
            level_mask: None,
            bit_len: 0,
            references: Default::default(),
        }
    }

    /// Tries to create a cell builder with the specified data.
    ///
    /// NOTE: if `bits` is greater than `bytes * 8`, pads the value with zeros (as high bits).
    pub fn from_raw_data(value: &[u8], bits: u16) -> Option<Self> {
        let mut res = Self::new();
        if res.store_raw(value, bits) {
            Some(res)
        } else {
            None
        }
    }

    /// Returns the data size of this cell in bits.
    #[inline]
    pub fn bit_len(&self) -> u16 {
        self.bit_len
    }

    /// Returns remaining data capacity in bits.
    #[inline]
    pub fn spare_bits_capacity(&self) -> u16 {
        MAX_BIT_LEN - self.bit_len
    }

    /// Returns remaining references capacity.
    #[inline]
    pub fn spare_refs_capacity(&self) -> u8 {
        (MAX_REF_COUNT - self.references.len()) as u8
    }

    /// Returns true if there is enough remaining capacity to fit `bits` and `refs`.
    #[inline]
    pub fn has_capacity(&self, bits: u16, refs: u8) -> bool {
        self.bit_len + bits <= MAX_BIT_LEN && self.references.len() + refs as usize <= MAX_REF_COUNT
    }

    /// Explicitly sets the level mask and marks this cell as exotic.
    #[inline]
    pub fn with_level_mask(mut self, level_mask: LevelMask) -> Self {
        self.level_mask = Some(level_mask);
        self
    }

    /// Explicitly sets the level mask and marks this cell as exotic.
    #[inline]
    pub fn set_level_mask(&mut self, level_mask: LevelMask) {
        self.level_mask = Some(level_mask);
    }

    /// Tries to store the specified number of zero bits in the cell,
    /// returning `false` if there is not enough remaining capacity.
    pub fn store_zeros(&mut self, bits: u16) -> bool {
        if self.bit_len + bits <= MAX_BIT_LEN {
            self.bit_len += bits;
            true
        } else {
            false
        }
    }

    /// Tries to store one zero bit in the cell,
    /// returning `false` if there is not enough remaining capacity.
    pub fn store_bit_zero(&mut self) -> bool {
        let fits = self.bit_len < MAX_BIT_LEN;
        self.bit_len += fits as u16;
        fits
    }

    /// Tries to store one non-zero bit in the cell,
    /// returning `false` if there is not enough remaining capacity.
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

    /// Tries to store `u8` in the cell,
    /// returning `false` if there is not enough remaining capacity.
    pub fn store_u8(&mut self, value: u8) -> bool {
        if self.bit_len + 8 <= MAX_BIT_LEN {
            let q = (self.bit_len / 8) as usize;
            let r = self.bit_len % 8;
            unsafe {
                if r == 0 {
                    debug_assert!(q < 128);
                    // xxxxxxxx
                    *self.data.get_unchecked_mut(q) = value;
                } else {
                    debug_assert!(q + 1 < 128);
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

    /// Tries to store `u16` in the cell,
    /// returning `false` if there is not enough remaining capacity.
    pub fn store_u16(&mut self, value: u16) -> bool {
        impl_store_uint!(self, value, bytes: 2, bits: 16)
    }

    /// Tries to store `u32` in the cell,
    /// returning `false` if there is not enough remaining capacity.
    pub fn store_u32(&mut self, value: u32) -> bool {
        impl_store_uint!(self, value, bytes: 4, bits: 32)
    }

    /// Tries to store `u64` in the cell,
    /// returning `false` if there is not enough remaining capacity.
    pub fn store_u64(&mut self, value: u64) -> bool {
        impl_store_uint!(self, value, bytes: 8, bits: 64)
    }

    /// Tries to store `u128` in the cell,
    /// returning `false` if there is not enough remaining capacity.
    pub fn store_u128(&mut self, value: u128) -> bool {
        impl_store_uint!(self, value, bytes: 16, bits: 128)
    }

    /// Tries to store 32 bytes in the cell,
    /// returning `false` if there is not enough remaining capacity.
    pub fn store_u256(&mut self, value: &[u8; 32]) -> bool {
        if self.bit_len + 256 <= MAX_BIT_LEN {
            let q = (self.bit_len / 8) as usize;
            let r = self.bit_len % 8;
            unsafe {
                let data_ptr = self.data.as_mut_ptr().add(q);
                debug_assert!(q + 32 + usize::from(r > 0) <= 128);
                if r == 0 {
                    // Just append data
                    std::ptr::copy_nonoverlapping(value.as_ptr(), data_ptr, 32);
                } else {
                    // Interpret 32 bytes as two u128
                    let [mut hi, mut lo]: [u128; 2] = std::mem::transmute_copy(value);

                    // Numbers are in big endian order, swap bytes on little endian arch
                    #[cfg(target_endian = "little")]
                    {
                        hi = hi.swap_bytes();
                        lo = lo.swap_bytes();
                    }

                    let shift = 8 - r;

                    // Append high bits to the last byte
                    *data_ptr |= (hi >> (128 - shift)) as u8;
                    // Make shifted bytes
                    let hi: [u8; 16] = ((hi << shift) | (lo >> (128 - shift))).to_be_bytes();
                    let lo: [u8; 16] = (lo << shift).to_be_bytes();
                    // Write shifted bytes
                    std::ptr::copy_nonoverlapping(hi.as_ptr(), data_ptr.add(1), 16);
                    std::ptr::copy_nonoverlapping(lo.as_ptr(), data_ptr.add(17), 16);
                }
            };
            self.bit_len += 256;
            true
        } else {
            false
        }
    }

    /// Tries to store `u8` in the cell (but only the specified number of bits),
    /// returning `false` if there is not enough remaining capacity.
    ///
    /// NOTE: if `bits` is greater than **8**, pads the value with zeros (as high bits).
    pub fn store_small_uint(&mut self, mut value: u8, mut bits: u16) -> bool {
        if bits == 0 {
            return true;
        }

        if self.bit_len + bits <= MAX_BIT_LEN {
            bits = if let Some(offset) = bits.checked_sub(8) {
                self.bit_len += offset;
                8
            } else {
                bits
            };

            // Ensure that value starts with significant bits
            value <<= 8 - bits;

            let q = (self.bit_len / 8) as usize;
            let r = self.bit_len % 8;
            unsafe {
                debug_assert!(q < 128);
                if r == 0 {
                    // xxxxxxxx
                    *self.data.get_unchecked_mut(q) = value;
                } else {
                    // yyyxxxxx|xxx00000
                    *self.data.get_unchecked_mut(q) |= value >> r;
                    if bits + r > 8 {
                        debug_assert!(q + 1 < 128);
                        *self.data.get_unchecked_mut(q + 1) = value << (8 - r);
                    }
                }
            };
            self.bit_len += bits;
            true
        } else {
            false
        }
    }

    /// Tries to store `u64` in the cell (but only the specified number of bits),
    /// returning `false` if there is not enough remaining capacity.
    ///
    /// NOTE: if `bits` is greater than **64**, pads the value with zeros (as high bits).
    pub fn store_uint(&mut self, mut value: u64, mut bits: u16) -> bool {
        if bits == 0 {
            return true;
        }

        if self.bit_len + bits <= MAX_BIT_LEN {
            // Store zeros if bits is greater than 64
            bits = if let Some(offset) = bits.checked_sub(64) {
                self.bit_len += offset;
                64
            } else {
                bits
            };

            // Ensure that value starts with significant bits
            value <<= 64 - bits;

            let q = (self.bit_len / 8) as usize;
            let r = self.bit_len % 8;
            // SAFETY: q is in range 0..=127, r is in range 0..=7
            unsafe {
                let data_ptr = self.data.as_mut_ptr().add(q);
                if r == 0 {
                    let byte_len = ((bits + 7) / 8) as usize;
                    debug_assert!(q + byte_len <= 128);

                    // Just append data
                    let value = value.to_be_bytes();
                    std::ptr::copy_nonoverlapping(value.as_ptr(), data_ptr, byte_len);
                } else {
                    debug_assert!(q < 128);

                    // Append high bits to the last byte
                    let shift = 8 - r;
                    *data_ptr |= (value >> (64 - shift)) as u8;

                    // If there are some bits left
                    if let Some(bits) = bits.checked_sub(shift) {
                        if bits > 0 {
                            let byte_len = ((bits + 7) / 8) as usize;
                            debug_assert!(q + 1 + byte_len <= 128);

                            // Make shifted bytes
                            let value: [u8; 8] = (value << shift).to_be_bytes();
                            // Write shifted bytes
                            std::ptr::copy_nonoverlapping(
                                value.as_ptr(),
                                data_ptr.add(1),
                                byte_len,
                            );
                        }
                    }
                }
            }
            self.bit_len += bits;
            true
        } else {
            false
        }
    }

    /// Tries to store bytes in the cell (but only the specified number of bits),
    /// returning `false` if there is not enough remaining capacity.
    ///
    /// NOTE: if `bits` is greater than `bytes * 8`, pads the value with zeros (as high bits).
    pub fn store_raw(&mut self, value: &[u8], bits: u16) -> bool {
        store_raw(&mut self.data, &mut self.bit_len, value, bits)
    }

    /// Tries to store the remaining slice data in the cell,
    /// returning `false` if there is not enough remaining capacity.
    pub fn store_slice_data<C1: CellFamily>(&mut self, value: &CellSlice<'_, C1>) -> bool {
        let bits = value.remaining_bits();
        if self.bit_len + bits <= MAX_BIT_LEN {
            let mut slice_data = MaybeUninit::<[u8; 128]>::uninit();
            let slice_data = unsafe { &mut *(slice_data.as_mut_ptr() as *mut [u8; 128]) };
            let Some(slice_data) = value.get_raw(0, slice_data, bits) else {
                return false;
            };

            self.store_raw(slice_data, bits)
        } else {
            false
        }
    }

    /// Tries to prepend bytes to the cell data (but only the specified number of bits),
    /// returning `false` if there is not enough capacity.
    ///
    /// NOTE: if `bits` is greater than `bytes * 8`, pads the value with zeros (as high bits).
    pub fn prepend_raw(&mut self, value: &[u8], bits: u16) -> bool {
        if bits == 0 {
            return true;
        }

        // Prevent asm code bloat
        fn store_raw_impl(
            data: &mut [u8; 128],
            bit_len: &mut u16,
            value: &[u8],
            bits: u16,
        ) -> bool {
            store_raw(data, bit_len, value, bits)
        }

        if self.bit_len + bits <= MAX_BIT_LEN {
            let mut data = [0; 128];
            let mut bit_len = 0;
            if store_raw_impl(&mut data, &mut bit_len, value, bits)
                && store_raw_impl(&mut data, &mut bit_len, &self.data, self.bit_len)
            {
                self.data = data;
                self.bit_len = bit_len;
                true
            } else {
                false
            }
        } else {
            false
        }
    }
}

#[inline]
fn store_raw(data: &mut [u8; 128], bit_len: &mut u16, value: &[u8], mut bits: u16) -> bool {
    if *bit_len + bits <= MAX_BIT_LEN {
        let max_bit_len = value.len().saturating_mul(8) as u16;
        bits = if let Some(offset) = bits.checked_sub(max_bit_len) {
            *bit_len += offset;
            max_bit_len
        } else {
            bits
        };

        // Do nothing for empty slices or noop store
        if bits == 0 {
            return true;
        }

        let q = (*bit_len / 8) as usize;
        let r = *bit_len % 8;
        // SAFETY: q is in range 0..=127, r is in range 0..=7
        unsafe {
            let mut data_ptr = data.as_mut_ptr().add(q);
            let mut value_ptr = value.as_ptr();

            if r == 0 {
                let byte_len = ((bits + 7) / 8) as usize;
                debug_assert!(q + byte_len <= 128);
                debug_assert!(byte_len <= value.len());

                std::ptr::copy_nonoverlapping(value_ptr, data_ptr, byte_len);

                let bits_r = bits % 8;
                if bits_r != 0 {
                    *data_ptr.add(byte_len - 1) &= 0xff << (8 - bits_r);
                }
            } else {
                let byte_len = ((bits + r + 7) / 8) as usize - 1;
                let value_len = ((bits + 7) / 8) as usize;
                debug_assert!(q + byte_len <= 128);
                debug_assert!(byte_len <= value_len && value_len <= value.len());

                let shift = 8 - r;
                for _ in 0..byte_len {
                    *data_ptr |= *value_ptr >> r;
                    data_ptr = data_ptr.add(1);
                    *data_ptr = *value_ptr << shift;
                    value_ptr = value_ptr.add(1);
                }
                if byte_len < value_len {
                    *data_ptr |= *value_ptr >> r;
                }

                let bits_r = (r + bits) % 8;
                if bits_r != 0 {
                    *data_ptr &= 0xff << (8 - bits_r);
                }
            }
        }
        *bit_len += bits;
        true
    } else {
        false
    }
}

impl<C: CellFamily> CellBuilder<C> {
    /// Computes the cell level from the level mask.
    pub fn compute_level(&self) -> u8 {
        self.compute_level_mask().level()
    }

    // Computes the cell level mask from children.
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

    /// Returns a slice of the child cells stored in the builder.
    #[inline]
    pub fn references(&self) -> &[CellContainer<C>] {
        self.references.as_ref()
    }

    /// Tries to store a child in the cell,
    /// returning `false` if there is not enough remaining capacity.
    pub fn store_reference(&mut self, cell: CellContainer<C>) -> bool {
        if self.references.len() < MAX_REF_COUNT {
            // SAFETY: reference count is in the valid range
            unsafe { self.references.push(cell) }
            true
        } else {
            false
        }
    }

    /// Tries to append a builder (its data and references),
    /// returning `false` if there is not enough remaining capacity.
    pub fn store_builder(&mut self, builder: &Self) -> bool {
        if self.bit_len + builder.bit_len <= MAX_BIT_LEN
            && self.references.len() + builder.references.len() <= MAX_REF_COUNT
            && self.store_raw(&builder.data, builder.bit_len)
        {
            for cell in builder.references.as_ref() {
                if !self.store_reference(cell.clone()) {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }

    /// Tries to append a cell slice (its data and references),
    /// returning `false` if there is not enough remaining capacity.
    pub fn store_slice<'a>(&mut self, value: &CellSlice<'a, C>) -> bool {
        if self.bit_len + value.remaining_bits() <= MAX_BIT_LEN
            && self.references.len() + value.remaining_refs() as usize <= MAX_REF_COUNT
            && self.store_slice_data(value)
        {
            for cell in value.references().cloned() {
                if !self.store_reference(cell) {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }

    /// Tries to build a new cell using the specified finalizer.
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

        let cell_parts: CellParts<C> = CellParts {
            stats,
            bit_len: self.bit_len,
            descriptor: CellDescriptor { d1, d2 },
            children_mask,
            references: self.references,
            data,
        };
        finalizer.finalize_cell(cell_parts)
    }
}

impl<C> CellBuilder<C>
where
    for<'a> C: DefaultFinalizer + 'a,
{
    /// Tries to build a new cell using the default finalizer.
    ///
    /// See [`default_finalizer`]
    ///
    /// [`default_finalizer`]: fn@crate::cell::finalizer::DefaultFinalizer::default_finalizer
    pub fn build(self) -> Option<CellContainer<C>> {
        self.build_ext(&mut C::default_finalizer())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::RcCellFamily;

    type RcCellBuilder = CellBuilder<RcCellFamily>;

    #[test]
    fn clone_builder() {
        let mut builder = RcCellBuilder::new();
        assert!(builder.store_u32(0xdeafbeaf));
        let cell1 = builder.clone().build().unwrap();
        let cell2 = builder.clone().build().unwrap();
        assert_eq!(cell1.as_ref(), cell2.as_ref());

        builder.store_u32(0xb00b5);
        let cell3 = builder.build().unwrap();
        assert_ne!(cell1.as_ref(), cell3.as_ref());
    }

    #[test]
    #[cfg_attr(miri, ignore)] // takes too long to execute on miri
    fn store_raw() {
        const ONES: &[u8] = &[0xff; 128];
        for offset in 0..8 {
            for bits in 0..=1016 {
                let mut builder = RcCellBuilder::new();
                assert!(builder.store_zeros(offset));
                assert!(builder.store_raw(ONES, bits));
                builder.build().unwrap();
            }
        }
    }

    #[test]
    fn prepend_raw() {
        let mut builder = RcCellBuilder::new();
        assert!(builder.store_raw(&[0xde, 0xaf, 0xbe, 0xaf], 20));
        assert!(builder.prepend_raw(&[0xaa, 0x55], 5));
        let cell = builder.build().unwrap();
        println!("{}", cell.display_tree());
    }

    #[test]
    fn store_slice() {
        const SOME_HASH: &[u8; 32] = &[
            0xdf, 0x86, 0xce, 0xbc, 0xe8, 0xd5, 0xab, 0x0c, 0x69, 0xb4, 0xce, 0x33, 0xfe, 0x9b,
            0x0e, 0x2c, 0xdf, 0x69, 0xa3, 0xe1, 0x13, 0x7e, 0x64, 0x85, 0x6b, 0xbc, 0xfd, 0x39,
            0xe7, 0x9b, 0xc1, 0x6f,
        ];

        let mut builder = RcCellBuilder::new();
        assert!(builder.store_zeros(3));
        assert!(builder.store_u256(SOME_HASH));
        let cell = builder.build().unwrap();
        println!("{}", cell.display_tree());

        let mut builder = RcCellBuilder::new();
        let mut slice = cell.as_slice();
        assert!(slice.try_advance(3, 0));
        assert!(builder.store_slice(&slice));
        let cell = builder.build().unwrap();
        println!("{}", cell.display_tree());
        assert_eq!(cell.data(), SOME_HASH);
    }
}
