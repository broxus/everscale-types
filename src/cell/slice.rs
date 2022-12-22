use crate::cell::{Cell, CellContainer, CellFamily, CellType, LevelMask, RefsIter};

pub trait Load<'a, C: CellFamily>: Sized {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self>;
}

macro_rules! impl_primitive_loads {
    ($($type:ty => |$s:ident| $expr:expr),*$(,)?) => {
        $(impl<C: CellFamily> Load<'_, C> for $type {
            #[inline]
            fn load_from($s: &mut CellSlice<C>) -> Option<Self> {
                $expr
            }
        })*
    };
}

impl_primitive_loads! {
    bool => |s| s.load_bit(),
    u8 => |s| s.load_u8(),
    i8 => |s| Some(s.load_u8()? as i8),
    u16 => |s| s.load_u16(),
    i16 => |s| Some(s.load_u16()? as i16),
    u32 => |s| s.load_u32(),
    i32 => |s| Some(s.load_u32()? as i32),
    u64 => |s| s.load_u64(),
    i64 => |s| Some(s.load_u64()? as i64),
    u128 => |s| s.load_u128(),
    i128 => |s| Some(s.load_u128()? as i128),
}

impl<'a, C: CellFamily> Load<'a, C> for &'a dyn Cell<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        slice.load_reference()
    }
}

/// A read-only view for a subcell of a cell
#[derive(Debug)]
pub struct CellSlice<'a, C: CellFamily> {
    cell: &'a dyn Cell<C>,
    bits_window_start: u16,
    bits_window_end: u16,
    refs_window_start: u8,
    refs_window_end: u8,
}

impl<'a, C: CellFamily> Clone for CellSlice<'a, C> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            cell: self.cell,
            bits_window_start: self.bits_window_start,
            bits_window_end: self.bits_window_end,
            refs_window_start: self.refs_window_start,
            refs_window_end: self.refs_window_end,
        }
    }
}

impl<'a, C: CellFamily> Copy for CellSlice<'a, C> {}

impl<'a, C: CellFamily> CellSlice<'a, C> {
    /// Constructs a new cell slice from the specified cell.
    pub fn new(cell: &'a dyn Cell<C>) -> Self {
        Self {
            bits_window_start: 0,
            bits_window_end: cell.bit_len(),
            refs_window_start: 0,
            refs_window_end: cell.reference_count(),
            cell,
        }
    }

    /// Returns a reference to the underlying cell.
    #[inline]
    pub fn cell(&self) -> &'a dyn Cell<C> {
        self.cell
    }

    /// Computes cell type from descriptor bytes.
    #[inline]
    pub fn cell_type(&self) -> CellType {
        self.cell.cell_type()
    }

    /// Computes the cell level from the level mask.
    #[inline]
    pub fn level(&self) -> u8 {
        self.cell.level()
    }

    /// Computes the level mask from the descriptor bytes.
    #[inline]
    pub fn level_mask(&self) -> LevelMask {
        self.cell.level_mask()
    }

    /// Returns whether there are no bits of data left.
    ///
    /// # Examples
    ///
    /// ```
    /// # use everscale_types::{CellFamily, RcCellBuilder, RcCellFamily};
    /// // Cell with empty data
    /// let empty_cell = RcCellFamily::empty_cell();
    /// assert!(empty_cell.as_slice().is_data_empty());
    ///
    /// // Cell with some bits in data
    /// let not_empty_cell = {
    ///     let mut builder = RcCellBuilder::new();
    ///     builder.store_bit_zero();
    ///     builder.build().unwrap()
    /// };
    /// assert!(!not_empty_cell.as_slice().is_data_empty());
    /// ```
    pub fn is_data_empty(&self) -> bool {
        self.bits_window_start >= self.bits_window_end
    }

    /// Returns whether threre are no references left.
    ///
    /// # Examples
    ///
    /// ```
    /// # use everscale_types::{CellFamily, RcCellBuilder, RcCellFamily};
    /// // Cell without references
    /// let empty_cell = RcCellFamily::empty_cell();
    /// assert!(empty_cell.as_slice().is_refs_empty());
    ///
    /// // Cell with some references
    /// let not_empty_cell = {
    ///     let mut builder = RcCellBuilder::new();
    ///     builder.store_reference(empty_cell);
    ///     builder.build().unwrap()
    /// };
    /// assert!(!not_empty_cell.as_slice().is_refs_empty());
    /// ```
    pub fn is_refs_empty(&self) -> bool {
        self.refs_window_start >= self.refs_window_end
    }

    /// Returns the number of remaining references in the slice.
    pub fn remaining_refs(&self) -> u8 {
        if self.refs_window_start > self.refs_window_end {
            0
        } else {
            self.refs_window_end - self.refs_window_start
        }
    }

    /// Returns the number of remaining bits of data in the slice.
    pub fn remaining_bits(&self) -> u16 {
        if self.bits_window_start > self.bits_window_end {
            0
        } else {
            self.bits_window_end - self.bits_window_start
        }
    }

    /// Returns the start of the data window.
    ///
    /// # Examples
    ///
    /// ```
    /// # use everscale_types::RcCellBuilder;
    /// let cell = {
    ///     let mut builder = RcCellBuilder::new();
    ///     builder.store_zeros(100);
    ///     builder.build().unwrap()
    /// };
    /// let mut slice = cell.as_slice();
    ///
    /// _ = slice.load_u8();
    /// assert_eq!(slice.bits_offset(), 8);
    /// ```
    #[inline]
    pub fn bits_offset(&self) -> u16 {
        self.bits_window_start
    }

    /// Returns the start of the references window.
    ///
    /// # Examples
    ///
    /// ```
    /// # use everscale_types::{CellFamily, RcCellBuilder, RcCellFamily};
    /// let cell = {
    ///     let mut builder = RcCellBuilder::new();
    ///     builder.store_reference(RcCellFamily::empty_cell());
    ///     builder.build().unwrap()
    /// };
    /// let mut slice = cell.as_slice();
    ///
    /// _ = slice.load_reference();
    /// assert_eq!(slice.refs_offset(), 1);
    /// ```
    #[inline]
    pub fn refs_offset(&self) -> u8 {
        self.refs_window_start
    }

    /// Returns true if the slice contains at least `bits` and `refs`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use everscale_types::{CellFamily, RcCellBuilder, RcCellFamily};
    /// let cell = {
    ///     let mut builder = RcCellBuilder::new();
    ///     builder.store_zeros(100);
    ///     builder.store_reference(RcCellFamily::empty_cell());
    ///     builder.store_reference(RcCellFamily::empty_cell());
    ///     builder.build().unwrap()
    /// };
    /// let mut slice = cell.as_slice();
    ///
    /// assert!(slice.has_remaining(10, 2));
    /// assert!(!slice.has_remaining(500, 2)); // too many bits
    /// assert!(!slice.has_remaining(0, 4)); // too many refs
    /// ```
    #[inline]
    pub fn has_remaining(&self, bits: u16, refs: u8) -> bool {
        self.bits_window_start + bits <= self.bits_window_end
            && self.refs_window_start + refs <= self.refs_window_end
    }

    /// Tries to advance the start of data and refs windows,
    /// returns `false` if `bits` or `refs` are greater than the remainder.
    pub fn try_advance(&mut self, bits: u16, refs: u8) -> bool {
        if self.bits_window_start + bits <= self.bits_window_end
            && self.refs_window_start + refs <= self.refs_window_end
        {
            self.bits_window_start += bits;
            self.refs_window_start += refs;
            true
        } else {
            false
        }
    }

    /// Returns a slice starting at the same bits and refs offsets,
    /// and containing no more than `bits` of data and `refs` of children.
    pub fn get_prefix(&self, bits: u16, refs: u8) -> Self {
        Self {
            cell: self.cell,
            bits_window_start: self.bits_window_start,
            bits_window_end: std::cmp::min(self.bits_window_start + bits, self.bits_window_end),
            refs_window_start: self.refs_window_start,
            refs_window_end: std::cmp::min(self.refs_window_start + refs, self.refs_window_end),
        }
    }

    /// Returns a subslice with the data prefix removed.
    ///
    /// If the slice starts with `prefix`, returns the subslice after the prefix, wrapped in `Some`.
    /// If `prefix` is empty, simply returns the original slice.
    ///
    /// If the slice does not start with `prefix`, returns `None`.
    pub fn strip_data_prefix(&self, prefix: &Self) -> Option<Self> {
        let prefix_len = prefix.remaining_bits();
        if prefix_len == 0 {
            return Some(*self);
        } else if self.remaining_bits() < prefix_len {
            return None;
        } else {
            let mut result = *self;
            let lcp = self.longest_common_data_prefix(prefix);
            if prefix_len <= lcp.remaining_bits() && result.try_advance(prefix_len, 0) {
                Some(result)
            } else {
                None
            }
        }
    }

    /// Returns the longest common data prefix.
    ///
    /// NOTE: The returned subslice will be a subslice of the current slice.
    pub fn longest_common_data_prefix(&self, other: &Self) -> Self {
        /// XOR  | BITS
        /// 0000 | 4
        /// 0001 | 3
        /// 001x | 2
        /// 01xx | 1
        /// 1xxx | 0
        const BITS: [u8; 16] = [4, 3, 2, 2, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0];

        if self.bits_window_start >= self.bits_window_end
            || other.bits_window_start >= other.bits_window_end
        {
            return *self;
        }
        let mut self_remaining_bits = self.bits_window_end - self.bits_window_start;
        let self_data = self.cell.data();
        let mut other_remaining_bits = other.bits_window_end - other.bits_window_start;
        let other_data = other.cell.data();
        let mut max_bit_len = std::cmp::min(self_remaining_bits, other_remaining_bits);

        let self_r = self.bits_window_start % 8;
        let self_q = (self.bits_window_start / 8) as usize;
        let other_r = other.bits_window_start % 8;
        let other_q = (other.bits_window_start / 8) as usize;

        // Handle case with possibly incorrect data
        if self_remaining_bits

        unsafe {
            let mut self_data_ptr = self_data.as_ptr().add(self_q);
            let mut other_data_ptr = other_data.as_ptr().add(other_q);

            let self_first_byte = *self_data_ptr;
            let other_first_byte = *other_data_ptr;

            let self_first_byte_mask: u8 = 0xff >> self_r;
            let other_first_byte_mask: u8 = 0xff >> other_r;

            // ___xxxxx|xxxx....
            // ___yyyyy|yyyy....

            // ___xxxxx|xxxx...
            // ______yy|yyyy...

            // ______xx|xxxx...
            // ___yyyyy|xxxx...

            /*
            match key1[i] ^ key2[i] {
                0 => result += 8,
                x => {
                    if x & 0xf0 == 0 {
                        result += BITS[(x & 0x0f) as usize] + 4;
                    } else {
                        result += BITS[(x >> 4) as usize]
                    }
                    break;
                }
            }
            */

            let last_byte_mask: u8 = 0xff << (8 - (remaining_bits + r) % 8);

            if r + remaining_bits <= 8 {
                // Special case if all remaining_bits are in the first byte
                if ((first_byte ^ target) & first_byte_mask & last_byte_mask) != 0 {
                    return None;
                }
            } else {
                // Check the first byte
                if (first_byte ^ target) & first_byte_mask != 0 {
                    return None;
                }

                // Check all full bytes
                remaining_bits -= 8 - r;
                for _ in 0..(remaining_bits / 8) {
                    data_ptr = data_ptr.add(1);
                    if *data_ptr != target {
                        return None;
                    }
                }

                // Check the last byte (if not aligned)
                if remaining_bits % 8 != 0 {
                    data_ptr = data_ptr.add(1);
                    if (*data_ptr ^ target) & last_byte_mask != 0 {
                        return None;
                    }
                }
            }

            Some(target != 0)
        }
    }

    /// Checks whether the current slice consists of the same bits,
    /// returns `None` if there are 0s and 1s, returns `Some(bit)` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// # use everscale_types::{CellFamily, RcCellBuilder, RcCellFamily};
    /// // Uniform cell consisting of only 0s
    /// let uniform_cell = {
    ///     let mut builder = RcCellBuilder::new();
    ///     builder.store_zeros(10);
    ///     builder.build().unwrap()
    /// };
    /// assert_eq!(uniform_cell.as_slice().test_uniform(), Some(false));
    ///
    /// // Non-uniform cell consisting of 0s and 1s
    /// let non_uniform_cell = {
    ///     let mut builder = RcCellBuilder::new();
    ///     builder.store_zeros(9);
    ///     builder.store_bit_true();
    ///     builder.build().unwrap()
    /// };
    /// assert_eq!(non_uniform_cell.as_slice().test_uniform(), None);
    ///
    /// // Empty cell is non-uniform
    /// let non_uniform_cell = RcCellFamily::empty_cell();
    /// assert_eq!(non_uniform_cell.as_slice().test_uniform(), None);
    /// ```
    pub fn test_uniform(&self) -> Option<bool> {
        if self.bits_window_start >= self.bits_window_end {
            return None;
        }
        let mut remaining_bits = self.bits_window_end - self.bits_window_start;
        let data = self.cell.data();

        // Check if data is enough
        if (self.bits_window_end + 7) / 8 < data.len() as u16 {
            return None;
        }

        let r = self.bits_window_start % 8;
        let q = (self.bits_window_start / 8) as usize;

        unsafe {
            let mut data_ptr = data.as_ptr().add(q);
            let first_byte = *data_ptr;

            let target = ((first_byte >> (7 - r)) & 1) * u8::MAX;
            let first_byte_mask: u8 = 0xff >> r;
            let last_byte_mask: u8 = 0xff << (8 - (remaining_bits + r) % 8);

            if r + remaining_bits <= 8 {
                // Special case if all remaining_bits are in the first byte
                if ((first_byte ^ target) & first_byte_mask & last_byte_mask) != 0 {
                    return None;
                }
            } else {
                // Check the first byte
                if (first_byte ^ target) & first_byte_mask != 0 {
                    return None;
                }

                // Check all full bytes
                remaining_bits -= 8 - r;
                for _ in 0..(remaining_bits / 8) {
                    data_ptr = data_ptr.add(1);
                    if *data_ptr != target {
                        return None;
                    }
                }

                // Check the last byte (if not aligned)
                if remaining_bits % 8 != 0 {
                    data_ptr = data_ptr.add(1);
                    if (*data_ptr ^ target) & last_byte_mask != 0 {
                        return None;
                    }
                }
            }

            Some(target != 0)
        }
    }

    /// Tries to read the bit at the specified offset (relative to the current bits window).
    pub fn get_bit(&self, offset: u16) -> Option<bool> {
        if self.bits_window_start + offset < self.bits_window_end {
            let index = self.bits_window_start + offset;
            let byte = *self.cell.data().get((index / 8) as usize)?;
            Some((byte >> (7 - index % 8)) & 1 != 0)
        } else {
            None
        }
    }

    /// Tries to read the next bit, incrementing the bits window start.
    pub fn load_bit(&mut self) -> Option<bool> {
        if self.bits_window_start < self.bits_window_end {
            let index = self.bits_window_start;
            let byte = *self.cell.data().get((index / 8) as usize)?;
            self.bits_window_start += 1;
            Some((byte >> (7 - index % 8)) & 1 != 0)
        } else {
            None
        }
    }

    /// Reads `u8` starting from the `offset`.
    #[inline]
    pub fn get_u8(&self, offset: u16) -> Option<u8> {
        self.get_small_uint(offset, 8)
    }

    /// Tries to read the next `u8`, incrementing the bits window start.
    #[inline]
    pub fn load_u8(&mut self) -> Option<u8> {
        self.load_small_uint(8)
    }

    /// Reads `u16` starting from the `offset`.
    pub fn get_u16(&self, offset: u16) -> Option<u16> {
        if self.bits_window_start + offset + 16 <= self.bits_window_end {
            let index = self.bits_window_start + offset;
            let data = self.cell.data();
            let data_len = data.len();

            let r = index % 8;
            let q = (index / 8) as usize;

            if r == 0 && q + 2 <= data_len {
                // xxxxxxxx|yyyyyyyy -> xxxxxxxx|yyyyyyyy
                //^r

                // SAFETY: `q + 2 <= data_len`
                Some(u16::from_be_bytes(unsafe {
                    *(data.as_ptr().add(q) as *const [u8; 2])
                }))
            } else if r != 0 && q + 3 <= data_len {
                // ___xxxxx|yyyyyyyy|zzz_____ -> xxxxxyyy|yyyyyzzz
                //  r^

                let mut bytes = [0u8; 4];

                // SAFETY: `q + 3 <= data_len`
                unsafe {
                    std::ptr::copy_nonoverlapping(
                        data.as_ptr().add(q),
                        bytes.as_mut_ptr().add(1),
                        3,
                    );
                };

                let res = u32::from_be_bytes(bytes);
                Some((res >> (8 - r)) as u16)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Tries to read the next `u16`, incrementing the bits window start.
    #[inline]
    pub fn load_u16(&mut self) -> Option<u16> {
        let res = self.get_u16(0)?;
        self.bits_window_start += 16;
        Some(res)
    }

    /// Reads `u32` starting from the `offset`.
    pub fn get_u32(&self, offset: u16) -> Option<u32> {
        if self.bits_window_start + offset + 32 <= self.bits_window_end {
            let index = self.bits_window_start + offset;
            let data = self.cell.data();
            let data_len = data.len();

            let r = index % 8;
            let q = (index / 8) as usize;

            if r == 0 && q + 4 <= data_len {
                // xxxxxxxx|yyyyyyyy|zzzzzzzz|wwwwwwww -> xxxxxxxx|yyyyyyyy|zzzzzzzz|wwwwwwww
                //^r

                // SAFETY: `q + 4 <= data_len`
                Some(u32::from_be_bytes(unsafe {
                    *(data.as_ptr().add(q) as *const [u8; 4])
                }))
            } else if r != 0 && q + 5 <= data_len {
                // ___xxxxx|yyyyyyyy|zzz_____ -> xxxxxyyy|yyyyyzzz
                //  r^

                let mut bytes = [0u8; 8];

                // SAFETY: `q + 5 <= data_len`
                unsafe {
                    std::ptr::copy_nonoverlapping(
                        data.as_ptr().add(q),
                        bytes.as_mut_ptr().add(3),
                        5,
                    );
                };

                let res = u64::from_be_bytes(bytes);
                Some((res >> (8 - r)) as u32)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Tries to read the next `u32`, incrementing the bits window start.
    #[inline]
    pub fn load_u32(&mut self) -> Option<u32> {
        let res = self.get_u32(0)?;
        self.bits_window_start += 32;
        Some(res)
    }

    /// Reads `u64` starting from the `offset`.
    pub fn get_u64(&self, offset: u16) -> Option<u64> {
        if self.bits_window_start + offset + 64 <= self.bits_window_end {
            let index = self.bits_window_start + offset;
            let data = self.cell.data();
            let data_len = data.len();

            let r = index % 8;
            let q = (index / 8) as usize;

            if r == 0 && q + 8 <= data_len {
                // SAFETY: `q + 8 <= data_len`
                Some(u64::from_be_bytes(unsafe {
                    *(data.as_ptr().add(q) as *const [u8; 8])
                }))
            } else if r != 0 && q + 9 <= data_len {
                // ___xxxxx|...|zzz_____ -> xxxxx...|...zzz
                //  r^

                let mut bytes = [0u8; 16];

                // SAFETY: `q + 9 <= data_len`
                unsafe {
                    std::ptr::copy_nonoverlapping(
                        data.as_ptr().add(q),
                        bytes.as_mut_ptr().add(7),
                        9,
                    );
                };

                let res = u128::from_be_bytes(bytes);
                Some((res >> (8 - r)) as u64)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Tries to read the next `u64`, incrementing the bits window start.
    #[inline]
    pub fn load_u64(&mut self) -> Option<u64> {
        let res = self.get_u64(0)?;
        self.bits_window_start += 64;
        Some(res)
    }

    /// Reads `u128` starting from the `offset`.
    pub fn get_u128(&self, offset: u16) -> Option<u128> {
        if self.bits_window_start + offset + 128 <= self.bits_window_end {
            let index = self.bits_window_start + offset;
            let data = self.cell.data();
            let data_len = data.len();

            let r = index % 8;
            let q = (index / 8) as usize;

            if r == 0 && q + 16 <= data_len {
                // SAFETY: `q + 16 <= data_len`
                Some(u128::from_be_bytes(unsafe {
                    *(data.as_ptr().add(q) as *const [u8; 16])
                }))
            } else if r != 0 && q + 17 <= data_len {
                // ___xxxxx|...|zzz_____ -> xxxxx...|...zzz
                //  r^

                let mut bytes = [0u8; 17];

                // SAFETY: `q + 17 <= data_len`
                unsafe {
                    std::ptr::copy_nonoverlapping(data.as_ptr().add(q), bytes.as_mut_ptr(), 17);
                };

                let res = u128::from_be_bytes(bytes[1..].try_into().unwrap());
                Some(((bytes[0] as u128) << (120 + r)) | (res >> (8 - r)))
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Tries to read the next `u128`, incrementing the bits window start.
    #[inline]
    pub fn load_u128(&mut self) -> Option<u128> {
        let res = self.get_u128(0)?;
        self.bits_window_start += 128;
        Some(res)
    }

    /// Reads 32 bytes starting from the `offset`.
    pub fn get_u256(&self, offset: u16) -> Option<[u8; 32]> {
        if self.bits_window_start + offset + 256 <= self.bits_window_end {
            let index = self.bits_window_start + offset;
            let data = self.cell.data();
            let data_len = data.len();

            let r = index % 8;
            let q = (index / 8) as usize;

            if r == 0 && q + 32 <= data_len {
                // SAFETY: `q + 32 <= data_len`
                Some(unsafe { *(data.as_ptr().add(q) as *const [u8; 32]) })
            } else if r != 0 && q + 33 <= data_len {
                // ___xxxxx|...|zzz_____ -> xxxxx...|...zzz
                //  r^

                let shift = 8 - r;
                let rev_shift = 120 + r;

                // SAFETY: `q + 33 <= data_len`
                unsafe {
                    let mut bytes = [0u8; 33];
                    std::ptr::copy_nonoverlapping(data.as_ptr().add(q), bytes.as_mut_ptr(), 33);

                    // Interpret last 32 bytes as two u128
                    let [ovf, bytes @ ..] = bytes;
                    let [mut hi, mut lo]: [u128; 2] = std::mem::transmute(bytes);

                    // Numbers are in big endian order, swap bytes on little endian arch
                    #[cfg(target_endian = "little")]
                    {
                        hi = hi.swap_bytes();
                        lo = lo.swap_bytes();
                    }

                    // Shift right, putting `ovf` to the high bits
                    Some(std::mem::transmute([
                        (hi >> shift | ((ovf as u128) << rev_shift)).to_be_bytes(),
                        (lo >> shift | (hi << rev_shift)).to_be_bytes(),
                    ]))
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Tries to read the next 32 bytes, incrementing the bits window start.
    #[inline]
    pub fn load_u256(&mut self) -> Option<[u8; 32]> {
        let res = self.get_u256(0)?;
        self.bits_window_start += 256;
        Some(res)
    }

    /// Returns a small subset of `bits` (0..=8) starting from the `offset`.
    ///
    /// NOTE: Reading zero bits always succeeds,
    /// and reading more than 8 bits always fails.
    pub fn get_small_uint(&self, offset: u16, bits: u16) -> Option<u8> {
        if bits == 0 {
            return Some(0);
        }

        if bits <= 8 && self.bits_window_start + offset + bits <= self.bits_window_end {
            let index = self.bits_window_start + offset;

            let r = index % 8;
            let q = (index / 8) as usize;
            let byte = *self.cell.data().get(q)?;

            if r == 0 {
                // xxx_____ -> _____xxx
                //^r
                Some(byte >> (8 - bits))
            } else if bits <= (8 - r) {
                // __xxx___ -> _____xxx
                // r^
                Some((byte >> (8 - r - bits)) & ((1 << bits) - 1))
            } else {
                // ______xx|y_______ -> _____xxy
                //     r^

                let mut res = (byte as u16) << 8;
                res |= *self.cell.data().get(q + 1)? as u16;
                Some((res >> (8 - r)) as u8 >> (8 - bits))
            }
        } else {
            None
        }
    }

    /// Tries to read the next small subset of `bits` (0..=8), incrementing the bits window start.
    ///
    /// NOTE: Reading zero bits always succeeds,
    /// and reading more than 8 bits always fails.
    #[inline]
    pub fn load_small_uint(&mut self, bits: u16) -> Option<u8> {
        let res = self.get_small_uint(0, bits)?;
        self.bits_window_start += bits;
        Some(res)
    }

    /// Reads `u64` from the cell (but only the specified number of bits)
    /// starting from the `offset`.
    ///
    /// NOTE: Reading zero bits always succeeds,
    /// and reading more than 64 bits always fails.
    pub fn get_uint(&mut self, offset: u16, mut bits: u16) -> Option<u64> {
        if bits == 0 {
            return Some(0);
        }

        if bits <= 64 && self.bits_window_start + offset + bits <= self.bits_window_end {
            let index = self.bits_window_start + offset;
            let data = self.cell.data();
            let data_len = data.len();

            // Check if data is enough
            if (self.bits_window_end + 7) / 8 < data_len as u16 {
                return None;
            }

            let r = index % 8;
            let q = (index / 8) as usize;

            unsafe {
                let data_ptr = data.as_ptr().add(q);
                let first_byte = *data_ptr & (0xff >> r);

                let right_shift = 8 - (bits + r) % 8;

                if r + bits <= 8 {
                    // Special case if all remaining_bits are in the first byte
                    Some((first_byte >> right_shift) as u64)
                } else {
                    let mut bytes = [0u8; 8];

                    // Copy remaining bytes
                    bits -= 8 - r;
                    std::ptr::copy_nonoverlapping(
                        data_ptr.add(1),
                        bytes.as_mut_ptr(),
                        ((bits + 7) / 8) as usize,
                    );

                    let mut result = u64::from_be_bytes(bytes) >> (64 - bits);
                    result |= (first_byte as u64) << bits;
                    Some(result)
                }
            }
        } else {
            None
        }
    }

    /// Tries to read the next `u64` (but only the specified number of bits),
    /// incrementing the bits window start.
    ///
    /// NOTE: Reading zero bits always succeeds,
    /// and reading more than 64 bits always fails.
    #[inline]
    pub fn load_uint(&mut self, bits: u16) -> Option<u64> {
        let res = self.get_uint(0, bits)?;
        self.bits_window_start += bits;
        Some(res)
    }

    /// Reads the specified number of bits to the taret starting from the `offset`.
    pub fn get_raw<'b>(
        &'_ self,
        offset: u16,
        target: &'b mut [u8],
        bits: u16,
    ) -> Option<&'b mut [u8]> {
        if bits == 0 {
            return Some(&mut target[..0]);
        }

        if self.bits_window_start + bits <= self.bits_window_end {
            let index = self.bits_window_start + offset;
            let data = self.cell.data();
            let data_len = data.len();

            let target_len = ((bits + 7) / 8) as usize;
            let target = if target_len <= target.len() {
                &mut target[..target_len]
            } else {
                return None;
            };

            let r = index % 8;
            let q = (index / 8) as usize;

            // SAFETY: q will be checked to be in range 0..data_len,
            // r is in range 0..=7, target is guaranteed to be `target_len`
            unsafe {
                let mut data_ptr = data.as_ptr().add(q);
                let target_ptr = target.as_mut_ptr();

                if r == 0 && q + target_len <= data_len {
                    std::ptr::copy_nonoverlapping(data_ptr, target_ptr, target_len);
                } else if r != 0 {
                    let byte_len = ((bits + r + 7) / 8) as usize - 1;
                    if q + byte_len > data_len {
                        return None;
                    }

                    let shift = 8 - r;
                    for i in 0..byte_len {
                        let target = target_ptr.add(i);
                        *target = *data_ptr << r;
                        data_ptr = data_ptr.add(1);
                        *target |= *data_ptr >> shift;
                    }
                    if byte_len < target_len {
                        *target_ptr.add(byte_len) = *data_ptr << r;
                    }
                } else {
                    return None;
                }

                let bits_r = bits % 8;
                if bits_r != 0 {
                    *target_ptr.add(target_len - 1) &= 0xff << (8 - bits_r);
                }
                Some(target)
            }
        } else {
            None
        }
    }

    /// Tries to read the specified number of bits, incrementing the bits window start.
    /// Returns the minimum subslice containing all bits.
    pub fn load_raw<'b>(&'_ mut self, target: &'b mut [u8], bits: u16) -> Option<&'b mut [u8]> {
        let res = self.get_raw(0, target, bits)?;
        self.bits_window_start += bits;
        Some(res)
    }

    /// Returns a reference to the Nth child cell (relative to this slice's refs window).
    pub fn get_reference(&self, index: u8) -> Option<&dyn Cell<C>> {
        if self.refs_window_start + index < self.refs_window_end {
            self.cell.reference(self.refs_window_start + index)
        } else {
            None
        }
    }

    /// Returns the Nth child cell (relative to this slice's refs window).
    pub fn get_reference_cloned(&self, index: u8) -> Option<CellContainer<C>> {
        if self.refs_window_start + index < self.refs_window_end {
            self.cell.reference_cloned(self.refs_window_start + index)
        } else {
            None
        }
    }

    /// Creates an iterator through child nodes.
    pub fn references(&self) -> RefsIter<'a, C> {
        RefsIter {
            cell: self.cell,
            len: self.refs_window_end - self.refs_window_start,
            index: self.refs_window_start,
        }
    }

    /// Converts this slice into an iterator through child nodes.
    #[inline]
    pub fn into_references(self) -> RefsIter<'a, C> {
        self.references()
    }

    /// Returins this slice, but with references skipped.
    #[inline]
    pub fn without_references(mut self) -> Self {
        self.refs_window_start = self.refs_window_end;
        self
    }

    /// Returns a reference to the next child cell (relative to this slice's refs window),
    /// incrementing the refs window start.
    pub fn load_reference(&mut self) -> Option<&'a dyn Cell<C>> {
        if self.refs_window_start < self.refs_window_end {
            let cell = self.cell.reference(self.refs_window_start)?;
            self.refs_window_start += 1;
            Some(cell)
        } else {
            None
        }
    }

    /// Returns the next child cell (relative to this slice's refs window),
    /// incrementing the refs window start.
    pub fn load_reference_cloned(&mut self) -> Option<CellContainer<C>> {
        if self.refs_window_start < self.refs_window_end {
            let cell = self.cell.reference_cloned(self.refs_window_start)?;
            self.refs_window_start += 1;
            Some(cell)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::RcCellBuilder;

    #[test]
    #[cfg_attr(miri, ignore)] // takes too long to execute on miri
    fn get_raw() {
        let cell = RcCellBuilder::from_raw_data(&[0xff; 128], 200)
            .and_then(RcCellBuilder::build)
            .unwrap();
        let slice = cell.as_slice();

        let mut data = [0; 1];
        assert!(slice.get_raw(0, &mut data, 100).is_none());

        let mut data = [0; 64];
        assert!(slice.get_raw(0, &mut data, 500).is_none());

        let cell = RcCellBuilder::from_raw_data(&[0xff; 128], 1023)
            .and_then(RcCellBuilder::build)
            .unwrap();
        let slice = cell.as_slice();

        let mut data = [0; 128];
        for offset in 0..=8 {
            for bits in 0..=(1023 - offset) {
                slice.get_raw(offset, &mut data, bits).unwrap();
            }
        }
    }

    #[test]
    fn get_uint() {
        let cell = {
            let mut builder = RcCellBuilder::new();
            builder.store_u64(0xfafafafafafafafa);
            builder.build().unwrap()
        };

        let mut slice = cell.as_slice();
        assert_eq!(slice.get_uint(0, 3), Some(0b111));
        assert_eq!(slice.get_uint(0, 11), Some(0b11111010111));
        assert_eq!(slice.get_uint(1, 11), Some(0b11110101111));
        assert_eq!(slice.get_uint(8, 3), Some(0b111));
    }

    #[test]
    fn test_uniform() {
        let cell = {
            let mut builder = RcCellBuilder::new();
            builder.store_zeros(10);
            builder.build().unwrap()
        };
        assert_eq!(cell.as_slice().test_uniform(), Some(false));

        let cell = {
            let mut builder = RcCellBuilder::new();
            builder.store_zeros(9);
            builder.store_bit_true();
            builder.build().unwrap()
        };
        assert_eq!(cell.as_slice().test_uniform(), None);

        let cell = {
            let mut builder = RcCellBuilder::new();
            builder.store_zeros(20);
            builder.store_bit_true();
            builder.build().unwrap()
        };
        assert_eq!(cell.as_slice().test_uniform(), None);

        let cell = {
            let mut builder = RcCellBuilder::new();
            builder.store_bit_zero();
            builder.store_uint(u64::MAX, 29);
            builder.build().unwrap()
        };
        let mut slice = cell.as_slice();
        slice.try_advance(1, 0);
        assert_eq!(slice.test_uniform(), Some(true));
    }
}
