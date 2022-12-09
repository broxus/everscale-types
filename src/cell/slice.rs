use crate::cell::{Cell, CellContainer, CellFamily, CellType, LevelMask, RefsIter};

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
    pub fn is_data_empty(&self) -> bool {
        self.bits_window_start >= self.bits_window_end
    }

    /// Returns whether threre are no references left.
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
    #[inline]
    pub fn bits_offset(&self) -> u16 {
        self.bits_window_start
    }

    /// Tries to advance the start of the data window,
    /// returns `false` if `bits` is greater than the remainder.
    pub fn try_advance(&mut self, bits: u16) -> bool {
        if self.bits_window_start + bits <= self.bits_window_end {
            self.bits_window_start += bits;
            true
        } else {
            false
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
    pub fn get_next_bit(&mut self) -> Option<bool> {
        if self.bits_window_start < self.bits_window_end {
            let index = self.bits_window_start;
            let byte = *self.cell.data().get((index / 8) as usize)?;
            self.bits_window_start += 1;
            Some((byte >> (7 - index % 8)) & 1 != 0)
        } else {
            None
        }
    }

    /// Returns a small subset of `bits` (0..=8) starting from the `offset`.
    pub fn get_bits(&self, offset: u16, bits: u8) -> Option<u8> {
        debug_assert!(bits <= 8);

        let bits = bits as u16;
        if self.bits_window_start + offset + bits <= self.bits_window_end {
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
    #[inline]
    pub fn get_next_bits(&mut self, bits: u8) -> Option<u8> {
        let res = self.get_bits(0, bits)?;
        self.bits_window_start += bits as u16;
        Some(res)
    }

    /// Reads `u8` starting from the `offset`.
    #[inline]
    pub fn get_u8(&self, offset: u16) -> Option<u8> {
        self.get_bits(offset, 8)
    }

    /// Tries to read the next `u8`, incrementing the bits window start.
    #[inline]
    pub fn get_next_u8(&mut self) -> Option<u8> {
        self.get_next_bits(8)
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
    pub fn get_next_u16(&mut self) -> Option<u16> {
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
    pub fn get_next_u32(&mut self) -> Option<u32> {
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
    pub fn get_next_u64(&mut self) -> Option<u64> {
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
    pub fn get_next_u128(&mut self) -> Option<u128> {
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
    pub fn get_next_u256(&mut self) -> Option<[u8; 32]> {
        let res = self.get_u256(0)?;
        self.bits_window_start += 256;
        Some(res)
    }

    /// Returns a reference to the Nth child cell (relative to this slice's refs window).
    pub fn reference(&self, index: u8) -> Option<&dyn Cell<C>> {
        if self.refs_window_start + index < self.refs_window_end {
            self.cell.reference(self.refs_window_start + index)
        } else {
            None
        }
    }

    /// Returns the Nth child cell (relative to this slice's refs window).
    pub fn reference_cloned(&self, index: u8) -> Option<CellContainer<C>> {
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

    /// Returns a reference to the next child cell (relative to this slice's refs window),
    /// incrementing the refs window start.
    pub fn get_next_reference(&mut self) -> Option<&dyn Cell<C>> {
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
    pub fn get_next_reference_cloned(&mut self) -> Option<CellContainer<C>> {
        if self.refs_window_start < self.refs_window_end {
            let cell = self.cell.reference_cloned(self.refs_window_start)?;
            self.refs_window_start += 1;
            Some(cell)
        } else {
            None
        }
    }
}
