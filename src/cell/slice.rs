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
                // ______xx|x_______ -> _____xxx
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
    pub fn get_next_bits(&mut self, bits: u8) -> Option<u8> {
        let res = self.get_bits(0, bits)?;
        self.bits_window_start += bits as u16;
        Some(res)
    }

    /// Tries to read the next `u8`, incrementing the bits windows start.
    #[inline]
    pub fn get_next_u8(&mut self) -> Option<u8> {
        self.get_next_bits(8)
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
