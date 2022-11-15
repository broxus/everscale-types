use super::level_mask::LevelMask;

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct CellDescriptor {
    pub d1: u8,
    pub d2: u8,
}

impl CellDescriptor {
    #[inline(always)]
    pub const fn new(bytes: [u8; 2]) -> Self {
        Self {
            d1: bytes[0],
            d2: bytes[1],
        }
    }

    #[inline(always)]
    pub const fn reference_count(&self) -> usize {
        (self.d1 & 0b111) as usize
    }

    #[inline(always)]
    pub const fn is_exotic(&self) -> bool {
        self.d1 & 0b1000 != 0
    }

    #[inline(always)]
    pub const fn store_hashes(&self) -> bool {
        self.d1 & 0b10000 != 0
    }

    #[inline(always)]
    pub const fn level_mask(&self) -> LevelMask {
        // SAFETY: `u8 >> 5` is always 3 bits long
        unsafe { LevelMask::new_unchecked(self.d1 >> 5) }
    }

    #[inline(always)]
    pub const fn is_aligned(&self) -> bool {
        self.d2 & 1 == 0
    }

    #[inline(always)]
    pub const fn byte_len(&self) -> u8 {
        (self.d2 & 1) + (self.d2 >> 1)
    }
}
