use super::level_mask::LevelMask;

#[derive(Hash, Debug, Clone, Copy)]
#[repr(C)]
pub struct CellDescriptor {
    pub d1: u8,
    pub d2: u8,
}

impl CellDescriptor {
    pub const REF_COUNT_MASK: u8 = 0b0000_0111;
    pub const IS_EXOTIC_MASK: u8 = 0b0000_1000;
    pub const STORE_HASHES_MASK: u8 = 0b0001_0000;
    pub const LEVEL_MASK: u8 = 0b1110_0000;

    #[inline(always)]
    pub const fn new(bytes: [u8; 2]) -> Self {
        Self {
            d1: bytes[0],
            d2: bytes[1],
        }
    }

    #[inline(always)]
    pub const fn reference_count(&self) -> usize {
        (self.d1 & Self::REF_COUNT_MASK) as usize
    }

    #[inline(always)]
    pub const fn is_exotic(&self) -> bool {
        self.d1 & Self::IS_EXOTIC_MASK != 0
    }

    #[inline(always)]
    pub const fn store_hashes(&self) -> bool {
        self.d1 & Self::STORE_HASHES_MASK != 0
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
