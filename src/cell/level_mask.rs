use std::ops::{BitOr, BitOrAssign};

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct LevelMask(u8);

impl LevelMask {
    pub const EMPTY: Self = LevelMask(0);

    /// Constructs new level mask, truncating extra bits
    #[inline(always)]
    pub const fn new(mask: u8) -> Self {
        Self(mask & 0b111)
    }

    /// # Safety
    /// Mask must be in range `0b000..=0b111`
    #[inline(always)]
    pub const unsafe fn new_unchecked(mask: u8) -> Self {
        Self(mask)
    }

    /// Creates a sufficient mask for the specified level
    ///
    /// NOTE: levels > 3 has no effect (mask will always be `0b111`)
    #[inline(always)]
    pub const fn from_level(level: u8) -> Self {
        Self(match level {
            0 => 0,
            1 => 1,
            2 => 3,
            _ => 7,
        })
    }

    /// Counts presented higher hashes
    pub const fn level(&self) -> u8 {
        (self.0 & 1) + ((self.0 >> 1) & 1) + ((self.0 >> 2) & 1)
    }

    /// Computes hash index for the specified level
    pub const fn hash_index(&self, level: u8) -> u8 {
        Self(self.0 & Self::from_level(level).0).level()
    }

    /// Creates a new mask, shifted by the offset
    #[inline(always)]
    pub const fn virtualize(&self, offset: u8) -> Self {
        Self(self.0 >> offset)
    }
}

impl PartialEq<u8> for LevelMask {
    fn eq(&self, other: &u8) -> bool {
        self.0 == *other
    }
}

impl BitOr for LevelMask {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for LevelMask {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl From<LevelMask> for u8 {
    #[inline(always)]
    fn from(m: LevelMask) -> u8 {
        m.0
    }
}

impl std::fmt::Debug for LevelMask {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:03b}", self.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn correct_level() {
        const LEVEL: [u8; 8] = [0, 1, 1, 2, 1, 2, 2, 3];

        for mask in 0b000..=0b111 {
            assert_eq!(LevelMask(mask).level(), LEVEL[mask as usize]);
        }
    }

    #[test]
    fn correct_hash_index() {
        const HASH_INDEX_TABLE: [[u8; 4]; 8] = [
            // index      // mask
            [0, 0, 0, 0], // 000
            [0, 1, 1, 1], // 001
            [0, 0, 1, 1], // 010
            [0, 1, 2, 2], // 011
            [0, 0, 0, 1], // 100
            [0, 1, 1, 2], // 101
            [0, 0, 1, 2], // 110
            [0, 1, 2, 3], // 111
        ];

        for mask in 0b000..=0b111 {
            let mask = LevelMask(mask);

            for i in 0..=3 {
                let hash_index = mask.hash_index(i);
                assert_eq!(hash_index, HASH_INDEX_TABLE[mask.0 as usize][i as usize]);
            }
        }
    }
}
