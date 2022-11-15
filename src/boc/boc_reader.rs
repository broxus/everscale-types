use std::ops::Deref;

/// Wrapper around indexed bytes slice access
/// to eliminate bounds check
pub struct BocReader {
    len: usize,
    offset: usize,
}

impl BocReader {
    #[inline(always)]
    pub const fn new(len: usize) -> Self {
        Self { len, offset: 0 }
    }

    #[inline(always)]
    pub const fn offset(&self) -> usize {
        self.offset
    }

    #[inline(always)]
    pub const fn require(&self, len: usize) -> bool {
        self.offset + len <= self.len
    }

    #[inline(always)]
    pub fn advance(&mut self, bytes: usize) {
        self.offset += bytes;
    }

    #[inline(always)]
    pub unsafe fn read_be_uint_fast(&mut self, data: &[u8], size: usize) -> usize {
        let res = read_be_uint_fast(data, self.offset, size);
        self.advance(size);
        res
    }

    #[inline(always)]
    pub unsafe fn read_be_uint_full(&mut self, data: &[u8], size: usize) -> u64 {
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
    pub unsafe fn read_descriptor_bytes(&mut self, data: &[u8]) -> [u8; 2] {
        *(data.as_ptr().add(self.offset) as *const [u8; 2])
    }
}

impl Deref for BocReader {
    type Target = usize;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.offset
    }
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
