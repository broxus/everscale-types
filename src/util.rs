//! General stuff.

use std::mem::MaybeUninit;

use crate::error::Error;

/// Brings [unlikely](core::intrinsics::unlikely) to stable rust.
#[inline(always)]
pub(crate) const fn unlikely(b: bool) -> bool {
    #[allow(clippy::needless_bool, clippy::bool_to_int_with_if)]
    if (1i32).checked_div(if b { 0 } else { 1 }).is_none() {
        true
    } else {
        false
    }
}

/// Reads n-byte integer as `u32` from the bytes pointer.
///
/// # Safety
///
/// The following must be true:
/// - size must be in range 1..=4.
/// - data must be at least `size` bytes long.
pub(crate) unsafe fn read_be_u32_fast(data_ptr: *const u8, size: usize) -> u32 {
    match size {
        1 => *data_ptr as u32,
        2 => u16::from_be_bytes(*(data_ptr as *const [u8; 2])) as u32,
        3 => {
            let mut bytes = [0u8; 4];
            std::ptr::copy_nonoverlapping(data_ptr, bytes.as_mut_ptr().add(1), 3);
            u32::from_be_bytes(bytes)
        }
        4 => u32::from_be_bytes(*(data_ptr as *const [u8; 4])),
        _ => std::hint::unreachable_unchecked(),
    }
}

/// Reads n-byte integer as `u64` from the bytes pointer.
///
/// # Safety
///
/// The following must be true:
/// - size must be in range 1..=8.
/// - data must be at least `size` bytes long.
pub(crate) unsafe fn read_be_u64_fast(data_ptr: *const u8, size: usize) -> u64 {
    match size {
        1..=4 => read_be_u32_fast(data_ptr, size) as u64,
        5..=8 => {
            let mut bytes = [0u8; 8];
            std::ptr::copy_nonoverlapping(data_ptr, bytes.as_mut_ptr().add(8 - size), size);
            u64::from_be_bytes(bytes)
        }
        _ => std::hint::unreachable_unchecked(),
    }
}

#[cfg(any(feature = "base64", test))]
#[inline]
pub(crate) fn encode_base64<T: AsRef<[u8]>>(data: T) -> String {
    use base64::Engine;
    fn encode_base64_impl(data: &[u8]) -> String {
        base64::engine::general_purpose::STANDARD.encode(data)
    }
    encode_base64_impl(data.as_ref())
}

#[cfg(any(feature = "base64", test))]
#[inline]
pub(crate) fn decode_base64<T: AsRef<[u8]>>(data: T) -> Result<Vec<u8>, base64::DecodeError> {
    use base64::Engine;
    fn decode_base64_impl(data: &[u8]) -> Result<Vec<u8>, base64::DecodeError> {
        base64::engine::general_purpose::STANDARD.decode(data)
    }
    decode_base64_impl(data.as_ref())
}

#[cfg(any(feature = "base64", test))]
#[allow(unused)]
#[inline]
pub(crate) fn decode_base64_slice<T: AsRef<[u8]>>(
    data: T,
    target: &mut [u8],
) -> Result<(), base64::DecodeSliceError> {
    use base64::Engine;
    fn decode_base64_slice_impl(
        data: &[u8],
        target: &mut [u8],
    ) -> Result<(), base64::DecodeSliceError> {
        base64::engine::general_purpose::STANDARD
            .decode_slice(data, target)
            .map(|_| ())
    }
    decode_base64_slice_impl(data.as_ref(), target)
}

#[cfg(any(feature = "base64", test))]
#[inline]
pub(crate) fn crc_16(data: &[u8]) -> u16 {
    let mut crc: u32 = 0;
    for c in data {
        let t = c ^ ((crc >> 8) as u8);
        crc = (CRC16_TABLE[t as usize] ^ ((crc << 8) as u16)) as u32;
    }
    crc as u16
}

static CRC16_TABLE: [u16; 256] = [
    0x0000, 0x1021, 0x2042, 0x3063, 0x4084, 0x50a5, 0x60c6, 0x70e7, 0x8108, 0x9129, 0xa14a, 0xb16b,
    0xc18c, 0xd1ad, 0xe1ce, 0xf1ef, 0x1231, 0x0210, 0x3273, 0x2252, 0x52b5, 0x4294, 0x72f7, 0x62d6,
    0x9339, 0x8318, 0xb37b, 0xa35a, 0xd3bd, 0xc39c, 0xf3ff, 0xe3de, 0x2462, 0x3443, 0x0420, 0x1401,
    0x64e6, 0x74c7, 0x44a4, 0x5485, 0xa56a, 0xb54b, 0x8528, 0x9509, 0xe5ee, 0xf5cf, 0xc5ac, 0xd58d,
    0x3653, 0x2672, 0x1611, 0x0630, 0x76d7, 0x66f6, 0x5695, 0x46b4, 0xb75b, 0xa77a, 0x9719, 0x8738,
    0xf7df, 0xe7fe, 0xd79d, 0xc7bc, 0x48c4, 0x58e5, 0x6886, 0x78a7, 0x0840, 0x1861, 0x2802, 0x3823,
    0xc9cc, 0xd9ed, 0xe98e, 0xf9af, 0x8948, 0x9969, 0xa90a, 0xb92b, 0x5af5, 0x4ad4, 0x7ab7, 0x6a96,
    0x1a71, 0x0a50, 0x3a33, 0x2a12, 0xdbfd, 0xcbdc, 0xfbbf, 0xeb9e, 0x9b79, 0x8b58, 0xbb3b, 0xab1a,
    0x6ca6, 0x7c87, 0x4ce4, 0x5cc5, 0x2c22, 0x3c03, 0x0c60, 0x1c41, 0xedae, 0xfd8f, 0xcdec, 0xddcd,
    0xad2a, 0xbd0b, 0x8d68, 0x9d49, 0x7e97, 0x6eb6, 0x5ed5, 0x4ef4, 0x3e13, 0x2e32, 0x1e51, 0x0e70,
    0xff9f, 0xefbe, 0xdfdd, 0xcffc, 0xbf1b, 0xaf3a, 0x9f59, 0x8f78, 0x9188, 0x81a9, 0xb1ca, 0xa1eb,
    0xd10c, 0xc12d, 0xf14e, 0xe16f, 0x1080, 0x00a1, 0x30c2, 0x20e3, 0x5004, 0x4025, 0x7046, 0x6067,
    0x83b9, 0x9398, 0xa3fb, 0xb3da, 0xc33d, 0xd31c, 0xe37f, 0xf35e, 0x02b1, 0x1290, 0x22f3, 0x32d2,
    0x4235, 0x5214, 0x6277, 0x7256, 0xb5ea, 0xa5cb, 0x95a8, 0x8589, 0xf56e, 0xe54f, 0xd52c, 0xc50d,
    0x34e2, 0x24c3, 0x14a0, 0x0481, 0x7466, 0x6447, 0x5424, 0x4405, 0xa7db, 0xb7fa, 0x8799, 0x97b8,
    0xe75f, 0xf77e, 0xc71d, 0xd73c, 0x26d3, 0x36f2, 0x0691, 0x16b0, 0x6657, 0x7676, 0x4615, 0x5634,
    0xd94c, 0xc96d, 0xf90e, 0xe92f, 0x99c8, 0x89e9, 0xb98a, 0xa9ab, 0x5844, 0x4865, 0x7806, 0x6827,
    0x18c0, 0x08e1, 0x3882, 0x28a3, 0xcb7d, 0xdb5c, 0xeb3f, 0xfb1e, 0x8bf9, 0x9bd8, 0xabbb, 0xbb9a,
    0x4a75, 0x5a54, 0x6a37, 0x7a16, 0x0af1, 0x1ad0, 0x2ab3, 0x3a92, 0xfd2e, 0xed0f, 0xdd6c, 0xcd4d,
    0xbdaa, 0xad8b, 0x9de8, 0x8dc9, 0x7c26, 0x6c07, 0x5c64, 0x4c45, 0x3ca2, 0x2c83, 0x1ce0, 0x0cc1,
    0xef1f, 0xff3e, 0xcf5d, 0xdf7c, 0xaf9b, 0xbfba, 0x8fd9, 0x9ff8, 0x6e17, 0x7e36, 0x4e55, 0x5e74,
    0x2e93, 0x3eb2, 0x0ed1, 0x1ef0,
];

/// Small on-stack vector of max length N.
pub struct ArrayVec<T, const N: usize> {
    inner: [MaybeUninit<T>; N],
    len: u8,
}

impl<T, const N: usize> ArrayVec<T, N> {
    /// Ensure that provided length is small enough.
    const _ASSERT_LEN: () = assert!(N <= u8::MAX as usize);

    /// Returns an empty vector.
    pub const fn new() -> Self {
        Self {
            // SAFETY: An uninitialized `[MaybeUninit<_>; LEN]` is valid.
            inner: unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() },
            len: 0,
        }
    }

    /// Returns the number of elements in the vector, also referred to as its ‘length’.
    #[inline]
    pub const fn len(&self) -> usize {
        self.len as usize
    }

    /// Returns true if the vector contains no elements.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Safety
    ///
    /// The following must be true:
    /// - The length of this vector is less than `N`.
    #[inline]
    pub unsafe fn push(&mut self, item: T) {
        debug_assert!((self.len as usize) < N);

        *self.inner.get_unchecked_mut(self.len as usize) = MaybeUninit::new(item);
        self.len += 1;
    }

    /// Returns a reference to an element.
    pub const fn get(&self, n: u8) -> Option<&T> {
        if n < self.len {
            let references = self.inner.as_ptr() as *const T;
            // SAFETY: {len} elements were initialized, n < len
            Some(unsafe { &*references.add(n as usize) })
        } else {
            None
        }
    }

    /// Returns the inner data without dropping its elements.
    ///
    /// # Safety
    ///
    /// The caller is responsible for calling the destructor for
    /// `len` initialized items in the returned array.
    #[inline]
    pub unsafe fn into_inner(self) -> [MaybeUninit<T>; N] {
        let this = std::mem::ManuallyDrop::new(self);
        std::ptr::read(&this.inner)
    }
}

impl<T, const N: usize> Default for ArrayVec<T, N> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<R, const N: usize> AsRef<[R]> for ArrayVec<R, N> {
    #[inline]
    fn as_ref(&self) -> &[R] {
        // SAFETY: {len} elements were initialized
        unsafe { std::slice::from_raw_parts(self.inner.as_ptr() as *const R, self.len as usize) }
    }
}

impl<T: Clone, const N: usize> Clone for ArrayVec<T, N> {
    fn clone(&self) -> Self {
        let mut res = Self::default();
        for item in self.as_ref() {
            // SAFETY: {len} elements were initialized
            unsafe { res.push(item.clone()) };
        }
        res
    }
}

impl<T, const N: usize> Drop for ArrayVec<T, N> {
    fn drop(&mut self) {
        debug_assert!(self.len as usize <= N);

        let references_ptr = self.inner.as_mut_ptr() as *mut T;
        for i in 0..self.len {
            // SAFETY: len items were initialized
            unsafe { std::ptr::drop_in_place(references_ptr.add(i as usize)) };
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) enum IterStatus {
    /// Iterator is still valid.
    Valid,
    /// Iterator started with a pruned branch cell.
    Pruned,
    /// [`RawDict`] has invalid structure.
    Broken,
}

impl IterStatus {
    #[inline]
    pub(crate) const fn is_valid(self) -> bool {
        matches!(self, Self::Valid)
    }

    #[inline]
    pub(crate) const fn is_pruned(self) -> bool {
        matches!(self, Self::Pruned)
    }
}

/// Used to get a mutable reference of the inner type if possible.
pub trait TryAsMut<T: ?Sized> {
    /// Tries to convert this type into a mutable reference of the (usually inferred) input type.
    fn try_as_mut(&mut self) -> Option<&mut T>;
}

/// A wrapper around arbitrary data with the specified bit length.
pub struct Bitstring<'a> {
    /// Underlying bytes (with or without termination bit).
    pub bytes: &'a [u8],
    /// Length of data in bits.
    pub bit_len: u16,
}

impl Bitstring<'_> {
    /// Parses a bitstring from a hex string.
    ///
    /// Returns the parsed data and the bit length.
    /// Tag bit is removed if present.
    pub fn from_hex_str(s: &str) -> Result<(Vec<u8>, u16), Error> {
        fn hex_char(c: u8) -> Result<u8, Error> {
            match c {
                b'A'..=b'F' => Ok(c - b'A' + 10),
                b'a'..=b'f' => Ok(c - b'a' + 10),
                b'0'..=b'9' => Ok(c - b'0'),
                _ => Err(Error::InvalidData),
            }
        }

        if !s.is_ascii() || s.len() > 128 * 2 {
            return Err(Error::InvalidData);
        }

        let s = s.as_bytes();
        let (mut s, with_tag) = match s.strip_suffix(b"_") {
            Some(s) => (s, true),
            None => (s, false),
        };

        let mut half_byte = None;
        if s.len() % 2 != 0 {
            if let Some((last, prefix)) = s.split_last() {
                half_byte = Some(ok!(hex_char(*last)));
                s = prefix;
            }
        }

        let Ok(mut data) = hex::decode(s) else {
            return Err(Error::InvalidData);
        };

        let mut bit_len = data.len() as u16 * 8;
        if let Some(half_byte) = half_byte {
            bit_len += 4;
            data.push(half_byte << 4);
        }

        if with_tag {
            bit_len = data.len() as u16 * 8;
            for byte in data.iter_mut().rev() {
                if *byte == 0 {
                    bit_len -= 8;
                } else {
                    let trailing = byte.trailing_zeros();
                    bit_len -= 1 + trailing as u16;

                    // NOTE: `trailing` is in range 0..=7,
                    // so we must split the shift in two parts.
                    *byte &= (0xff << trailing) << 1;
                    break;
                }
            }

            data.truncate((bit_len as usize + 7) / 8);
        }

        Ok((data, bit_len))
    }
}

impl std::fmt::Display for Bitstring<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const CHUNK_LEN: usize = 16;

        let bit_len = std::cmp::min(self.bit_len as usize, self.bytes.len() * 8) as u16;
        let byte_len = ((bit_len + 7) / 8) as usize;
        let bytes = &self.bytes[..byte_len];

        let rem = bit_len % 8;
        let (bytes, last_byte) = match bytes.split_last() {
            Some((last_byte, bytes)) if rem != 0 => {
                let tag_mask: u8 = 1 << (7 - rem);
                let data_mask = !(tag_mask - 1);
                let last_byte = (*last_byte & data_mask) | tag_mask;
                (bytes, Some(last_byte))
            }
            _ => (bytes, None),
        };

        let mut chunk = [0u8; CHUNK_LEN * 2];
        for data in bytes.chunks(CHUNK_LEN) {
            let chunk = &mut chunk[..data.len() * 2];
            hex::encode_to_slice(data, chunk).unwrap();

            // SAFETY: result was constructed from valid ascii `HEX_CHARS_LOWER`
            ok!(f.write_str(unsafe { std::str::from_utf8_unchecked(chunk) }));
        }

        if let Some(mut last_byte) = last_byte {
            let tag = if rem != 4 { "_" } else { "" };
            let rem = 1 + (rem > 4) as usize;
            if rem == 1 {
                last_byte >>= 4;
            }
            ok!(write!(f, "{last_byte:0rem$x}{tag}"));
        }

        Ok(())
    }
}

impl std::fmt::Binary for Bitstring<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let bit_len = std::cmp::min(self.bit_len as usize, self.bytes.len() * 8) as u16;
        let byte_len = ((bit_len + 7) / 8) as usize;
        let bytes = &self.bytes[..byte_len];

        let rem = (bit_len % 8) as usize;
        let (bytes, last_byte) = match bytes.split_last() {
            Some((last_byte, bytes)) if rem != 0 => (bytes, Some(*last_byte)),
            _ => (bytes, None),
        };

        for byte in bytes {
            ok!(write!(f, "{byte:08b}"));
        }

        if let Some(mut last_byte) = last_byte {
            last_byte >>= 8 - rem;
            ok!(write!(f, "{last_byte:0rem$b}"))
        }

        Ok(())
    }
}

#[allow(unused)]
pub(crate) fn debug_tuple_field1_finish(
    f: &mut std::fmt::Formatter<'_>,
    name: &str,
    value1: &dyn std::fmt::Debug,
) -> std::fmt::Result {
    let mut builder = std::fmt::Formatter::debug_tuple(f, name);
    builder.field(value1);
    builder.finish()
}

pub(crate) fn debug_struct_field1_finish(
    f: &mut std::fmt::Formatter<'_>,
    name: &str,
    name1: &str,
    value1: &dyn std::fmt::Debug,
) -> std::fmt::Result {
    let mut builder = std::fmt::Formatter::debug_struct(f, name);
    builder.field(name1, value1);
    builder.finish()
}

pub(crate) fn debug_struct_field2_finish(
    f: &mut std::fmt::Formatter<'_>,
    name: &str,
    name1: &str,
    value1: &dyn std::fmt::Debug,
    name2: &str,
    value2: &dyn std::fmt::Debug,
) -> std::fmt::Result {
    let mut builder = std::fmt::Formatter::debug_struct(f, name);
    builder.field(name1, value1);
    builder.field(name2, value2);
    builder.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_bitstring_from_hex_str() {
        let (data, bit_len) = Bitstring::from_hex_str("").unwrap();
        assert_eq!(bit_len, 0);
        assert!(data.is_empty());

        let (data, bit_len) = Bitstring::from_hex_str("8_").unwrap();
        assert_eq!(bit_len, 0);
        assert!(data.is_empty());

        let (data, bit_len) = Bitstring::from_hex_str("ded_").unwrap();
        assert_eq!(bit_len, 11);
        assert_eq!(data, vec![0xde, 0xc0]);

        let (data, bit_len) = Bitstring::from_hex_str("b00b1e5").unwrap();
        assert_eq!(bit_len, 28);
        assert_eq!(data, vec![0xb0, 0x0b, 0x1e, 0x50]);

        let (data, bit_len) = Bitstring::from_hex_str("b00b1e5_").unwrap();
        assert_eq!(bit_len, 27);
        assert_eq!(data, vec![0xb0, 0x0b, 0x1e, 0x40]);
    }

    #[test]
    fn bitstring_zero_char_with_completion_tag() {
        assert_eq!(
            format!(
                "{}",
                Bitstring {
                    bytes: &[0b_0011_0000],
                    bit_len: 4
                }
            ),
            format!("{:x}", 0b_0011)
        );
        assert_eq!(
            format!(
                "{}",
                Bitstring {
                    bytes: &[0b_0100_0000],
                    bit_len: 2
                }
            ),
            format!("{:x}_", 0b_0110)
        );
        assert_eq!(
            format!(
                "{}",
                Bitstring {
                    bytes: &[0b_0000_1000],
                    bit_len: 5
                }
            ),
            format!("{:x}{:x}_", 0b_0000, 0b_1100)
        );
        assert_eq!(
            format!(
                "{}",
                Bitstring {
                    bytes: &[0b_0000_1000, 0b_0100_0000],
                    bit_len: 8 + 2
                }
            ),
            format!("{:x}{:x}{:x}_", 0b_0000, 0b_1000, 0b_0110)
        );
        assert_eq!(
            format!(
                "{}",
                Bitstring {
                    bytes: &[0b_0100_0000, 0b_0000_1000],
                    bit_len: 8 + 5
                }
            ),
            format!("{:x}{:x}{:x}{:x}_", 0b_0100, 0b_0000, 0b_0000, 0b_1100)
        );
    }
}
