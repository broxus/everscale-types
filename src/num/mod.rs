//! Integer types used in blockchain models.

use std::num::NonZeroU8;
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

use crate::cell::*;
use crate::util::unlikely;

macro_rules! impl_ops {
    ($ident:ident, $inner:ty) => {
        impl From<$ident> for $inner {
            #[inline]
            fn from(value: $ident) -> Self {
                value.0
            }
        }

        impl PartialEq<$inner> for $ident {
            #[inline]
            fn eq(&self, other: &$inner) -> bool {
                self.0 == *other
            }
        }

        impl PartialEq<$ident> for $inner {
            #[inline]
            fn eq(&self, other: &$ident) -> bool {
                *self == other.0
            }
        }

        impl std::fmt::Display for $ident {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.0.fmt(f)
            }
        }

        impl std::fmt::Binary for $ident {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Binary::fmt(&self.0, f)
            }
        }

        impl std::fmt::LowerHex for $ident {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::LowerHex::fmt(&self.0, f)
            }
        }

        impl std::fmt::UpperHex for $ident {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::UpperHex::fmt(&self.0, f)
            }
        }

        impl Add for $ident {
            type Output = Self;

            #[inline]
            fn add(mut self, rhs: Self) -> Self::Output {
                self.0 += rhs.0;
                self
            }
        }

        impl Add<$inner> for $ident {
            type Output = Self;

            #[inline]
            fn add(mut self, rhs: $inner) -> Self::Output {
                self.0 += rhs;
                self
            }
        }

        impl AddAssign for $ident {
            #[inline]
            fn add_assign(&mut self, rhs: Self) {
                self.0 += rhs.0;
            }
        }

        impl AddAssign<$inner> for $ident {
            fn add_assign(&mut self, rhs: $inner) {
                self.0 += rhs;
            }
        }

        impl Sub for $ident {
            type Output = Self;

            #[inline]
            fn sub(mut self, rhs: Self) -> Self::Output {
                self.0 -= rhs.0;
                self
            }
        }

        impl Sub<$inner> for $ident {
            type Output = Self;

            #[inline]
            fn sub(mut self, rhs: $inner) -> Self::Output {
                self.0 -= rhs;
                self
            }
        }

        impl SubAssign for $ident {
            #[inline]
            fn sub_assign(&mut self, rhs: Self) {
                self.0 -= rhs.0;
            }
        }

        impl SubAssign<$inner> for $ident {
            #[inline]
            fn sub_assign(&mut self, rhs: $inner) {
                self.0 -= rhs;
            }
        }

        impl Mul for $ident {
            type Output = Self;

            #[inline]
            fn mul(mut self, rhs: Self) -> Self::Output {
                self.0 *= rhs.0;
                self
            }
        }

        impl Mul<$inner> for $ident {
            type Output = Self;

            #[inline]
            fn mul(mut self, rhs: $inner) -> Self::Output {
                self.0 *= rhs;
                self
            }
        }

        impl MulAssign for $ident {
            #[inline]
            fn mul_assign(&mut self, rhs: Self) {
                self.0 *= rhs.0;
            }
        }

        impl MulAssign<$inner> for $ident {
            #[inline]
            fn mul_assign(&mut self, rhs: $inner) {
                self.0 *= rhs;
            }
        }

        impl Div for $ident {
            type Output = Self;

            #[inline]
            fn div(mut self, rhs: Self) -> Self::Output {
                self.0 /= rhs.0;
                self
            }
        }

        impl Div<$inner> for $ident {
            type Output = Self;

            #[inline]
            fn div(mut self, rhs: $inner) -> Self::Output {
                self.0 /= rhs;
                self
            }
        }

        impl DivAssign for $ident {
            #[inline]
            fn div_assign(&mut self, rhs: Self) {
                self.0 /= rhs.0;
            }
        }

        impl DivAssign<$inner> for $ident {
            #[inline]
            fn div_assign(&mut self, rhs: $inner) {
                self.0 /= rhs;
            }
        }

        impl Shr<u8> for $ident {
            type Output = Self;

            #[inline]
            fn shr(mut self, rhs: u8) -> Self::Output {
                self.0 >>= rhs;
                self
            }
        }

        impl ShrAssign<u8> for $ident {
            #[inline]
            fn shr_assign(&mut self, rhs: u8) {
                self.0 >>= rhs;
            }
        }

        impl Shl<u8> for $ident {
            type Output = Self;

            #[inline]
            fn shl(mut self, rhs: u8) -> Self::Output {
                self.0 <<= rhs;
                self
            }
        }

        impl ShlAssign<u8> for $ident {
            #[inline]
            fn shl_assign(&mut self, rhs: u8) {
                self.0 <<= rhs;
            }
        }
    };
}

macro_rules! impl_var_uints {
    ($($(#[doc = $doc:expr])* $vis:vis struct $ident:ident($inner:ty[..$max_bytes:literal]);)*) => {
        $(
            impl_var_uints!{@impl $(#[doc = $doc])* $vis $ident $inner, $max_bytes}
        )*
    };

    (@impl $(#[doc = $doc:expr])* $vis:vis $ident:ident $inner:ty, $max_bytes:literal) => {
        $(#[doc = $doc])*
        #[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        #[repr(transparent)]
        $vis struct $ident($inner);

        impl $ident {
            /// The additive identity for this integer type, i.e. `0`.
            pub const ZERO: Self = $ident(0);

            /// The multiplicative identity for this integer type, i.e. `1`.
            pub const ONE: Self = $ident(1);

            /// The smallest value that can be represented by this integer type.
            pub const MIN: Self = $ident(0);

            /// The largest value that can be represented by this integer type.
            pub const MAX: Self = $ident(((1 as $inner) << ($max_bytes * 8)) - 1);

            /// The number of data bits that the length occupies.
            pub const LEN_BITS: u16 = 8 - ($max_bytes as u8).leading_zeros() as u16;

            /// The maximum number of data bits that this struct occupies.
            pub const MAX_BITS: u16 = Self::LEN_BITS + $max_bytes * 8;

            /// Creates a new integer value from a primitive integer.
            #[inline]
            pub const fn new(value: $inner) -> Self {
                Self(value)
            }

            /// Converts integer into an underlying primitive integer.
            #[inline]
            pub const fn into_inner(self) -> $inner {
                self.0
            }

            /// Returns `true` if an underlying primitive integer is zero.
            #[inline]
            pub const fn is_zero(&self) -> bool {
                self.0 == 0
            }

            /// Returns `true` if an underlying primitive integer fits into the repr.
            #[inline]
            pub const fn is_valid(&self) -> bool {
                self.0 <= Self::MAX.0
            }

            /// Returns number of data bits that this struct occupies.
            /// Returns `None` if an underlying primitive integer is too large.
            pub const fn bit_len(&self) -> Option<u16> {
                let bytes = (std::mem::size_of::<Self>() as u32 - self.0.leading_zeros() / 8) as u8;
                if unlikely(bytes > $max_bytes) {
                    None
                } else {
                    Some(Self::LEN_BITS + bytes as u16 * 8)
                }
            }

            /// Returns number of data bits that this struct occupies.
            /// Returns [`MAX_BITS`] if an underlying primitive integer is too large.
            ///
            /// [`MAX_BITS`]: Self::MAX_BITS
            pub const fn unwrap_bit_len(&self) -> u16 {
                let bytes = (std::mem::size_of::<Self>() as u32 - self.0.leading_zeros() / 8) as u8;
                if unlikely(bytes > $max_bytes) {
                    Self::MAX_BITS
                } else {
                    Self::LEN_BITS + bytes as u16 * 8
                }
            }

            /// Checked integer addition. Computes `self + rhs`, returning `None` if overflow occurred.
            #[inline]
            pub const fn checked_add(self, rhs: Self) -> Option<Self> {
                match self.0.checked_add(rhs.0) {
                    Some(value) if value <= Self::MAX.0 => Some($ident(value)),
                    _ => None,
                }
            }

            /// Checked integer subtraction. Computes `self - rhs`, returning `None` if overflow occurred.
            #[inline]
            pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
                match self.0.checked_sub(rhs.0) {
                    Some(value) if value <= Self::MAX.0 => Some($ident(value)),
                    _ => None,
                }
            }

            /// Checked integer multiplication. Computes `self * rhs`, returning `None` if overflow occurred.
            #[inline]
            pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
                match self.0.checked_mul(rhs.0) {
                    Some(value) if value <= Self::MAX.0 => Some($ident(value)),
                    _ => None,
                }
            }

            /// Checked integer division. Computes `self / rhs`, returning None if `rhs == 0`
            /// or overflow occurred.
            #[inline]
            pub const fn checked_div(self, rhs: Self) -> Option<Self> {
                match self.0.checked_div(rhs.0) {
                    Some(value) if value <= Self::MAX.0 => Some($ident(value)),
                    _ => None,
                }
            }
        }

        impl_ops! { $ident, $inner }
    };
}

impl_var_uints! {
    /// Variable-length 24-bit integer.
    ///
    /// Stored as 2 bits of `len` (`0..=3`), followed by `len` bytes.
    pub struct VarUint24(u32[..3]);

    /// Variable-length 56-bit integer.
    ///
    /// Stored as 3 bits of `len` (`0..=7`), followed by `len` bytes.
    pub struct VarUint56(u64[..7]);

    /// Variable-length 120-bit integer. Used for native currencies.
    ///
    /// Stored as 4 bits of `len` (`0..=15`), followed by `len` bytes.
    pub struct Tokens(u128[..15]);
}

impl<C: CellFamily> Store<C> for VarUint24 {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        let bytes = (4 - self.0.leading_zeros() / 8) as u8;
        let bits = bytes as u16 * 8;

        if unlikely(bytes > 3 || !builder.has_capacity(Self::LEN_BITS + bits, 0)) {
            return false;
        }

        builder.store_small_uint(bytes, Self::LEN_BITS) && builder.store_uint(self.0 as u64, bits)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for VarUint24 {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let bytes = slice.load_small_uint(Self::LEN_BITS)?;
        Some(Self(slice.load_uint(bytes as u16 * 8)? as u32))
    }
}

impl<C: CellFamily> Store<C> for VarUint56 {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        let bytes = (8 - self.0.leading_zeros() / 8) as u8;
        let bits = bytes as u16 * 8;

        if unlikely(bytes > 7 || !builder.has_capacity(Self::LEN_BITS + bits, 0)) {
            return false;
        }

        builder.store_small_uint(bytes, Self::LEN_BITS) && builder.store_uint(self.0, bits)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for VarUint56 {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let bytes = slice.load_small_uint(Self::LEN_BITS)?;
        Some(Self(slice.load_uint(bytes as u16 * 8)?))
    }
}

impl<C: CellFamily> Store<C> for Tokens {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        let bytes = (16 - self.0.leading_zeros() / 8) as u8;
        let bits = bytes as u16 * 8;

        if unlikely(bytes > 15 || !builder.has_capacity(Self::LEN_BITS + bits, 0)) {
            return false;
        }

        builder.store_small_uint(bytes, Self::LEN_BITS) && store_u128(builder, self.0, bits)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for Tokens {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let bytes = slice.load_small_uint(Self::LEN_BITS)?;
        Some(Self(load_u128(slice, bytes)?))
    }
}

/// Variable-length 248-bit integer.
///
/// Stored as 5 bits of `len` (`0..=31`), followed by `len` bytes.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct VarUint248([u128; 2]);

impl VarUint248 {
    /// The multiplicative identity for this integer type, i.e. `1`.
    pub const ONE: Self = Self([0; 2]);

    /// The smallest value that can be represented by this integer type.
    pub const MIN: Self = Self::new(1);

    /// The largest value that can be represented by this integer type.
    pub const MAX: Self = Self::from_words(u128::MAX >> 8, u128::MAX);

    /// The number of data bits that the length occupies.
    pub const LEN_BITS: u16 = 5;

    /// The maximum number of data bits that this struct occupies.
    pub const MAX_BITS: u16 = Self::LEN_BITS + 31 * 8;

    /// Creates a new integer value from a primitive integer.
    #[inline]
    pub const fn new(value: u128) -> Self {
        Self::from_words(0, value)
    }

    /// Constructs self from a pair of high and low underlying integers.
    #[inline]
    pub const fn from_words(hi: u128, lo: u128) -> Self {
        #[cfg(target_endian = "little")]
        {
            Self([lo, hi])
        }
        #[cfg(target_endian = "big")]
        {
            Self([hi, lo])
        }
    }

    /// Returns a tuple of high and low underlying integers.
    #[inline]
    pub const fn into_words(self) -> (u128, u128) {
        #[cfg(target_endian = "little")]
        {
            (self.0[1], self.0[0])
        }
        #[cfg(target_endian = "big")]
        {
            (self.0[0], self.0[1])
        }
    }

    /// Returns `true` if an underlying primitive integer is zero.
    #[inline]
    pub const fn is_zero(&self) -> bool {
        self.0[0] == 0 && self.0[1] == 0
    }

    /// Returns `true` if an underlying primitive integer fits into the repr.
    #[inline]
    pub const fn is_valid(&self) -> bool {
        self.into_words().0 <= (u128::MAX >> 8)
    }

    /// Returns number of data bits that this struct occupies.
    /// Returns `None` if an underlying primitive integer is too large.
    pub const fn bit_len(&self) -> Option<u16> {
        let bytes = (32 - self.leading_zeros() / 8) as u8;
        if unlikely(bytes > 31) {
            None
        } else {
            Some(Self::LEN_BITS + bytes as u16 * 8)
        }
    }

    /// Returns the number of leading zeros in the binary representation of self.
    pub const fn leading_zeros(&self) -> u32 {
        let (hi, lo) = self.into_words();
        if hi == 0 {
            128 + lo.leading_zeros()
        } else {
            hi.leading_zeros()
        }
    }
}

impl Ord for VarUint248 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.into_words().cmp(&other.into_words())
    }
}

impl PartialOrd for VarUint248 {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<C: CellFamily> Store<C> for VarUint248 {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        let bytes = (32 - self.leading_zeros() / 8) as u8;
        let mut bits = bytes as u16 * 8;

        if unlikely(bytes > 31 || !builder.has_capacity(Self::LEN_BITS + bits, 0)) {
            return false;
        }

        builder.store_small_uint(bytes, Self::LEN_BITS);

        let (hi, lo) = self.into_words();
        if let Some(high_bits) = bits.checked_sub(128) {
            store_u128(builder, hi, high_bits);
            bits -= high_bits;
        }
        store_u128(builder, lo, bits)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for VarUint248 {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let mut bytes = slice.load_small_uint(Self::LEN_BITS)?;

        let mut hi: u128 = 0;
        if let Some(high_bytes) = bytes.checked_sub(16) {
            if high_bytes > 0 {
                hi = load_u128(slice, high_bytes)?;
                bytes -= high_bytes;
            }
        }

        let lo = load_u128(slice, bytes)?;
        Some(Self::from_words(hi, lo))
    }
}

macro_rules! impl_small_uints {
    ($($(#[doc = $doc:expr])* $vis:vis struct $ident:ident($bits:literal);)*) => {
        $(
            impl_small_uints!{@impl $(#[doc = $doc])* $vis $ident, $bits}
        )*
    };

    (@impl $(#[doc = $doc:expr])* $vis:vis $ident:ident, $bits:literal) => {
        $(#[doc = $doc])*
        #[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        #[repr(transparent)]
        $vis struct $ident(u16);

        impl $ident {
            /// The additive identity for this integer type, i.e. `0`.
            pub const ZERO: Self = $ident(0);

            /// The multiplicative identity for this integer type, i.e. `1`.
            pub const ONE: Self = $ident(1);

            /// The smallest value that can be represented by this integer type.
            pub const MIN: Self = $ident(0);

            /// The largest value that can be represented by this integer type.
            pub const MAX: Self = $ident((1u16 << $bits) - 1);

            /// The number of data bits that this struct occupies.
            pub const BITS: u16 = $bits;

            /// Creates a new integer value from a primitive integer.
            #[inline]
            pub const fn new(value: u16) -> Self {
                Self(value)
            }

            /// Converts integer into an underlying primitive integer.
            #[inline]
            pub const fn into_inner(self) -> u16 {
                self.0
            }

            /// Returns `true` if an underlying primitive integer is zero.
            #[inline]
            pub const fn is_zero(&self) -> bool {
                self.0 == 0
            }

            /// Returns `true` if an underlying primitive integer fits into the repr.
            #[inline]
            pub const fn is_valid(&self) -> bool {
                self.0 <= Self::MAX.0
            }

            /// Checked integer addition. Computes `self + rhs`, returning `None` if overflow occurred.
            #[inline]
            pub const fn checked_add(self, rhs: Self) -> Option<Self> {
                match self.0.checked_add(rhs.0) {
                    Some(value) if value <= Self::MAX.0 => Some($ident(value)),
                    _ => None,
                }
            }

            /// Checked integer subtraction. Computes `self - rhs`, returning `None` if overflow occurred.
            #[inline]
            pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
                match self.0.checked_sub(rhs.0) {
                    Some(value) if value <= Self::MAX.0 => Some($ident(value)),
                    _ => None,
                }
            }

            /// Checked integer multiplication. Computes `self * rhs`, returning `None` if overflow occurred.
            #[inline]
            pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
                match self.0.checked_mul(rhs.0) {
                    Some(value) if value <= Self::MAX.0 => Some($ident(value)),
                    _ => None,
                }
            }

            /// Checked integer division. Computes `self / rhs`, returning None if `rhs == 0`
            /// or overflow occurred.
            #[inline]
            pub const fn checked_div(self, rhs: Self) -> Option<Self> {
                match self.0.checked_div(rhs.0) {
                    Some(value) if value <= Self::MAX.0 => Some($ident(value)),
                    _ => None,
                }
            }
        }

        impl<C: CellFamily> Store<C> for $ident {
            fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
                self.is_valid() && builder.store_uint(self.0 as u64, Self::BITS)
            }
        }

        impl<'a, C: CellFamily> Load<'a, C> for $ident {
            fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
                Some(Self(slice.load_uint(Self::BITS)? as u16))
            }
        }

        impl crate::dict::DictKey for $ident {
            const BITS: u16 = $bits;
        }

        impl_ops! { $ident, u16 }
    };
}

impl_small_uints! {
    /// Fixed-length 9-bit integer.
    pub struct Uint9(9);

    /// Fixed-length 12-bit integer.
    pub struct Uint12(12);

    /// Fixed-length 13-bit integer.
    pub struct Uint13(13);

    /// Fixed-length 15-bit integer.
    pub struct Uint15(15);
}

/// Account split depth. Fixed-length 5-bit integer of range `1..=30`
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
#[repr(transparent)]
pub struct SplitDepth(NonZeroU8);

impl SplitDepth {
    /// The minimum allowed number of bits in the rewrite prefix.
    pub const MIN: Self = match NonZeroU8::new(1) {
        Some(value) => Self(value),
        None => unreachable!(),
    };

    /// The maximum allowed number of bits in the rewrite prefix.
    pub const MAX: Self = match NonZeroU8::new(30) {
        Some(value) => Self(value),
        None => unreachable!(),
    };

    /// The number of data bits that this struct occupies.
    pub const BITS: u16 = 5;

    /// Creates a new integer value from a primitive integer.
    #[inline]
    pub const fn new(value: u8) -> Option<Self> {
        match NonZeroU8::new(value) {
            Some(value) => Some(Self(value)),
            None => None,
        }
    }

    /// Creates a new integer value from bit len.
    #[inline]
    pub const fn from_bit_len(bit_len: u16) -> Option<Self> {
        if bit_len < u8::MAX as u16 {
            Self::new(bit_len as u8)
        } else {
            None
        }
    }

    /// Converts split depths into the number of bits.
    #[inline]
    pub const fn into_bit_len(self) -> u16 {
        self.0.get() as u16
    }
}

impl<C: CellFamily> Store<C> for SplitDepth {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        builder.store_small_uint(self.0.get(), Self::BITS)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for SplitDepth {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Self::new(slice.load_small_uint(Self::BITS)?)
    }
}

fn store_u128<C: CellFamily>(builder: &mut CellBuilder<C>, value: u128, mut bits: u16) -> bool {
    if let Some(high_bits) = bits.checked_sub(64) {
        if !builder.store_uint((value >> 64) as u64, high_bits) {
            return false;
        }
        bits -= high_bits;
    }
    builder.store_uint(value as u64, bits)
}

fn load_u128<C: CellFamily>(slice: &mut CellSlice<'_, C>, mut bytes: u8) -> Option<u128> {
    let mut result: u128 = 0;
    if let Some(high_bytes) = bytes.checked_sub(8) {
        if high_bytes > 0 {
            result = (slice.load_uint(high_bytes as u16 * 8)? as u128) << 64;
            bytes -= high_bytes;
        }
    }
    result |= slice.load_uint(bytes as u16 * 8)? as u128;
    Some(result)
}

#[cfg(test)]
mod tests {
    use crate::{RcCellBuilder, RcCellFamily};

    use super::*;

    macro_rules! impl_operation_tests {
        ($ident:ident$(, $check_max_div:ident)?) => {
            assert_eq!($ident::new(10) + $ident::new(4), $ident::new(14));
            assert_eq!($ident::new(10) + 4, $ident::new(14));

            assert_eq!($ident::new(10) - $ident::new(4), $ident::new(6));
            assert_eq!($ident::new(10) - 4, $ident::new(6));

            assert_eq!($ident::new(10) * $ident::new(4), $ident::new(40));
            assert_eq!($ident::new(10) * 4, $ident::new(40));

            assert_eq!($ident::new(10) / $ident::new(2), $ident::new(5));
            assert_eq!($ident::new(10) / 2, $ident::new(5));

            assert_eq!($ident::new(10) >> 2, $ident::new(2));
            assert_eq!($ident::new(10) << 2, $ident::new(40));

            let mut value = $ident::new(10);
            value += 4;
            assert_eq!(value, $ident::new(14));

            let mut value = $ident::new(10);
            value -= 4;
            assert_eq!(value, $ident::new(6));

            let mut value = $ident::new(10);
            value *= 4;
            assert_eq!(value, $ident::new(40));

            let mut value = $ident::new(10);
            value /= 2;
            assert_eq!(value, $ident::new(5));

            let mut value = $ident::new(10);
            value >>= 2;
            assert_eq!(value, $ident::new(2));

            let mut value = $ident::new(10);
            value <<= 2;
            assert_eq!(value, $ident::new(40));

            assert!(!($ident::MAX + 1).is_valid());

            assert_eq!($ident::MAX.checked_add($ident::new(1)), None);
            assert_eq!(
                ($ident::MAX - 1).checked_add($ident::new(1)),
                Some($ident::MAX)
            );

            assert_eq!(($ident::MAX + 10).checked_sub($ident::new(1)), None);
            assert_eq!(
                ($ident::MAX + 10).checked_sub($ident::MAX),
                Some($ident::new(10)),
            );
            assert_eq!($ident::new(10).checked_sub($ident::MAX), None);

            assert_eq!($ident::MAX.checked_mul($ident::new(2)), None);
            assert_eq!(
                ($ident::MAX / 2).checked_mul($ident::new(2)),
                Some($ident::MAX - 1)
            );

            $(
                let $check_max_div = ();
                _ = $check_max_div;
                assert_eq!((($ident::MAX + 1) * 2).checked_div($ident::new(2)), None);
                assert_eq!(
                    ($ident::MAX * 2).checked_div($ident::new(2)),
                    Some($ident::MAX)
                );
                assert_eq!($ident::ONE.checked_div($ident::ZERO), None);
            )?
        };
    }

    macro_rules! impl_serialization_tests {
        ($ident:ident, $max_bits:literal) => {
            let finalizer = &mut RcCellFamily::default_finalizer();

            for i in 0..$max_bits {
                let value = $ident::ONE << i;
                let mut builder = RcCellBuilder::new();

                if value <= $ident::MAX {
                    assert!(value.store_into(&mut builder, finalizer));
                    let cell = builder.build().unwrap();
                    assert_eq!(value.bit_len().unwrap(), cell.bit_len());
                } else {
                    assert!(!value.store_into(&mut builder, finalizer));
                }
            }
        };
    }

    macro_rules! impl_deserialization_tests {
        ($ident:ident, $max_bits:literal, $value:literal) => {
            let finalizer = &mut RcCellFamily::default_finalizer();

            let mut value = $ident::new($value);
            for _ in 0..=$max_bits {
                let mut builder = RcCellBuilder::new();
                assert!(value.store_into(&mut builder, finalizer));
                let cell = builder.build().unwrap();

                let parsed_value = $ident::load_from(&mut cell.as_slice()).unwrap();
                assert_eq!(parsed_value, value);

                value >>= 1;
            }
        };
    }

    macro_rules! impl_fixed_len_serialization_tests {
        ($ident:ident, $max_bits:literal) => {
            let finalizer = &mut RcCellFamily::default_finalizer();

            for i in 0..$max_bits {
                let value = $ident::ONE << i;
                let mut builder = RcCellBuilder::new();

                if value <= $ident::MAX {
                    assert!(value.store_into(&mut builder, finalizer));
                    let cell = builder.build().unwrap();
                    assert_eq!($ident::BITS, cell.bit_len());
                } else {
                    assert!(!value.store_into(&mut builder, finalizer));
                }
            }
        };
    }

    #[test]
    fn fixed_len_operations() {
        impl_operation_tests!(Uint9, check_max_div);
        impl_operation_tests!(Uint12, check_max_div);
        impl_operation_tests!(Uint13, check_max_div);
        impl_operation_tests!(Uint15);
    }

    #[test]
    fn fixed_len_serialization() {
        impl_fixed_len_serialization_tests!(Uint9, 16);
        impl_fixed_len_serialization_tests!(Uint12, 16);
        impl_fixed_len_serialization_tests!(Uint13, 16);
        impl_fixed_len_serialization_tests!(Uint15, 16);
    }

    #[test]
    fn fixed_len_deserialization() {
        impl_deserialization_tests!(Uint9, 9, 0b100110011);
        impl_deserialization_tests!(Uint12, 12, 0b111100110011);
        impl_deserialization_tests!(Uint13, 13, 0b1111100110011);
        impl_deserialization_tests!(Uint15, 15, 0b11111100110011);
    }

    #[test]
    fn var_uint3_operations() {
        impl_operation_tests!(VarUint24, check_max_div);
    }

    #[test]
    fn var_uint7_operations() {
        impl_operation_tests!(VarUint56, check_max_div);
    }

    #[test]
    fn tokens_operations() {
        impl_operation_tests!(Tokens, check_max_div);
    }

    #[test]
    fn var_uint3_serialization() {
        impl_serialization_tests!(VarUint24, 32);
    }

    #[test]
    fn var_uint7_serialization() {
        impl_serialization_tests!(VarUint56, 64);
    }

    #[test]
    fn tokens_serialization() {
        impl_serialization_tests!(Tokens, 128);
    }

    #[test]
    fn var_uint3_deserialization() {
        impl_deserialization_tests!(VarUint24, 24, 0xabcdef);
    }

    #[test]
    fn var_uint7_deserialization() {
        impl_deserialization_tests!(VarUint56, 56, 0xabcdef89abcdef);
    }

    #[test]
    fn tokens_deserialization() {
        impl_deserialization_tests!(Tokens, 120, 0xabcdef89abcdefdeadbeeffafacafe);
    }

    #[test]
    fn var_uint31_serialization() {
        let finalizer = &mut RcCellFamily::default_finalizer();

        for i in 0..128 {
            let lo = 1u128 << i;
            let mut builder = RcCellBuilder::new();

            let value = VarUint248::new(lo);
            assert!(value.store_into(&mut builder, finalizer));
            let cell = builder.build().unwrap();
            assert_eq!(value.bit_len().unwrap(), cell.bit_len());
        }
    }

    #[test]
    fn var_uint31_deserialization() {
        let finalizer = &mut RcCellFamily::default_finalizer();

        let mut lo: u128 = 0xababcdef89abcdefdeadbeeffafacafe;
        for _ in 0..=128 {
            let value = VarUint248::new(lo);

            let mut builder = RcCellBuilder::new();
            assert!(value.store_into(&mut builder, finalizer));
            let cell = builder.build().unwrap();

            let parsed_value = VarUint248::load_from(&mut cell.as_slice()).unwrap();
            assert_eq!(parsed_value, value);

            lo >>= 1;
        }
    }
}
