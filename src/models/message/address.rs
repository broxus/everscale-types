use std::str::FromStr;

use crate::cell::*;
use crate::error::ParseAddrError;
use crate::num::*;
use crate::util::{unlikely, DisplayHash};

/// Internal message address.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum IntAddr {
    /// Standard internal address.
    Std(StdAddr),
    /// Variable-length internal address.
    Var(VarAddr),
}

impl Default for IntAddr {
    #[inline]
    fn default() -> Self {
        Self::Std(StdAddr::default())
    }
}

impl IntAddr {
    /// Returns the number of data bits that this struct occupies.
    pub const fn bit_len(&self) -> u16 {
        match self {
            Self::Std(addr) => addr.bit_len(),
            Self::Var(addr) => addr.bit_len(),
        }
    }
}

impl FromStr for IntAddr {
    type Err = ParseAddrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // TODO: impl from_str for VarAddr
        Ok(Self::Std(ok!(StdAddr::from_str(s))))
    }
}

impl std::fmt::Display for IntAddr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntAddr::Std(addr) => std::fmt::Display::fmt(addr, f),
            IntAddr::Var(_) => f.write_str("varaddr"), // TODO: impl display
        }
    }
}

impl<C: CellFamily> Store<C> for IntAddr {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        match self {
            Self::Std(addr) => addr.store_into(builder, finalizer),
            Self::Var(addr) => addr.store_into(builder, finalizer),
        }
    }
}

impl<'a, C: CellFamily> Load<'a, C> for IntAddr {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if !slice.load_bit()? {
            return None;
        }

        Some(if unlikely(slice.load_bit()?) {
            let anycast = Option::<Box<Anycast>>::load_from(slice)?;
            let address_len = Uint9::load_from(slice)?;
            let workchain = slice.load_u32()? as i32;
            if !slice.has_remaining(address_len.into_inner(), 0) {
                return None;
            }

            let mut address = Vec::with_capacity((address_len.into_inner() as usize + 7) / 8);
            slice.load_raw(&mut address, address_len.into_inner())?;

            Self::Var(VarAddr {
                anycast,
                address_len,
                workchain,
                address,
            })
        } else {
            Self::Std(StdAddr {
                anycast: Option::<Box<Anycast>>::load_from(slice)?,
                workchain: slice.load_u8()? as i8,
                address: slice.load_u256()?,
            })
        })
    }
}

/// Standard internal address.
#[derive(Default, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct StdAddr {
    /// Optional anycast info.
    pub anycast: Option<Box<Anycast>>,
    /// Workchain id (one-byte range).
    pub workchain: i8,
    /// Account id.
    pub address: [u8; 32],
}

impl std::fmt::Debug for StdAddr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StdAddr")
            .field("anycast", &self.anycast)
            .field("workchain", &self.workchain)
            .field("address", &DisplayHash(&self.address))
            .finish()
    }
}

impl StdAddr {
    /// The number of data bits that address without anycast occupies.
    ///
    /// - 2 bits id (`0b10`)
    /// - 1 bit Maybe None
    /// - 8 bits workchain
    /// - 256 bits address
    pub const BITS_WITHOUT_ANYCAST: u16 = 2 + 1 + 8 + 256;

    /// The maximum number of bits that address with anycast occupies.
    pub const BITS_MAX: u16 = Self::BITS_WITHOUT_ANYCAST + Anycast::BITS_MAX;

    /// Constructs a new standard address without anycast info.
    #[inline]
    pub const fn new(workchain: i8, address: [u8; 32]) -> Self {
        Self {
            anycast: None,
            workchain,
            address,
        }
    }

    /// Returns the number of data bits that this struct occupies.
    pub const fn bit_len(&self) -> u16 {
        let mut bit_len = Self::BITS_WITHOUT_ANYCAST;
        if let Some(anycast) = &self.anycast {
            bit_len += anycast.bit_len();
        }
        bit_len
    }
}

impl std::fmt::Display for StdAddr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(anycast) = &self.anycast {
            ok!(f.write_fmt(format_args!("{anycast}:")))
        }

        f.write_fmt(format_args!(
            "{}:{}",
            self.workchain,
            DisplayHash(&self.address)
        ))
    }
}

impl From<StdAddr> for IntAddr {
    #[inline]
    fn from(value: StdAddr) -> Self {
        Self::Std(value)
    }
}

impl FromStr for StdAddr {
    type Err = ParseAddrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.is_empty() {
            return Err(ParseAddrError::Empty);
        }

        let mut result = Self::default();

        let mut parts = s.split(':');
        match parts.next() {
            Some(part) => match part.parse() {
                Ok(workchain) => result.workchain = workchain,
                Err(_) => return Err(ParseAddrError::InvalidWorkchain),
            },
            None => return Err(ParseAddrError::Empty),
        }

        match parts.next() {
            Some(part) => match hex::decode_to_slice(part, &mut result.address) {
                Ok(()) => {}
                Err(_) => return Err(ParseAddrError::InvalidAccountId),
            },
            None => return Err(ParseAddrError::InvalidAccountId),
        }

        if parts.next().is_none() {
            Ok(result)
        } else {
            Err(ParseAddrError::UnexpectedPart)
        }
    }
}

impl<C: CellFamily> Store<C> for StdAddr {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        builder.has_capacity(self.bit_len(), 0)
            && builder.store_small_uint(0b10, 2)
            && self.anycast.store_into(builder, finalizer)
            && builder.store_u8(self.workchain as u8)
            && builder.store_u256(&self.address)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for StdAddr {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if !slice.load_bit()? || slice.load_bit()? {
            return None;
        }

        Some(Self {
            anycast: Option::<Box<Anycast>>::load_from(slice)?,
            workchain: slice.load_u8()? as i8,
            address: slice.load_u256()?,
        })
    }
}

impl crate::dict::DictKey for StdAddr {
    const BITS: u16 = StdAddr::BITS_WITHOUT_ANYCAST;
}

/// Variable-length internal address.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct VarAddr {
    /// Optional anycast info.
    pub anycast: Option<Box<Anycast>>,
    /// Address length in bits.
    pub address_len: Uint9,
    /// Workchain id (full range).
    pub workchain: i32,
    /// Variable-length address.
    pub address: Vec<u8>,
}

impl VarAddr {
    /// The maximum number of bits that address occupies.
    ///
    /// - 2 bits id (`0b11`)
    /// - 1 + `Anycast::BITS_MAX` maybe anycast
    /// - 9 bits `address_len`
    /// - 32 bits workchain
    /// - `address_len` bits of address
    pub const BITS_MAX: u16 =
        2 + 1 + Anycast::BITS_MAX + Uint9::BITS + 32 + Uint9::MAX.into_inner();

    /// Returns the number of data bits that this struct occupies.
    pub const fn bit_len(&self) -> u16 {
        let mut bit_len = 2 + 1 + Uint9::BITS + 32 + self.address_len.into_inner();
        if let Some(anycast) = &self.anycast {
            bit_len += anycast.bit_len();
        }
        bit_len
    }
}

impl From<VarAddr> for IntAddr {
    #[inline]
    fn from(value: VarAddr) -> Self {
        Self::Var(value)
    }
}

impl<C: CellFamily> Store<C> for VarAddr {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        builder.has_capacity(self.bit_len(), 0)
            && builder.store_small_uint(0b11, 2)
            && self.anycast.store_into(builder, finalizer)
            && self.address_len.store_into(builder, finalizer)
            && builder.store_u32(self.workchain as u32)
            && builder.store_raw(&self.address, self.address_len.into_inner())
    }
}

/// External address.
///
/// ```text
/// addr_none$00 = MsgAddressExt;
/// addr_extern$01 len:(## 9) external_address:(bits len) = MsgAddressExt;
/// ```
#[derive(Debug, Default, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct ExtAddr {
    /// Number of bits stored in data.
    pub data_bit_len: Uint9,
    /// External address data
    pub data: Vec<u8>,
}

impl ExtAddr {
    /// Creates non-empty external address.
    pub fn new<T>(data_bit_len: u16, data: T) -> Option<Self>
    where
        T: Into<Vec<u8>>,
    {
        let data_bit_len = Uint9::new(data_bit_len);
        if data_bit_len.is_valid() {
            Some(Self {
                data_bit_len,
                data: data.into(),
            })
        } else {
            None
        }
    }

    /// Returns the number of data bits that this struct occupies.
    pub const fn bit_len(&self) -> u16 {
        Uint9::BITS + self.data_bit_len.into_inner()
    }
}

/// Anycast prefix info.
///
/// ```text
/// anycast_info$_ depth:(#<= 30) { depth >= 1 } rewrite_pfx:(bits depth) = Anycast;
/// ```
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct Anycast {
    /// Prefix length in bits.
    pub depth: SplitDepth,
    /// Rewrite prefix data.
    pub rewrite_prefix: Vec<u8>,
}

impl Anycast {
    /// The minimum allowed number of bits in the rewrite prefix.
    pub const MIN_DEPTH: u8 = 1;
    /// The maximum allowed number of bits in the rewrite prefix.
    pub const MAX_DEPTH: u8 = 30;

    /// The maximum number of bits that an Anycast occupies.
    pub const BITS_MAX: u16 = SplitDepth::BITS + Self::MAX_DEPTH as u16;

    /// Constructs anycast info from rewrite prefix.
    pub fn from_slice<C: CellFamily>(rewrite_prefix: &CellSlice<'_, C>) -> Option<Self> {
        let depth = SplitDepth::from_bit_len(rewrite_prefix.remaining_bits())?;
        let mut data = Vec::with_capacity((depth.into_bit_len() as usize + 7) / 8);
        rewrite_prefix.get_raw(0, &mut data, depth.into_bit_len())?;

        Some(Self {
            depth,
            rewrite_prefix: data,
        })
    }

    /// Returns the number of data bits that this struct occupies.
    pub const fn bit_len(&self) -> u16 {
        SplitDepth::BITS + self.depth.into_bit_len()
    }
}

const HEX_CHARS_LOWER: &[u8; 16] = b"0123456789abcdef";

impl std::fmt::Display for Anycast {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let depth = std::cmp::min(self.depth.into_bit_len(), 30);

        let mut result = [b'0'; 9]; // 8 bytes for rewrite, 1 byte for

        let rem = depth % 8;

        let byte_len = std::cmp::min(((depth - rem) / 8) as usize, 4);
        let result_ptr = result.as_mut_ptr();
        for (i, &byte) in self.rewrite_prefix.iter().take(byte_len).enumerate() {
            // SAFETY: byte_len is 4 at max
            unsafe {
                *result_ptr.add(i * 2) = HEX_CHARS_LOWER[(byte >> 4) as usize];
                *result_ptr.add(i * 2 + 1) = HEX_CHARS_LOWER[(byte & 0x0f) as usize];
            }
        }

        if rem != 0 {
            let tag_mask: u8 = 1 << (7 - rem);
            let data_mask = !(tag_mask - 1);

            let mut byte = self
                .rewrite_prefix
                .get((depth / 8) as usize)
                .copied()
                .unwrap_or_default();

            // xxxxyyyy & data_mask -> xxxxy000 | tag_mask -> xxxx1000
            byte = (byte & data_mask) | tag_mask;

            result[byte_len * 2] = HEX_CHARS_LOWER[(byte >> 4) as usize];
            result[byte_len * 2 + 1] = HEX_CHARS_LOWER[(byte & 0x0f) as usize];
        }

        let data = if depth % 4 == 0 {
            &result[..(depth / 4) as usize]
        } else {
            let underscore = (depth / 4 + 1) as usize;
            result[underscore] = b'_';
            &result[..=underscore]
        };

        // SAFETY: result was constructed from valid ascii `HEX_CHARS_LOWER`
        let part = unsafe { std::str::from_utf8_unchecked(data) };
        f.write_str(part)
    }
}

impl<C: CellFamily> Store<C> for Anycast {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        builder.has_capacity(self.bit_len(), 0)
            && self.depth.store_into(builder, finalizer)
            && builder.store_raw(&self.rewrite_prefix, self.depth.into_bit_len())
    }
}

impl<'a, C: CellFamily> Load<'a, C> for Anycast {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let depth = SplitDepth::load_from(slice)?;
        if !slice.has_remaining(depth.into_bit_len(), 0) {
            return None;
        }

        let mut rewrite_prefix = Vec::with_capacity((depth.into_bit_len() as usize + 7) / 8);
        slice.load_raw(&mut rewrite_prefix, depth.into_bit_len())?;

        Some(Self {
            depth,
            rewrite_prefix,
        })
    }
}
