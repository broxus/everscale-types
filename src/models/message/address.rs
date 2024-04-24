use std::str::FromStr;

use crate::cell::*;
use crate::error::{Error, ParseAddrError};
use crate::models::block::ShardIdent;
use crate::num::*;
use crate::util::*;

/// Internal message address.
#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
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
    /// The maximum number of bits that address occupies.
    pub const BITS_MAX: u16 = 1 + VarAddr::BITS_MAX;

    /// Returns `true` if this address is for a masterchain block.
    ///
    /// See [`ShardIdent::MASTERCHAIN`]
    #[inline]
    pub const fn is_masterchain(&self) -> bool {
        self.workchain() == ShardIdent::MASTERCHAIN.workchain()
    }

    /// Returns the workchain part of the address.
    #[inline]
    pub const fn workchain(&self) -> i32 {
        match self {
            Self::Std(addr) => addr.workchain as i32,
            Self::Var(addr) => addr.workchain,
        }
    }

    /// Returns the workchain part of the address.
    #[inline]
    pub const fn anycast(&self) -> &Option<Box<Anycast>> {
        match self {
            Self::Std(addr) => &addr.anycast,
            Self::Var(addr) => &addr.anycast,
        }
    }

    /// Returns the underlying standard address.
    #[inline]
    pub const fn as_std(&self) -> Option<&StdAddr> {
        match self {
            Self::Std(addr) => Some(addr),
            Self::Var(_) => None,
        }
    }

    /// Returns the underlying variable-length address.
    #[inline]
    pub const fn as_var(&self) -> Option<&VarAddr> {
        match self {
            Self::Std(_) => None,
            Self::Var(addr) => Some(addr),
        }
    }

    /// Returns the number of data bits that this struct occupies.
    pub const fn bit_len(&self) -> u16 {
        match self {
            Self::Std(addr) => addr.bit_len(),
            Self::Var(addr) => addr.bit_len(),
        }
    }
}

impl From<(i8, HashBytes)> for IntAddr {
    #[inline]
    fn from((workchain, address): (i8, HashBytes)) -> Self {
        IntAddr::Std(StdAddr::new(workchain, address))
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

impl Store for IntAddr {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        match self {
            Self::Std(addr) => addr.store_into(builder, context),
            Self::Var(addr) => addr.store_into(builder, context),
        }
    }
}

impl<'a> Load<'a> for IntAddr {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        if !ok!(slice.load_bit()) {
            return Err(Error::InvalidTag);
        }

        Ok(if unlikely(ok!(slice.load_bit())) {
            let anycast = ok!(Option::<Box<Anycast>>::load_from(slice));
            let address_len = ok!(Uint9::load_from(slice));
            let workchain = ok!(slice.load_u32()) as i32;
            if !slice.has_remaining(address_len.into_inner(), 0) {
                return Err(Error::CellUnderflow);
            }

            let mut address = vec![0; (address_len.into_inner() as usize + 7) / 8];
            ok!(slice.load_raw(&mut address, address_len.into_inner()));

            Self::Var(VarAddr {
                anycast,
                address_len,
                workchain,
                address,
            })
        } else {
            Self::Std(StdAddr {
                anycast: ok!(Option::<Box<Anycast>>::load_from(slice)),
                workchain: ok!(slice.load_u8()) as i8,
                address: ok!(slice.load_u256()),
            })
        })
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for IntAddr {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Self::Std(addr) => addr.serialize(serializer),
            Self::Var(_) => {
                // TODO: impl serde for `VarAddr`
                serializer.serialize_str("varaddr")
            }
        }
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for IntAddr {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        // TODO: impl serde for `VarAddr`
        StdAddr::deserialize(deserializer).map(IntAddr::Std)
    }
}

/// Standard internal address.
#[derive(Debug, Default, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct StdAddr {
    /// Optional anycast info.
    pub anycast: Option<Box<Anycast>>,
    /// Workchain id (one-byte range).
    pub workchain: i8,
    /// Account id.
    pub address: HashBytes,
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
    pub const fn new(workchain: i8, address: HashBytes) -> Self {
        Self {
            anycast: None,
            workchain,
            address,
        }
    }

    /// Returns `true` if this address is for a masterchain block.
    ///
    /// See [`ShardIdent::MASTERCHAIN`]
    #[inline]
    pub const fn is_masterchain(&self) -> bool {
        self.workchain as i32 == ShardIdent::MASTERCHAIN.workchain()
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

        f.write_fmt(format_args!("{}:{}", self.workchain, self.address))
    }
}

impl From<(i8, HashBytes)> for StdAddr {
    #[inline]
    fn from((workchain, address): (i8, HashBytes)) -> Self {
        Self::new(workchain, address)
    }
}

impl From<(i8, [u8; 32])> for StdAddr {
    #[inline]
    fn from((workchain, address): (i8, [u8; 32])) -> Self {
        Self::new(workchain, HashBytes(address))
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
            Some(part) => match hex::decode_to_slice(part, &mut result.address.0) {
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

impl Store for StdAddr {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        if !builder.has_capacity(self.bit_len(), 0) {
            return Err(Error::CellOverflow);
        }
        ok!(builder.store_small_uint(0b10, 2));
        ok!(self.anycast.store_into(builder, context));
        ok!(builder.store_u8(self.workchain as u8));
        builder.store_u256(&self.address)
    }
}

impl<'a> Load<'a> for StdAddr {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        if !ok!(slice.load_bit()) || ok!(slice.load_bit()) {
            return Err(Error::InvalidTag);
        }

        Ok(Self {
            anycast: ok!(Option::<Box<Anycast>>::load_from(slice)),
            workchain: ok!(slice.load_u8()) as i8,
            address: ok!(slice.load_u256()),
        })
    }
}

impl crate::dict::DictKey for StdAddr {
    const BITS: u16 = StdAddr::BITS_WITHOUT_ANYCAST;

    fn from_raw_data([first_byte, second_byte, data @ ..]: &[u8; 128]) -> Option<Self> {
        // 2 bits id, 1 bit maybe (None), 8 bits workchain, 256 bits address

        const PREFIX_BITS: u8 = 0b1000_0000;
        const PREFIX_MASK: u8 = 0b1110_0000;

        const R: u8 = 3;
        const SHIFT: u8 = 8 - R;
        const REV_SHIFT: u8 = 120 + R;

        if unlikely((first_byte ^ PREFIX_BITS) & PREFIX_MASK != 0) {
            return None;
        }

        let mut result = Self {
            anycast: None,
            // 100xxxxx | xxxaaaaa -> xxxxxxxx
            workchain: ((first_byte << R) | (second_byte >> SHIFT)) as i8,
            address: HashBytes::ZERO,
        };

        // SAFETY: transmuting [u8; 32] to [u128; 2] is safe
        let [mut hi, mut lo]: [u128; 2] =
            unsafe { std::mem::transmute::<[u8; 32], _>(data[..32].try_into().unwrap()) };

        // Numbers are in big endian order, swap bytes on little endian arch
        #[cfg(target_endian = "little")]
        {
            hi = hi.swap_bytes();
            lo = lo.swap_bytes();
        }

        // SAFETY: transmuting [[u8; 16]; 2] to [u8; 32] is safe
        result.address = unsafe {
            std::mem::transmute([
                (hi >> SHIFT | ((*second_byte as u128) << REV_SHIFT)).to_be_bytes(),
                (lo >> SHIFT | (hi << REV_SHIFT)).to_be_bytes(),
            ])
        };

        Some(result)
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for StdAddr {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        if serializer.is_human_readable() {
            serializer.collect_str(self)
        } else {
            (self.workchain, &self.address).serialize(serializer)
        }
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for StdAddr {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::{Error, Visitor};

        struct StdAddrVisitor;

        impl<'de> Visitor<'de> for StdAddrVisitor {
            type Value = StdAddr;

            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                f.write_str("a standard address")
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: Error,
            {
                StdAddr::from_str(v).map_err(E::custom)
            }
        }

        if deserializer.is_human_readable() {
            deserializer.deserialize_str(StdAddrVisitor)
        } else {
            <(i8, HashBytes)>::deserialize(deserializer)
                .map(|(workchain, address)| Self::new(workchain, address))
        }
    }
}

/// Variable-length internal address.
#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
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

    /// Returns `true` if this address is for a masterchain block.
    ///
    /// See [`ShardIdent::MASTERCHAIN`]
    #[inline]
    pub const fn is_masterchain(&self) -> bool {
        self.workchain == ShardIdent::MASTERCHAIN.workchain()
    }

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

impl Store for VarAddr {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        if !builder.has_capacity(self.bit_len(), 0) {
            return Err(Error::CellOverflow);
        }
        ok!(builder.store_small_uint(0b11, 2));
        ok!(self.anycast.store_into(builder, context));
        ok!(self.address_len.store_into(builder, context));
        ok!(builder.store_u32(self.workchain as u32));
        builder.store_raw(&self.address, self.address_len.into_inner())
    }
}

/// External address.
///
/// ```text
/// addr_none$00 = MsgAddressExt;
/// addr_extern$01 len:(## 9) external_address:(bits len) = MsgAddressExt;
/// ```
#[derive(Debug, Default, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
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

impl std::fmt::Display for ExtAddr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let bitstring = Bitstring {
            bytes: &self.data,
            bit_len: self.data_bit_len.into_inner(),
        };
        std::fmt::Display::fmt(&bitstring, f)
    }
}

impl FromStr for ExtAddr {
    type Err = ParseAddrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.is_empty() {
            return Err(ParseAddrError::Empty);
        }

        let Some(s) = s.strip_prefix(':') else {
            return Err(ParseAddrError::UnexpectedPart);
        };

        let Ok((data, bit_len)) = Bitstring::from_hex_str(s) else {
            return Err(ParseAddrError::InvalidAccountId);
        };

        ExtAddr::new(bit_len, data).ok_or(ParseAddrError::UnexpectedPart)
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for ExtAddr {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if serializer.is_human_readable() {
            serializer.collect_str(self)
        } else {
            (self.data_bit_len.into_inner(), &self.data).serialize(serializer)
        }
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for ExtAddr {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        use serde::de::{Error, Visitor};

        struct ExtAddrVisitor;

        impl<'de> Visitor<'de> for ExtAddrVisitor {
            type Value = ExtAddr;

            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                f.write_str("an external address")
            }

            fn visit_str<E: Error>(self, v: &str) -> Result<Self::Value, E> {
                ExtAddr::from_str(v).map_err(E::custom)
            }
        }

        if deserializer.is_human_readable() {
            deserializer.deserialize_str(ExtAddrVisitor)
        } else {
            <(u16, Vec<u8>)>::deserialize(deserializer).and_then(|(data_bit_len, data)| {
                ExtAddr::new(data_bit_len, data)
                    .ok_or_else(|| Error::custom("invalid external address data length"))
            })
        }
    }
}

/// Anycast prefix info.
///
/// ```text
/// anycast_info$_ depth:(#<= 30) { depth >= 1 } rewrite_pfx:(bits depth) = Anycast;
/// ```
#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
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
    pub fn from_slice(rewrite_prefix: &CellSlice<'_>) -> Result<Self, Error> {
        let depth = ok!(SplitDepth::from_bit_len(rewrite_prefix.remaining_bits()));

        let mut data = vec![0; (depth.into_bit_len() as usize + 7) / 8];
        ok!(rewrite_prefix.get_raw(0, &mut data, depth.into_bit_len()));

        Ok(Self {
            depth,
            rewrite_prefix: data,
        })
    }

    /// Returns the number of data bits that this struct occupies.
    pub const fn bit_len(&self) -> u16 {
        SplitDepth::BITS + self.depth.into_bit_len()
    }
}

impl std::fmt::Display for Anycast {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let bitstring = Bitstring {
            bytes: &self.rewrite_prefix,
            bit_len: self.depth.into_bit_len(),
        };
        std::fmt::Display::fmt(&bitstring, f)
    }
}

impl Store for Anycast {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        if !builder.has_capacity(self.bit_len(), 0) {
            return Err(Error::CellOverflow);
        }
        ok!(self.depth.store_into(builder, context));
        builder.store_raw(&self.rewrite_prefix, self.depth.into_bit_len())
    }
}

impl<'a> Load<'a> for Anycast {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let depth = ok!(SplitDepth::load_from(slice));
        if !slice.has_remaining(depth.into_bit_len(), 0) {
            return Err(Error::CellUnderflow);
        }

        let mut rewrite_prefix = vec![0; (depth.into_bit_len() as usize + 7) / 8];
        ok!(slice.load_raw(&mut rewrite_prefix, depth.into_bit_len()));

        Ok(Self {
            depth,
            rewrite_prefix,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dict::Dict;

    #[test]
    fn dict_with_std_addr_keys() {
        let mut dict = Dict::<StdAddr, u32>::new();
        dict.set(StdAddr::new(-1, HashBytes([0x33; 32])), 123)
            .unwrap();
        dict.set(StdAddr::new(0, HashBytes([0x10; 32])), 321)
            .unwrap();
        dict.set(StdAddr::new(-1, HashBytes([0x55; 32])), 234)
            .unwrap();
        dict.set(StdAddr::new(0, HashBytes([0x20; 32])), 432)
            .unwrap();

        for entry in dict.iter() {
            let (addr, value) = entry.unwrap();
            println!("{addr}: {value}");
        }
    }

    #[test]
    fn anycast_str() {
        // 0 bit
        let empty_res = Anycast::from_slice(&Cell::empty_cell().as_slice().unwrap());
        assert_eq!(empty_res.unwrap_err(), Error::IntOverflow);

        // 1 bit
        let mut prefix = CellBuilder::new();
        prefix.store_bit_one().unwrap();
        let anycast = Anycast::from_slice(&prefix.as_data_slice()).unwrap();
        assert_eq!(anycast.to_string(), "c_");

        // 8 bit
        let mut prefix = CellBuilder::new();
        prefix.store_u8(0xa5).unwrap();
        let anycast = Anycast::from_slice(&prefix.as_data_slice()).unwrap();
        assert_eq!(anycast.to_string(), "a5");

        // 30 bit
        let mut prefix = CellBuilder::new();
        prefix.store_uint(0xb00b1e5, 28).unwrap();
        prefix.store_zeros(2).unwrap();
        let anycast = Anycast::from_slice(&prefix.as_data_slice()).unwrap();
        assert_eq!(anycast.to_string(), "b00b1e52_");
    }
}
