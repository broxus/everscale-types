//! Message models.

use crate::cell::*;
use crate::num::*;
use crate::util::{unlikely, DisplayHash};

use super::account::{CurrencyCollection, StateInit};

/// Blockchain message.
pub struct Message<C: CellFamily> {
    /// Message info.
    pub info: MsgInfo<C>,
    /// Optional state init.
    pub init: Option<StateInit<C>>,
    /// Optional payload.
    pub body: Option<CellContainer<C>>,
}

// impl<C: CellFamily> Store<C> for Message<C> {
//     fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
//         todo!()
//     }
// }

/// Message info.
pub enum MsgInfo<C: CellFamily> {
    /// Internal message info,
    Int(IntMsgInfo<C>),
    /// External incoming message info.
    ExtIn(ExtInMsgInfo),
    /// External outgoing message info,
    ExtOut(ExtOutMsgInfo),
}

impl<C: CellFamily> Store<C> for MsgInfo<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        match self {
            Self::Int(info) => builder.store_bit_zero() && info.store_into(builder, finalizer),
            Self::ExtIn(info) => {
                builder.store_small_uint(0b10, 2) && info.store_into(builder, finalizer)
            }
            Self::ExtOut(info) => {
                builder.store_small_uint(0b11, 2) && info.store_into(builder, finalizer)
            }
        }
    }
}

/// Internal message info.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct IntMsgInfo<C: CellFamily> {
    /// Whether IHR is disabled for the message.
    pub ihr_disabled: bool,
    /// Whether to bounce this message back if the destination transaction fails.
    pub bounce: bool,
    /// Whether this message is a bounced message from some failed transaction.
    pub bounced: bool,
    /// Internal source address.
    pub src: IntAddr,
    /// Internal destination address.
    pub dst: IntAddr,
    /// Attached amounts.
    pub value: CurrencyCollection<C>,
    /// IHR fee.
    ///
    /// NOTE: currently unused, but can be used to split attached amount.
    pub ihr_fee: Tokens,
    /// Forwarding fee paid for using the routing.
    pub fwd_fee: Tokens,
    /// Logical time when the message was created.
    pub created_lt: u64,
    /// Unix timestamp when the message was created.
    pub created_at: u32,
}

impl<C: CellFamily> Store<C> for IntMsgInfo<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        let flags =
            ((self.ihr_disabled as u8) << 2) | ((self.bounce as u8) << 1) | self.bounced as u8;
        builder.store_small_uint(flags, 3)
            && self.src.store_into(builder, finalizer)
            && self.dst.store_into(builder, finalizer)
            && self.value.store_into(builder, finalizer)
            && self.ihr_fee.store_into(builder, finalizer)
            && self.fwd_fee.store_into(builder, finalizer)
            && builder.store_u64(self.created_lt)
            && builder.store_u32(self.created_at)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for IntMsgInfo<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let flags = slice.load_small_uint(3)?;
        Some(Self {
            ihr_disabled: flags & 0b100 != 0,
            bounce: flags & 0b010 != 0,
            bounced: flags & 0b001 != 0,
            src: IntAddr::load_from(slice)?,
            dst: IntAddr::load_from(slice)?,
            value: CurrencyCollection::load_from(slice)?,
            ihr_fee: Tokens::load_from(slice)?,
            fwd_fee: Tokens::load_from(slice)?,
            created_lt: slice.load_u64()?,
            created_at: slice.load_u32()?,
        })
    }
}

/// External incoming message info.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ExtInMsgInfo {
    /// Optional external source address.
    pub src: Option<ExtAddr>,
    /// Internal destination address.
    pub dst: IntAddr,
    /// External message import fee.
    ///
    /// NOTE: currently unused and reserved for future use.
    pub import_fee: Tokens,
}

impl ExtInMsgInfo {
    /// Returns the number of data bits that this struct occupies.
    pub const fn bit_len(&self) -> u16 {
        let import_fee_bit_len = match self.import_fee.bit_len() {
            Some(bit_len) => bit_len,
            None => Tokens::MAX_BITS, // fallback to max length for invalid import fee
        };
        2 + compute_ext_addr_bit_len(&self.src) + self.dst.bit_len() + import_fee_bit_len
    }
}

impl<C: CellFamily> Store<C> for ExtInMsgInfo {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        if !self.import_fee.is_valid() {
            return false;
        }
        builder.has_capacity(self.bit_len(), 0)
            && store_ext_addr(builder, finalizer, &self.src)
            && self.dst.store_into(builder, finalizer)
            && self.import_fee.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ExtInMsgInfo {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            src: load_ext_addr(slice)?,
            dst: IntAddr::load_from(slice)?,
            import_fee: Tokens::load_from(slice)?,
        })
    }
}

/// External outgoing message info.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ExtOutMsgInfo {
    /// Internal source address.
    pub src: IntAddr,
    /// Optional external address.
    pub dst: Option<ExtAddr>,
    /// Logical time when the message was created.
    pub created_lt: u64,
    /// Unix timestamp when the message was created.
    pub created_at: u32,
}

impl ExtOutMsgInfo {
    /// Returns the number of data bits that this struct occupies.
    pub const fn bit_len(&self) -> u16 {
        2 + self.src.bit_len() + compute_ext_addr_bit_len(&self.dst) + 64 + 32
    }
}

impl<C: CellFamily> Store<C> for ExtOutMsgInfo {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        builder.has_capacity(self.bit_len(), 0)
            && builder.store_small_uint(0b11, 2)
            && self.src.store_into(builder, finalizer)
            && store_ext_addr(builder, finalizer, &self.dst)
            && builder.store_u64(self.created_lt)
            && builder.store_u32(self.created_at)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ExtOutMsgInfo {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            src: IntAddr::load_from(slice)?,
            dst: load_ext_addr(slice)?,
            created_lt: slice.load_u64()?,
            created_at: slice.load_u32()?,
        })
    }
}

/// Internal message address.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum IntAddr {
    /// Standard internal address.
    Std(StdAddr),
    /// Variable-length internal address.
    Var(VarAddr),
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

const fn compute_ext_addr_bit_len(addr: &Option<ExtAddr>) -> u16 {
    match addr {
        Some(addr) => 2 + addr.bit_len(),
        None => 2,
    }
}

#[inline]
fn store_ext_addr<C: CellFamily>(
    builder: &mut CellBuilder<C>,
    finalizer: &mut dyn Finalizer<C>,
    addr: &Option<ExtAddr>,
) -> bool {
    match addr {
        None => builder.store_zeros(2),
        Some(ExtAddr { data_bit_len, data }) => {
            builder.has_capacity(2 + Uint9::BITS + data_bit_len.into_inner(), 0)
                && builder.store_bit_zero()
                && builder.store_bit_one()
                && data_bit_len.store_into(builder, finalizer)
                && builder.store_raw(data, data_bit_len.into_inner())
        }
    }
}

#[inline]
fn load_ext_addr<C: CellFamily>(slice: &mut CellSlice<'_, C>) -> Option<Option<ExtAddr>> {
    if slice.load_bit()? {
        return None;
    }

    if !slice.load_bit()? {
        return Some(None);
    }

    let data_bit_len = Uint9::load_from(slice)?;
    if !slice.has_remaining(data_bit_len.into_inner(), 0) {
        return None;
    }

    let mut data = Vec::with_capacity((data_bit_len.into_inner() as usize + 7) / 8);
    slice.load_raw(&mut data, data_bit_len.into_inner())?;
    Some(Some(ExtAddr { data_bit_len, data }))
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
