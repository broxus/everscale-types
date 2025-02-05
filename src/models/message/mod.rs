//! Message models.

use std::borrow::Borrow;

use crate::cell::*;
use crate::error::Error;
use crate::num::*;

use crate::models::account::StateInit;
use crate::models::currency::CurrencyCollection;

pub use self::address::*;
pub use self::envelope::*;
pub use self::in_message::*;
pub use self::out_message::*;

mod address;
mod envelope;
mod in_message;
mod out_message;
#[cfg(test)]
mod tests;

/// Blockchain message (with body as slice).
pub type Message<'a> = BaseMessage<MsgInfo, CellSlice<'a>>;

impl EquivalentRepr<OwnedMessage> for Message<'_> {}
impl EquivalentRepr<RelaxedMessage<'_>> for Message<'_> {}
impl EquivalentRepr<OwnedRelaxedMessage> for Message<'_> {}

/// Blockchain message (with body as slice parts).
pub type OwnedMessage = BaseMessage<MsgInfo, CellSliceParts>;

impl EquivalentRepr<Message<'_>> for OwnedMessage {}
impl EquivalentRepr<RelaxedMessage<'_>> for OwnedMessage {}
impl EquivalentRepr<OwnedRelaxedMessage> for OwnedMessage {}

/// Unfinished blockchain message (with body as slice).
pub type RelaxedMessage<'a> = BaseMessage<RelaxedMsgInfo, CellSlice<'a>>;

impl EquivalentRepr<Message<'_>> for RelaxedMessage<'_> {}
impl EquivalentRepr<OwnedMessage> for RelaxedMessage<'_> {}
impl EquivalentRepr<OwnedRelaxedMessage> for RelaxedMessage<'_> {}

/// Unfinished blockchain message (with body as slice parts).
pub type OwnedRelaxedMessage = BaseMessage<RelaxedMsgInfo, CellSliceParts>;

impl EquivalentRepr<Message<'_>> for OwnedRelaxedMessage {}
impl EquivalentRepr<OwnedMessage> for OwnedRelaxedMessage {}
impl EquivalentRepr<RelaxedMessage<'_>> for OwnedRelaxedMessage {}

/// Blockchain message.
#[derive(Debug, Clone)]
pub struct BaseMessage<I, B> {
    /// Message info.
    pub info: I,
    /// Optional state init.
    pub init: Option<StateInit>,
    /// Optional payload.
    pub body: B,
    /// Optional message layout.
    pub layout: Option<MessageLayout>,
}

#[cfg(feature = "serde")]
impl<I, B> serde::Serialize for BaseMessage<I, B>
where
    I: ExactSize + Store + serde::Serialize,
    B: ExactSize + StoreBody,
{
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::{Error, SerializeStruct};

        struct BodySerializer<'a, B: StoreBody>(&'a B);

        impl<B: StoreBody> serde::Serialize for BodySerializer<'_, B> {
            fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                let mut builder = CellBuilder::new();
                ok!(self
                    .0
                    .store_body(false, &mut builder, Cell::empty_context())
                    .map_err(Error::custom));
                let cell = ok!(builder.build().map_err(Error::custom));
                crate::boc::Boc::serialize(&cell, serializer)
            }
        }

        if serializer.is_human_readable() {
            let mut ser = ok!(serializer.serialize_struct("Message", 4));
            ok!(ser.serialize_field("info", &self.info));
            ok!(ser.serialize_field("init", &self.init));
            ok!(ser.serialize_field("body", &BodySerializer(&self.body)));
            ok!(ser.serialize_field("layout", &self.layout));
            ser.end()
        } else {
            crate::boc::BocRepr::serialize(self, serializer)
        }
    }
}

#[cfg(feature = "serde")]
impl<'de, I> serde::Deserialize<'de> for BaseMessage<I, CellSliceParts>
where
    for<'a> I: ExactSize + Load<'a> + serde::Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(serde::Deserialize)]
        struct Message<I> {
            info: I,
            #[serde(default)]
            init: Option<StateInit>,
            #[serde(with = "crate::boc::Boc", default)]
            body: Cell,
            #[serde(default)]
            layout: Option<MessageLayout>,
        }

        if deserializer.is_human_readable() {
            let msg = Message::deserialize(deserializer)?;
            let body_range = CellSliceRange::full(msg.body.as_ref());
            Ok(Self {
                info: msg.info,
                init: msg.init,
                body: (msg.body, body_range),
                layout: msg.layout,
            })
        } else {
            crate::boc::BocRepr::deserialize(deserializer)
        }
    }
}

impl<I: Borrow<MsgInfo>, B> BaseMessage<I, B> {
    /// Returns the type of this message.
    pub fn ty(&self) -> MsgType {
        self.info.borrow().ty()
    }
}

impl<I: ExactSize, B: ExactSize> BaseMessage<I, B> {
    /// Computes the most optimal layout of the message parts.
    pub fn compute_layout(info: &I, init: Option<&StateInit>, body: &B) -> MessageLayout {
        let (layout, ..) = MessageLayout::compute(info.exact_size(), init, body.exact_size());
        layout
    }
}

impl<I, B> Store for BaseMessage<I, B>
where
    I: Store + ExactSize,
    B: StoreBody + ExactSize,
{
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        let info_size = self.info.exact_size();
        let body_size = self.body.exact_size();
        let (layout, size) = match self.layout {
            Some(layout) => {
                let size = layout.compute_full_size(info_size, self.init.as_ref(), body_size);
                (layout, size)
            }
            None => MessageLayout::compute(info_size, self.init.as_ref(), body_size),
        };
        let Size { bits, refs } = size;

        // Check capacity
        if !builder.has_capacity(bits, refs) {
            return Err(Error::CellOverflow);
        }

        // Try to store info
        ok!(self.info.store_into(builder, context));

        // Try to store init
        ok!(match &self.init {
            Some(value) => {
                ok!(builder.store_bit_one()); // just$1
                SliceOrCell {
                    to_cell: layout.init_to_cell,
                    value,
                }
                .store_into(builder, context)
            }
            None => builder.store_bit_zero(), // nothing$0
        });

        // Try to store body
        ok!(builder.store_bit(layout.body_to_cell));
        self.body.store_body(layout.body_to_cell, builder, context)
    }
}

impl<'a, I, B> Load<'a> for BaseMessage<I, B>
where
    I: Load<'a>,
    B: LoadBody<'a>,
{
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let info = ok!(I::load_from(slice));
        let init = ok!(Option::<SliceOrCell<StateInit>>::load_from(slice));

        let body_to_cell = ok!(slice.load_bit());
        let body = ok!(B::load_body(body_to_cell, slice));

        let (init, init_to_cell) = match init {
            Some(SliceOrCell { to_cell, value }) => (Some(value), to_cell),
            None => (None, false),
        };

        let layout = MessageLayout {
            init_to_cell,
            body_to_cell,
        };

        Ok(Self {
            info,
            init,
            body,
            layout: Some(layout),
        })
    }
}

trait StoreBody {
    fn store_body(
        &self,
        to_cell: bool,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error>;
}

impl StoreBody for CellSlice<'_> {
    fn store_body(
        &self,
        to_cell: bool,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        SliceOrCell {
            to_cell,
            value: self,
        }
        .store_only_value_into(builder, context)
    }
}

impl StoreBody for CellSliceParts {
    fn store_body(
        &self,
        to_cell: bool,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        let (cell, range) = self;
        if to_cell && range.is_full(cell.as_ref()) {
            builder.store_reference(cell.clone())
        } else {
            SliceOrCell {
                to_cell,
                value: ok!(range.apply(cell)),
            }
            .store_only_value_into(builder, context)
        }
    }
}

trait LoadBody<'a>: Sized {
    fn load_body(from_cell: bool, slice: &mut CellSlice<'a>) -> Result<Self, Error>;
}

impl<'a> LoadBody<'a> for CellSlice<'a> {
    fn load_body(from_cell: bool, slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        if from_cell {
            slice.load_reference_as_slice()
        } else {
            Ok(slice.load_remaining())
        }
    }
}

impl<'a> LoadBody<'a> for CellSliceParts {
    fn load_body(from_cell: bool, slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let body = ok!(if from_cell {
            slice.load_reference_cloned()
        } else {
            let slice = slice.load_remaining();
            let mut builder = CellBuilder::new();
            ok!(builder.store_slice(slice));
            builder.build()
        });

        let range = CellSliceRange::full(body.as_ref());
        Ok((body, range))
    }
}

struct SliceOrCell<T> {
    to_cell: bool,
    value: T,
}

impl<T: Store> SliceOrCell<T> {
    fn store_only_value_into(
        &self,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        if self.to_cell {
            let cell = {
                let mut builder = CellBuilder::new();
                ok!(self.value.store_into(&mut builder, context));
                ok!(builder.build_ext(context))
            };
            builder.store_reference(cell)
        } else {
            self.value.store_into(builder, context)
        }
    }
}

impl<T: Store> Store for SliceOrCell<T> {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_bit(self.to_cell));
        self.store_only_value_into(builder, context)
    }
}

impl<'a, T: Load<'a>> Load<'a> for SliceOrCell<T> {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let to_cell = ok!(slice.load_bit());

        let mut child_cell = if to_cell {
            Some(ok!(slice.load_reference_as_slice()))
        } else {
            None
        };

        let slice = match &mut child_cell {
            Some(slice) => slice,
            None => slice,
        };

        Ok(Self {
            to_cell,
            value: ok!(T::load_from(slice)),
        })
    }
}

/// Message payload layout.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MessageLayout {
    /// Whether to store state init in a child cell.
    pub init_to_cell: bool,
    /// Whether to store payload as a child cell.
    pub body_to_cell: bool,
}

impl MessageLayout {
    /// Returns a plain message layout (init and body stored in the root cell).
    #[inline]
    pub const fn plain() -> Self {
        Self {
            init_to_cell: false,
            body_to_cell: false,
        }
    }

    /// Computes the number of bits and refs for this layout for the root cell.
    pub const fn compute_full_size(
        &self,
        info_size: Size,
        init: Option<&StateInit>,
        body_size: Size,
    ) -> Size {
        let l = DetailedMessageLayout::compute(info_size, init, body_size);

        let mut total = l.info;

        // Append init bits and refs
        if self.init_to_cell {
            total.refs += 1;
        } else {
            total.bits += l.init.bits;
            total.refs += l.init.refs;
        }

        // Append body bits and refs
        if self.body_to_cell {
            total.refs += 1;
        } else {
            total.bits += l.body.bits;
            total.refs += l.body.refs;
        }

        total
    }

    /// Computes the most optimal layout of the message parts.
    /// Also returns the number of bits and refs for the root cell.
    pub const fn compute(
        info_size: Size,
        init: Option<&StateInit>,
        body_size: Size,
    ) -> (Self, Size) {
        let l = DetailedMessageLayout::compute(info_size, init, body_size);

        // Try plain layout
        let total_bits = l.info.bits + l.init.bits + l.body.bits;
        let total_refs = l.info.refs + l.init.refs + l.body.refs;
        if total_bits <= MAX_BIT_LEN && total_refs <= MAX_REF_COUNT as u8 {
            let layout = Self {
                init_to_cell: false,
                body_to_cell: false,
            };
            return (
                layout,
                Size {
                    bits: total_bits,
                    refs: total_refs,
                },
            );
        }

        // Try body to ref
        let total_bits = l.info.bits + l.init.bits;
        let total_refs = l.info.refs + l.init.refs;
        if total_bits <= MAX_BIT_LEN && total_refs < MAX_REF_COUNT as u8 {
            let layout = Self {
                init_to_cell: false,
                body_to_cell: true,
            };
            return (
                layout,
                Size {
                    bits: total_bits,
                    refs: total_refs + 1,
                },
            );
        }

        // Try init to ref
        let total_bits = l.info.bits + l.body.bits;
        let total_refs = l.info.refs + l.body.refs;
        if total_bits <= MAX_BIT_LEN && total_refs < MAX_REF_COUNT as u8 {
            let layout = Self {
                init_to_cell: true,
                body_to_cell: false,
            };
            return (
                layout,
                Size {
                    bits: total_bits,
                    refs: total_refs + 1,
                },
            );
        }

        // Fallback to init and body to ref
        let layout = Self {
            init_to_cell: true,
            body_to_cell: true,
        };
        (
            layout,
            Size {
                bits: l.info.bits,
                refs: l.info.refs + 2,
            },
        )
    }
}

struct DetailedMessageLayout {
    info: Size,
    init: Size,
    body: Size,
}

impl DetailedMessageLayout {
    const fn compute(mut info: Size, init: Option<&StateInit>, body: Size) -> Self {
        info.bits += 2; // (Maybe X) (1bit) + (Either X) (1bit)

        let init = match init {
            Some(init) => {
                info.bits += 1; // (Either X) (1bit)
                init.exact_size_const()
            }
            None => Size::ZERO,
        };

        Self { info, init, body }
    }
}

/// Unfinalized message info.
#[derive(Debug, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(tag = "ty"))]
pub enum RelaxedMsgInfo {
    /// Internal message info,
    Int(RelaxedIntMsgInfo),
    /// External outgoing message info,
    ExtOut(RelaxedExtOutMsgInfo),
}

impl RelaxedMsgInfo {
    /// Exact size of this value when it is stored in slice.
    pub const fn exact_size_const(&self) -> Size {
        Size {
            bits: self.bit_len(),
            refs: self.has_references() as u8,
        }
    }

    /// Returns the number of data bits that this struct occupies.
    const fn bit_len(&self) -> u16 {
        match self {
            Self::Int(info) => info.bit_len(),
            Self::ExtOut(info) => info.bit_len(),
        }
    }

    const fn has_references(&self) -> bool {
        match self {
            Self::Int(info) => !info.value.other.is_empty(),
            _ => false,
        }
    }
}

impl ExactSize for RelaxedMsgInfo {
    #[inline]
    fn exact_size(&self) -> Size {
        self.exact_size_const()
    }
}

impl Store for RelaxedMsgInfo {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        match self {
            Self::Int(info) => {
                ok!(builder.store_bit_zero());
                info.store_into(builder, context)
            }
            Self::ExtOut(info) => {
                ok!(builder.store_small_uint(0b11, 2));
                info.store_into(builder, context)
            }
        }
    }
}

impl<'a> Load<'a> for RelaxedMsgInfo {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        Ok(if !ok!(slice.load_bit()) {
            match RelaxedIntMsgInfo::load_from(slice) {
                Ok(info) => Self::Int(info),
                Err(e) => return Err(e),
            }
        } else if ok!(slice.load_bit()) {
            match RelaxedExtOutMsgInfo::load_from(slice) {
                Ok(info) => Self::ExtOut(info),
                Err(e) => return Err(e),
            }
        } else {
            return Err(Error::InvalidTag);
        })
    }
}

/// Message type.
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub enum MsgType {
    /// Internal message.
    Int,
    /// External incoming message.
    ExtIn,
    /// External outgoing message.
    ExtOut,
}

impl MsgType {
    /// Returns whether this message is internal.
    pub const fn is_internal(&self) -> bool {
        matches!(self, Self::Int)
    }

    /// Returns whether this message is external incoming.
    pub const fn is_external_in(&self) -> bool {
        matches!(self, Self::ExtIn)
    }

    /// Returns whether this message is external outgoing.
    pub const fn is_external_out(&self) -> bool {
        matches!(self, Self::ExtOut)
    }
}

impl Store for MsgType {
    fn store_into(&self, b: &mut CellBuilder, _: &dyn CellContext) -> Result<(), Error> {
        match self {
            Self::Int => b.store_bit_zero(),
            Self::ExtIn => b.store_small_uint(0b10, 2),
            Self::ExtOut => b.store_small_uint(0b11, 2),
        }
    }
}

impl<'a> Load<'a> for MsgType {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        Ok(if !ok!(slice.load_bit()) {
            Self::Int
        } else if !ok!(slice.load_bit()) {
            Self::ExtIn
        } else {
            Self::ExtOut
        })
    }
}

/// Message info.
#[derive(Debug, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(tag = "ty"))]
pub enum MsgInfo {
    /// Internal message info,
    Int(IntMsgInfo),
    /// External incoming message info.
    ExtIn(ExtInMsgInfo),
    /// External outgoing message info,
    ExtOut(ExtOutMsgInfo),
}

impl MsgInfo {
    /// Returns the type of this message info.
    pub const fn ty(&self) -> MsgType {
        match self {
            Self::Int(_) => MsgType::Int,
            Self::ExtIn(_) => MsgType::ExtIn,
            Self::ExtOut(_) => MsgType::ExtOut,
        }
    }

    /// Returns whether this message is internal.
    pub const fn is_internal(&self) -> bool {
        matches!(self, Self::Int(_))
    }

    /// Returns whether this message is external incoming.
    pub const fn is_external_in(&self) -> bool {
        matches!(self, Self::ExtIn(_))
    }

    /// Returns whether this message is external outgoing.
    pub const fn is_external_out(&self) -> bool {
        matches!(self, Self::ExtOut(_))
    }

    /// Exact size of this value when it is stored in slice.
    pub const fn exact_size_const(&self) -> Size {
        Size {
            bits: self.bit_len(),
            refs: self.has_references() as u8,
        }
    }

    /// Returns the number of data bits that this struct occupies.
    const fn bit_len(&self) -> u16 {
        match self {
            Self::Int(info) => info.bit_len(),
            Self::ExtIn(info) => info.bit_len(),
            Self::ExtOut(info) => info.bit_len(),
        }
    }

    const fn has_references(&self) -> bool {
        match self {
            Self::Int(info) => !info.value.other.is_empty(),
            _ => false,
        }
    }
}

impl ExactSize for MsgInfo {
    #[inline]
    fn exact_size(&self) -> Size {
        self.exact_size_const()
    }
}

impl Store for MsgInfo {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        match self {
            Self::Int(info) => {
                ok!(builder.store_bit_zero());
                info.store_into(builder, context)
            }
            Self::ExtIn(info) => {
                ok!(builder.store_small_uint(0b10, 2));
                info.store_into(builder, context)
            }
            Self::ExtOut(info) => {
                ok!(builder.store_small_uint(0b11, 2));
                info.store_into(builder, context)
            }
        }
    }
}

impl<'a> Load<'a> for MsgInfo {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        Ok(if !ok!(slice.load_bit()) {
            match IntMsgInfo::load_from(slice) {
                Ok(info) => Self::Int(info),
                Err(e) => return Err(e),
            }
        } else if !ok!(slice.load_bit()) {
            match ExtInMsgInfo::load_from(slice) {
                Ok(info) => Self::ExtIn(info),
                Err(e) => return Err(e),
            }
        } else {
            match ExtOutMsgInfo::load_from(slice) {
                Ok(info) => Self::ExtOut(info),
                Err(e) => return Err(e),
            }
        })
    }
}

impl From<IntMsgInfo> for MsgInfo {
    #[inline]
    fn from(value: IntMsgInfo) -> Self {
        Self::Int(value)
    }
}

impl From<ExtInMsgInfo> for MsgInfo {
    #[inline]
    fn from(value: ExtInMsgInfo) -> Self {
        Self::ExtIn(value)
    }
}

impl From<ExtOutMsgInfo> for MsgInfo {
    #[inline]
    fn from(value: ExtOutMsgInfo) -> Self {
        Self::ExtOut(value)
    }
}

/// Internal message info.
#[derive(Debug, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IntMsgInfo {
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
    pub value: CurrencyCollection,
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

impl Default for IntMsgInfo {
    fn default() -> Self {
        Self {
            ihr_disabled: true,
            bounce: false,
            bounced: false,
            src: Default::default(),
            dst: Default::default(),
            value: CurrencyCollection::ZERO,
            ihr_fee: Default::default(),
            fwd_fee: Default::default(),
            created_lt: 0,
            created_at: 0,
        }
    }
}

impl IntMsgInfo {
    /// Returns the number of data bits that this struct occupies.
    pub const fn bit_len(&self) -> u16 {
        3 + self.src.bit_len()
            + self.dst.bit_len()
            + self.value.bit_len()
            + self.ihr_fee.unwrap_bit_len()
            + self.fwd_fee.unwrap_bit_len()
            + 64
            + 32
    }
}

impl Store for IntMsgInfo {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        let flags =
            ((self.ihr_disabled as u8) << 2) | ((self.bounce as u8) << 1) | self.bounced as u8;
        ok!(builder.store_small_uint(flags, 3));
        ok!(self.src.store_into(builder, context));
        ok!(self.dst.store_into(builder, context));
        ok!(self.value.store_into(builder, context));
        ok!(self.ihr_fee.store_into(builder, context));
        ok!(self.fwd_fee.store_into(builder, context));
        ok!(builder.store_u64(self.created_lt));
        builder.store_u32(self.created_at)
    }
}

impl<'a> Load<'a> for IntMsgInfo {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let flags = ok!(slice.load_small_uint(3));
        Ok(Self {
            ihr_disabled: flags & 0b100 != 0,
            bounce: flags & 0b010 != 0,
            bounced: flags & 0b001 != 0,
            src: ok!(IntAddr::load_from(slice)),
            dst: ok!(IntAddr::load_from(slice)),
            value: ok!(CurrencyCollection::load_from(slice)),
            ihr_fee: ok!(Tokens::load_from(slice)),
            fwd_fee: ok!(Tokens::load_from(slice)),
            created_lt: ok!(slice.load_u64()),
            created_at: ok!(slice.load_u32()),
        })
    }
}

/// Unfinished internal message info.
#[derive(Debug, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct RelaxedIntMsgInfo {
    /// Whether IHR is disabled for the message.
    pub ihr_disabled: bool,
    /// Whether to bounce this message back if the destination transaction fails.
    pub bounce: bool,
    /// Whether this message is a bounced message from some failed transaction.
    pub bounced: bool,
    /// Optional internal source address.
    pub src: Option<IntAddr>,
    /// Internal destination address.
    pub dst: IntAddr,
    /// Attached amounts.
    pub value: CurrencyCollection,
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

impl Default for RelaxedIntMsgInfo {
    fn default() -> Self {
        Self {
            ihr_disabled: true,
            bounce: false,
            bounced: false,
            src: Default::default(),
            dst: Default::default(),
            value: CurrencyCollection::ZERO,
            ihr_fee: Default::default(),
            fwd_fee: Default::default(),
            created_lt: 0,
            created_at: 0,
        }
    }
}

impl RelaxedIntMsgInfo {
    /// Returns the number of data bits that this struct occupies.
    pub const fn bit_len(&self) -> u16 {
        3 + compute_opt_int_addr_bit_len(&self.src)
            + self.dst.bit_len()
            + self.value.bit_len()
            + self.ihr_fee.unwrap_bit_len()
            + self.fwd_fee.unwrap_bit_len()
            + 64
            + 32
    }
}

impl Store for RelaxedIntMsgInfo {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        let flags =
            ((self.ihr_disabled as u8) << 2) | ((self.bounce as u8) << 1) | self.bounced as u8;
        ok!(builder.store_small_uint(flags, 3));
        ok!(store_opt_int_addr(builder, context, &self.src));
        ok!(self.dst.store_into(builder, context));
        ok!(self.value.store_into(builder, context));
        ok!(self.ihr_fee.store_into(builder, context));
        ok!(self.fwd_fee.store_into(builder, context));
        ok!(builder.store_u64(self.created_lt));
        builder.store_u32(self.created_at)
    }
}

impl<'a> Load<'a> for RelaxedIntMsgInfo {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let flags = ok!(slice.load_small_uint(3));
        Ok(Self {
            ihr_disabled: flags & 0b100 != 0,
            bounce: flags & 0b010 != 0,
            bounced: flags & 0b001 != 0,
            src: ok!(load_opt_int_addr(slice)),
            dst: ok!(IntAddr::load_from(slice)),
            value: ok!(CurrencyCollection::load_from(slice)),
            ihr_fee: ok!(Tokens::load_from(slice)),
            fwd_fee: ok!(Tokens::load_from(slice)),
            created_lt: ok!(slice.load_u64()),
            created_at: ok!(slice.load_u32()),
        })
    }
}

/// External incoming message info.
#[derive(Debug, Default, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ExtInMsgInfo {
    /// Optional external source address.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
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
        2 + compute_ext_addr_bit_len(&self.src)
            + self.dst.bit_len()
            + self.import_fee.unwrap_bit_len()
    }
}

impl Store for ExtInMsgInfo {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        if !self.import_fee.is_valid() {
            return Err(Error::InvalidData);
        }
        if !builder.has_capacity(self.bit_len(), 0) {
            return Err(Error::CellOverflow);
        }
        ok!(store_ext_addr(builder, context, &self.src));
        ok!(self.dst.store_into(builder, context));
        self.import_fee.store_into(builder, context)
    }
}

impl<'a> Load<'a> for ExtInMsgInfo {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        Ok(Self {
            src: ok!(load_ext_addr(slice)),
            dst: ok!(IntAddr::load_from(slice)),
            import_fee: ok!(Tokens::load_from(slice)),
        })
    }
}

/// External outgoing message info.
#[derive(Debug, Default, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ExtOutMsgInfo {
    /// Internal source address.
    pub src: IntAddr,
    /// Optional external address.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
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

impl Store for ExtOutMsgInfo {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        if !builder.has_capacity(self.bit_len(), 0) {
            return Err(Error::CellOverflow);
        }
        ok!(self.src.store_into(builder, context));
        ok!(store_ext_addr(builder, context, &self.dst));
        ok!(builder.store_u64(self.created_lt));
        builder.store_u32(self.created_at)
    }
}

impl<'a> Load<'a> for ExtOutMsgInfo {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        Ok(Self {
            src: ok!(IntAddr::load_from(slice)),
            dst: ok!(load_ext_addr(slice)),
            created_lt: ok!(slice.load_u64()),
            created_at: ok!(slice.load_u32()),
        })
    }
}

/// Unfinalized external outgoing message info.
#[derive(Debug, Default, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct RelaxedExtOutMsgInfo {
    /// Optional internal source address.
    pub src: Option<IntAddr>,
    /// Optional external address.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub dst: Option<ExtAddr>,
    /// Logical time when the message was created.
    pub created_lt: u64,
    /// Unix timestamp when the message was created.
    pub created_at: u32,
}

impl RelaxedExtOutMsgInfo {
    /// Returns the number of data bits that this struct occupies.
    pub const fn bit_len(&self) -> u16 {
        2 + compute_opt_int_addr_bit_len(&self.src) + compute_ext_addr_bit_len(&self.dst) + 64 + 32
    }
}

impl Store for RelaxedExtOutMsgInfo {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        ok!(store_opt_int_addr(builder, context, &self.src));
        ok!(store_ext_addr(builder, context, &self.dst));
        ok!(builder.store_u64(self.created_lt));
        builder.store_u32(self.created_at)
    }
}

impl<'a> Load<'a> for RelaxedExtOutMsgInfo {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        Ok(Self {
            src: ok!(load_opt_int_addr(slice)),
            dst: ok!(load_ext_addr(slice)),
            created_lt: ok!(slice.load_u64()),
            created_at: ok!(slice.load_u32()),
        })
    }
}

const fn compute_ext_addr_bit_len(addr: &Option<ExtAddr>) -> u16 {
    match addr {
        Some(addr) => 2 + addr.bit_len(),
        None => 2,
    }
}

fn store_ext_addr(
    builder: &mut CellBuilder,
    context: &dyn CellContext,
    addr: &Option<ExtAddr>,
) -> Result<(), Error> {
    match addr {
        None => builder.store_zeros(2),
        Some(ExtAddr { data_bit_len, data }) => {
            if !builder.has_capacity(2 + Uint9::BITS + data_bit_len.into_inner(), 0) {
                return Err(Error::CellOverflow);
            }
            ok!(builder.store_bit_zero());
            ok!(builder.store_bit_one());
            ok!(data_bit_len.store_into(builder, context));
            builder.store_raw(data, data_bit_len.into_inner())
        }
    }
}

fn load_ext_addr(slice: &mut CellSlice<'_>) -> Result<Option<ExtAddr>, Error> {
    if ok!(slice.load_bit()) {
        return Err(Error::InvalidTag);
    }

    if !ok!(slice.load_bit()) {
        return Ok(None);
    }

    let data_bit_len = ok!(Uint9::load_from(slice));
    if !slice.has_remaining(data_bit_len.into_inner(), 0) {
        return Err(Error::CellUnderflow);
    }

    let mut data = vec![0; (data_bit_len.into_inner() as usize + 7) / 8];
    ok!(slice.load_raw(&mut data, data_bit_len.into_inner()));
    Ok(Some(ExtAddr { data_bit_len, data }))
}

const fn compute_opt_int_addr_bit_len(addr: &Option<IntAddr>) -> u16 {
    match addr {
        Some(src) => src.bit_len(),
        None => 2,
    }
}

fn store_opt_int_addr(
    builder: &mut CellBuilder,
    context: &dyn CellContext,
    addr: &Option<IntAddr>,
) -> Result<(), Error> {
    match addr {
        Some(addr) => addr.store_into(builder, context),
        None => builder.store_zeros(2),
    }
}

fn load_opt_int_addr(slice: &mut CellSlice<'_>) -> Result<Option<IntAddr>, Error> {
    if ok!(slice.get_bit(0)) {
        IntAddr::load_from(slice).map(Some)
    } else if ok!(slice.load_small_uint(2)) == 0b00 {
        Ok(None)
    } else {
        Err(Error::InvalidTag)
    }
}
