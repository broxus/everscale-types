//! Message models.

use crate::cell::*;
use crate::error::Error;
use crate::num::*;

use crate::models::account::StateInit;
use crate::models::currency::CurrencyCollection;

pub use self::address::*;

mod address;

#[cfg(test)]
mod tests;

/// Lazy-loaded message model.
#[derive(Debug, Clone, Eq)]
#[repr(transparent)]
pub struct LazyMessage(Cell);

impl LazyMessage {
    /// Serializes the provided data and returns the typed wrapper around it.
    pub fn new(data: &Message) -> Result<Self, Error> {
        let mut builder = CellBuilder::new();
        let finalizer = &mut Cell::default_finalizer();
        ok!(data.store_into(&mut builder, finalizer));
        Ok(Self::from_raw(ok!(builder.build_ext(finalizer))))
    }

    /// Wraps the cell in a typed wrapper.
    #[inline]
    pub fn from_raw(cell: Cell) -> Self {
        Self(cell)
    }

    /// Converts into the underlying cell.
    #[inline]
    pub fn into_inner(self) -> Cell {
        self.0
    }

    /// Returns the underlying cell.
    #[inline]
    pub fn inner(&self) -> &Cell {
        &self.0
    }

    /// Loads inner data from cell.
    pub fn load(&self) -> Result<Message<'_>, Error> {
        self.0.as_ref().parse::<Message>()
    }
}

impl PartialEq for LazyMessage {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ref() == other.0.as_ref()
    }
}

impl PartialEq<Cell> for LazyMessage {
    #[inline]
    fn eq(&self, other: &Cell) -> bool {
        self.0.as_ref() == other.as_ref()
    }
}

impl Store for LazyMessage {
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn Finalizer) -> Result<(), Error> {
        builder.store_reference(self.0.clone())
    }
}

impl<'a> Load<'a> for LazyMessage {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        slice.load_reference_cloned().map(Self)
    }
}

/// Blockchain message.
#[derive(Debug, Clone)]
pub struct Message<'a> {
    /// Message info.
    pub info: MsgInfo,
    /// Optional state init.
    pub init: Option<StateInit>,
    /// Optional payload.
    pub body: Option<CellSlice<'a>>,
    /// Optional message layout.
    pub layout: Option<MessageLayout>,
}

impl EquivalentRepr<OwnedMessage> for Message<'_> {}

impl<'a> Store for Message<'a> {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        let (layout, bits, refs) = match self.layout {
            Some(layout) => {
                let (bits, refs) =
                    layout.compute_full_len(&self.info, self.init.as_ref(), self.body.as_ref());
                (layout, bits, refs)
            }
            None => MessageLayout::compute(&self.info, self.init.as_ref(), self.body.as_ref()),
        };

        // Check capacity
        if !builder.has_capacity(bits, refs) {
            return Err(Error::CellOverflow);
        }

        // Try to store info
        ok!(self.info.store_into(builder, finalizer));

        // Try to store init
        ok!(match &self.init {
            Some(value) => {
                ok!(builder.store_bit_one()); // just$1
                SliceOrCell {
                    to_cell: layout.init_to_cell,
                    value,
                }
                .store_into(builder, finalizer)
            }
            None => builder.store_bit_zero(), // nothing$0
        });

        // Try to store body
        match &self.body {
            Some(value) => SliceOrCell {
                to_cell: layout.body_to_cell,
                value,
            }
            .store_into(builder, finalizer),
            None => builder.store_bit_zero(),
        }
    }
}

impl<'a> Load<'a> for Message<'a> {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let info = ok!(MsgInfo::load_from(slice));
        let init = ok!(Option::<SliceOrCell<StateInit>>::load_from(slice));
        let body = ok!(SliceOrCell::<CellSlice<'a>>::load_from(slice));

        let (init, init_to_cell) = match init {
            Some(SliceOrCell { to_cell, value }) => (Some(value), to_cell),
            None => (None, false),
        };

        let layout = MessageLayout {
            init_to_cell,
            body_to_cell: body.to_cell,
        };

        let body = if body.value.is_data_empty() && body.value.is_refs_empty() {
            None
        } else {
            Some(body.value)
        };

        Ok(Self {
            info,
            init,
            body,
            layout: Some(layout),
        })
    }
}

/// Blockchain message.
///
/// [`Message`] alternative with a static lifetime.
#[derive(Debug, Clone)]
pub struct OwnedMessage {
    /// Message info.
    pub info: Box<MsgInfo>,
    /// Optional state init.
    pub init: Option<StateInit>,
    /// Optional payload.
    pub body: Option<CellSliceParts>,
    /// Optional message layout.
    pub layout: Option<MessageLayout>,
}

impl EquivalentRepr<Message<'_>> for OwnedMessage {}

impl Store for OwnedMessage {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        let body_slice = ok!(self
            .body
            .as_ref()
            .map(|(cell, range)| range.apply(cell))
            .transpose());

        let (layout, bits, refs) = match self.layout {
            Some(layout) => {
                let (bits, refs) =
                    layout.compute_full_len(&self.info, self.init.as_ref(), body_slice.as_ref());
                (layout, bits, refs)
            }
            None => MessageLayout::compute(&self.info, self.init.as_ref(), body_slice.as_ref()),
        };

        // Check capacity
        if !builder.has_capacity(bits, refs) {
            return Err(Error::CellOverflow);
        }

        // Try to store info
        ok!(self.info.store_into(builder, finalizer));

        // Try to store init
        ok!(match &self.init {
            Some(value) => {
                ok!(builder.store_bit_one()); // just$1
                SliceOrCell {
                    to_cell: layout.init_to_cell,
                    value,
                }
                .store_into(builder, finalizer)
            }
            None => builder.store_bit_zero(), // nothing$0
        });

        // Try to store body
        match &self.body {
            Some((cell, range)) => {
                if layout.body_to_cell && range.is_full(cell.as_ref()) {
                    ok!(builder.store_bit_one());
                    builder.store_reference(cell.clone())
                } else {
                    SliceOrCell {
                        to_cell: layout.body_to_cell,
                        value: ok!(range.apply(cell)),
                    }
                    .store_into(builder, finalizer)
                }
            }
            None => builder.store_bit_zero(),
        }
    }
}

impl<'a> Load<'a> for OwnedMessage {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let info = ok!(Box::<MsgInfo>::load_from(slice));
        let init = ok!(Option::<SliceOrCell<StateInit>>::load_from(slice));

        let body_to_cell = ok!(slice.load_bit());
        let body = if body_to_cell {
            let body = ok!(slice.load_reference_cloned());
            let range = CellSliceRange::full(body.as_ref());
            (!range.is_data_empty() || !range.is_refs_empty()).then_some((body, range))
        } else if !slice.is_data_empty() || !slice.is_refs_empty() {
            let range = slice.range();
            let mut builder = CellBuilder::new();
            ok!(builder.store_slice(slice));
            Some((ok!(builder.build()), range))
        } else {
            None
        };

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

struct SliceOrCell<T> {
    to_cell: bool,
    value: T,
}

impl<T: Store> Store for SliceOrCell<T> {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        if self.to_cell {
            let cell = {
                let mut builder = CellBuilder::new();
                ok!(self.value.store_into(&mut builder, finalizer));
                ok!(builder.build_ext(finalizer))
            };

            // right$1 ^Cell
            ok!(builder.store_bit_one());
            builder.store_reference(cell)
        } else {
            // left$0 X
            ok!(builder.store_bit_zero());
            self.value.store_into(builder, finalizer)
        }
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
    pub const fn compute_full_len(
        &self,
        info: &MsgInfo,
        init: Option<&StateInit>,
        body: Option<&CellSlice<'_>>,
    ) -> (u16, u8) {
        let l = DetailedMessageLayout::compute(info, init, body);

        let mut total_bits = l.info_bits;
        let mut total_refs = l.info_refs;

        // Append init bits and refs
        if self.init_to_cell {
            total_refs += 1;
        } else {
            total_bits += l.init_bits;
            total_refs += l.init_refs;
        }

        // Append body bits and refs
        if self.body_to_cell {
            total_refs += 1;
        } else {
            total_bits += l.body_bits;
            total_refs += l.body_refs;
        }

        (total_bits, total_refs)
    }

    /// Computes the most optimal layout of the message parts.
    /// Also returns the number of bits and refs for the root cell.
    pub const fn compute(
        info: &MsgInfo,
        init: Option<&StateInit>,
        body: Option<&CellSlice<'_>>,
    ) -> (Self, u16, u8) {
        let l = DetailedMessageLayout::compute(info, init, body);

        // Try plain layout
        let total_bits = l.info_bits + l.init_bits + l.body_bits;
        let total_refs = l.info_refs + l.init_refs + l.body_refs;
        if total_bits <= MAX_BIT_LEN && total_refs <= MAX_REF_COUNT as u8 {
            let layout = Self {
                init_to_cell: false,
                body_to_cell: false,
            };
            return (layout, total_bits, total_refs);
        }

        // Try body to ref
        let total_bits = l.info_bits + l.init_bits;
        let total_refs = l.info_refs + l.init_refs;
        if total_bits <= MAX_BIT_LEN && total_refs < MAX_REF_COUNT as u8 {
            let layout = Self {
                init_to_cell: false,
                body_to_cell: true,
            };
            return (layout, total_bits, total_refs);
        }

        // Try init to ref
        let total_bits = l.info_bits + l.body_bits;
        let total_refs = l.info_refs + l.body_refs;
        if total_bits <= MAX_BIT_LEN && total_refs < MAX_REF_COUNT as u8 {
            let layout = Self {
                init_to_cell: true,
                body_to_cell: false,
            };
            return (layout, total_bits, total_refs);
        }

        // Fallback to init and body to ref
        let layout = Self {
            init_to_cell: true,
            body_to_cell: true,
        };
        (layout, l.info_bits, l.info_refs + 2)
    }
}

struct DetailedMessageLayout {
    info_bits: u16,
    info_refs: u8,
    init_bits: u16,
    init_refs: u8,
    body_bits: u16,
    body_refs: u8,
}

impl DetailedMessageLayout {
    const fn compute(
        info: &MsgInfo,
        init: Option<&StateInit>,
        body: Option<&CellSlice<'_>>,
    ) -> Self {
        let mut info_bits = info.bit_len() + 2; // (Maybe X) (1bit) + (Either X) (1bit)
        let info_refs = info.has_references() as u8;

        let (init_bits, init_refs) = match init {
            Some(init) => {
                info_bits += 1; // (Either X) (1bit)
                (init.bit_len(), init.reference_count())
            }
            None => (0, 0),
        };

        let (body_bits, body_refs) = match body {
            Some(body) => (body.remaining_bits(), body.remaining_refs()),
            None => (0, 0),
        };

        Self {
            info_bits,
            info_refs,
            init_bits,
            init_refs,
            body_bits,
            body_refs,
        }
    }
}

/// Message info.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum MsgInfo {
    /// Internal message info,
    Int(IntMsgInfo),
    /// External incoming message info.
    ExtIn(ExtInMsgInfo),
    /// External outgoing message info,
    ExtOut(ExtOutMsgInfo),
}

impl MsgInfo {
    /// Returns the number of data bits that this struct occupies.
    pub const fn bit_len(&self) -> u16 {
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

impl Store for MsgInfo {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        match self {
            Self::Int(info) => {
                ok!(builder.store_bit_zero());
                info.store_into(builder, finalizer)
            }
            Self::ExtIn(info) => {
                ok!(builder.store_small_uint(0b10, 2));
                info.store_into(builder, finalizer)
            }
            Self::ExtOut(info) => {
                ok!(builder.store_small_uint(0b11, 2));
                info.store_into(builder, finalizer)
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

/// Internal message info.
#[derive(Debug, Clone, Eq, PartialEq)]
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
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        let flags =
            ((self.ihr_disabled as u8) << 2) | ((self.bounce as u8) << 1) | self.bounced as u8;
        ok!(builder.store_small_uint(flags, 3));
        ok!(self.src.store_into(builder, finalizer));
        ok!(self.dst.store_into(builder, finalizer));
        ok!(self.value.store_into(builder, finalizer));
        ok!(self.ihr_fee.store_into(builder, finalizer));
        ok!(self.fwd_fee.store_into(builder, finalizer));
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

/// External incoming message info.
#[derive(Debug, Default, Clone, Eq, PartialEq)]
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
        2 + compute_ext_addr_bit_len(&self.src)
            + self.dst.bit_len()
            + self.import_fee.unwrap_bit_len()
    }
}

impl Store for ExtInMsgInfo {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        if !self.import_fee.is_valid() {
            return Err(Error::InvalidData);
        }
        if !builder.has_capacity(self.bit_len(), 0) {
            return Err(Error::CellOverflow);
        }
        ok!(store_ext_addr(builder, finalizer, &self.src));
        ok!(self.dst.store_into(builder, finalizer));
        self.import_fee.store_into(builder, finalizer)
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

impl Store for ExtOutMsgInfo {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        if !builder.has_capacity(self.bit_len(), 0) {
            return Err(Error::CellOverflow);
        }
        ok!(builder.store_small_uint(0b11, 2));
        ok!(self.src.store_into(builder, finalizer));
        ok!(store_ext_addr(builder, finalizer, &self.dst));
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

const fn compute_ext_addr_bit_len(addr: &Option<ExtAddr>) -> u16 {
    match addr {
        Some(addr) => 2 + addr.bit_len(),
        None => 2,
    }
}

#[inline]
fn store_ext_addr(
    builder: &mut CellBuilder,
    finalizer: &mut dyn Finalizer,
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
            ok!(data_bit_len.store_into(builder, finalizer));
            builder.store_raw(data, data_bit_len.into_inner())
        }
    }
}

#[inline]
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
