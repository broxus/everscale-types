//! Message models.

use crate::cell::*;
use crate::error::Error;
use crate::num::*;

use crate::models::account::StateInit;
use crate::models::currency::CurrencyCollection;

pub use self::address::*;

mod address;

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

impl<'a> Store for Message<'a> {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        let (layout, bits, refs) = match self.layout {
            Some(layout) => {
                let (bits, refs) = layout.compute_full_len(&self.info, &self.init, &self.body);
                (layout, bits, refs)
            }
            None => MessageLayout::compute(&self.info, &self.init, &self.body),
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
            Some(ok!(slice.load_reference()).as_slice())
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
        init: &Option<StateInit>,
        body: &Option<CellSlice<'_>>,
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
        init: &Option<StateInit>,
        body: &Option<CellSlice<'_>>,
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
        init: &Option<StateInit>,
        body: &Option<CellSlice<'_>>,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prelude::*;

    fn serialize_message(message: Message) -> Cell {
        CellBuilder::build_from(message).unwrap()
    }

    fn check_message(boc: &str) -> Cell {
        let boc = Boc::decode_base64(boc).unwrap();
        let message = boc.parse::<Message>().unwrap();
        println!("message: {message:#?}");

        if let Some(init) = &message.init {
            let init = CellBuilder::build_from(init).unwrap();
            println!("{}", Boc::encode_base64(init));
        }

        let serialized = serialize_message(message);
        assert_eq!(serialized.as_ref(), boc.as_ref());

        boc
    }

    #[test]
    fn external_message() {
        let boc = check_message("te6ccgEBAwEA7gABRYgBGRoZkBXGlyf8MT+9+Aps6LyB9WVSLzZvhJSDPgmbHEIMAQHh8Nu9eCxecUj/vM96Y20RjiKgx6WoTw2DovvS/s9dA8fluaPCOfF9jDxVICPgt0F7bK5DLXQwAabrqb7Wnd+hgnWJpZrz4u8JX/jyyB6RENwoAPPEnVzvkFpHxK5gcHDrgAAAYW7VQB2Y8V2LAAAABGACAKMAAAAAAAAAAAAAAACy0F4AgBBMK6mc15szE1BZJlPsqtMkXmhvBh1UIAaIln9JSMkh+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAARnFb2fy+DAM");

        let body = Boc::decode_base64("te6ccgEBAgEAyAAB4fDbvXgsXnFI/7zPemNtEY4ioMelqE8Ng6L70v7PXQPH5bmjwjnxfYw8VSAj4LdBe2yuQy10MAGm66m+1p3foYJ1iaWa8+LvCV/48sgekRDcKADzxJ1c75BaR8SuYHBw64AAAGFu1UAdmPFdiwAAAARgAQCjAAAAAAAAAAAAAAAAstBeAIAQTCupnNebMxNQWSZT7KrTJF5obwYdVCAGiJZ/SUjJIfgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEZxW9n8vgwDA==").unwrap();
        let serialized = serialize_message(Message {
            info: MsgInfo::ExtIn(ExtInMsgInfo {
                dst: "0:8c8d0cc80ae34b93fe189fdefc0536745e40fab2a9179b37c24a419f04cd8e21"
                    .parse()
                    .unwrap(),
                ..Default::default()
            }),
            init: None,
            body: Some(body.as_slice()),
            layout: None,
        });
        assert_eq!(boc.as_ref(), serialized.as_ref());
    }

    #[test]
    fn internal_message_empty() {
        let boc = check_message("te6ccgEBAQEAWwAAsUgBUkKKaORs1v/d2CpkdS1rueLjL5EbgaivG/SlIBcUZ5cAKkhRTRyNmt/7uwVMjqWtdzxcZfIjcDUV436UpALijPLQ7msoAAYUWGAAAD6o4PtmhMeK8nJA");

        let serialized = serialize_message(Message {
            info: MsgInfo::Int(IntMsgInfo {
                ihr_disabled: true,
                src: "0:a921453472366b7feeec15323a96b5dcf17197c88dc0d4578dfa52900b8a33cb"
                    .parse()
                    .unwrap(),
                dst: "0:a921453472366b7feeec15323a96b5dcf17197c88dc0d4578dfa52900b8a33cb"
                    .parse()
                    .unwrap(),
                value: CurrencyCollection::new(1000000000),
                fwd_fee: Tokens::new(666672),
                created_lt: 34447525000002,
                created_at: 1673886009,
                ..Default::default()
            }),
            init: None,
            body: None,
            layout: None,
        });
        assert_eq!(boc.as_ref(), serialized.as_ref());
    }

    #[test]
    fn internal_message_with_body() {
        let boc = check_message("te6ccgEBBAEA7AABsWgBBMK6mc15szE1BZJlPsqtMkXmhvBh1UIAaIln9JSMkh8AKcyu6HDSN2uCXClQSdunN5ORKwsVegHnQNPiLAwT3wIQF0ZQIAYwZroAAD6ov3v2DMeK7AjAAQFLAAAADMAF47ShSRBdLiDscbrZ36xyWwI6GHiM/l4Mroth4ygz7HgCAaOABHg99SYML+GkoEJQXFyIG56xbLXbw9MCLDl9Vfnxmy7AAAAAAAAAAAAAAAAAAABD4AAAAAAAAAAAAAAAABMS0AAAAAAAAAAAAAACxOw48AAQAwAgAAAAAAAAAAAAAAAAAAAAAA==");

        let body = Boc::decode_base64("te6ccgEBAwEAkAABSwAAAAzABeO0oUkQXS4g7HG62d+sclsCOhh4jP5eDK6LYeMoM+x4AQGjgAR4PfUmDC/hpKBCUFxciBuesWy128PTAiw5fVX58ZsuwAAAAAAAAAAAAAAAAAAAQ+AAAAAAAAAAAAAAAAATEtAAAAAAAAAAAAAAAsTsOPAAEAIAIAAAAAAAAAAAAAAAAAAAAAA=").unwrap();
        let serialized = serialize_message(Message {
            info: MsgInfo::Int(IntMsgInfo {
                ihr_disabled: true,
                bounce: true,
                src: "0:82615d4ce6bcd9989a82c9329f65569922f3437830eaa1003444b3fa4a46490f"
                    .parse()
                    .unwrap(),
                dst: "0:a732bba1c348ddae0970a541276e9cde4e44ac2c55e8079d034f88b0304f7c08"
                    .parse()
                    .unwrap(),
                value: CurrencyCollection::new(97621000),
                fwd_fee: Tokens::new(1586013),
                created_lt: 34447244000006,
                created_at: 1673885188,
                ..Default::default()
            }),
            init: None,
            body: Some(body.as_slice()),
            layout: Some(MessageLayout {
                init_to_cell: false,
                body_to_cell: true,
            }),
        });
        assert_eq!(boc.as_ref(), serialized.as_ref());
    }

    #[test]
    fn internal_message_with_deploy() {
        let boc = check_message("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");

        let init = Boc::decode_base64("te6ccgECHwEAAusAAgE0BwEBAcACAgPPoAQDAENIAUpnBMEzNuMM19fqFpbnKo8XDAuxxPo5wy4djuha3dClAgEgBgUAQyAFJOanCsVNCqqvMSOs8XJzs2kTAFvABsSPI3yUj4IlSewAQQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIAIGits1HggEJIrtUyDjAyDA/+MCIMD+4wLyCxoLCgkAAAOK7UTQ10nDAfhmifhpIds80wABn4ECANcYIPkBWPhC+RDyqN7TPwH4QyG58rQg+COBA+iogggbd0CgufK0+GPTHwHbPPI8GBQMA1LtRNDXScMB+GYi0NMD+kAw+GmpOADcIccA4wIh1w0f8rwh4wMB2zzyPBkZDAEUIIIQFaA4+7rjAg0EkDD4Qm7jAPhG8nMhltTTH9TR0JPU0x/i+kDU0dD6QNH4SfhKxwUgjoDfjoCOFCDIz4UIzoBvz0DJgQCApiC1B/sA4l8E2zzyABQRDh0BCF0i2zwPAnz4SsjO+EsBznABy39wAcsfEssfzvhBiMjPjits1szOyQHMIfsEAdAgizits1jHBZPXTdDe10zQ7R7tU8nbPB4QAATwAgEeMCH6Qm8T1wv/wwAgjoDeEgEQMCHbPPhJxwUTAX5wyMv/cG2AQPRD+EpxWIBA9BYBcliAQPQWyPQAyfhBiMjPjits1szOycjPhID0APQAz4HJ+QDIz4oAQMv/ydAeAhbtRNDXScIBjoDjDRYVADTtRNDT/9M/0wAx+kDU0dD6QNH4a/hq+GP4YgJUcO1E0PQFcSGAQPQOjoDfciKAQPQOjoDf+Gv4aoBA9A7yvdcL//hicPhjFxcBAokYAEOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAAr4RvLgTAIK9KQg9KEcGwAUc29sIDAuNTcuMQEYoAAAAAIw2zz4D/IAHQAs+Er4Q/hCyMv/yz/Pg874S8jOzcntVAAMIPhh7R7Z").unwrap();
        let init = init.parse::<StateInit>().unwrap();

        let body = Boc::decode_base64("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").unwrap();

        let serialized = serialize_message(Message {
            info: MsgInfo::Int(IntMsgInfo {
                ihr_disabled: true,
                bounce: true,
                src: "0:098c37c0d8a78b32826de1d956242ee7830f83016eaa930e8c535295aea3ff1b"
                    .parse()
                    .unwrap(),
                dst: "0:a4232bb25ca73b09e1bb5200f87548f5a51a2d143d296a5a86b4bf74ec83e662"
                    .parse()
                    .unwrap(),
                value: CurrencyCollection::new(100000000),
                fwd_fee: Tokens::new(28859554),
                created_lt: 34447559000008,
                created_at: 1673886111,
                ..Default::default()
            }),
            init: Some(init),
            body: Some(body.as_slice()),
            layout: Some(MessageLayout {
                init_to_cell: true,
                body_to_cell: true,
            }),
        });
        assert_eq!(boc.as_ref(), serialized.as_ref());
    }

    #[test]
    fn internal_message_with_deploy_special() {
        use crate::models::account::*;

        let boc = check_message("te6ccgEBAwEAZgABsUgBbEihcGq1yvqcKmG7SIXC+7TB5znc+YFGjyqs3GDGG38/6C2Xq2vdBoTJGfwJ+7clxo9Tw1600zBjtr6ydPBmP2bQ5xx9YAb6cxQAABQ+Ztidisbf8S+gAQIBfQICAAb/AAA=");

        let init = StateInit {
            split_depth: None,
            special: Some(SpecialFlags {
                tick: true,
                tock: true,
            }),
            code: Some(Boc::decode_base64("te6ccgEBAQEABQAABv8AAA==").unwrap()),
            data: Some(Boc::decode_base64("te6ccgEBAQEABQAABv8AAA==").unwrap()),
            libraries: Default::default(),
        };

        let serialized = serialize_message(Message {
            info: MsgInfo::Int(IntMsgInfo {
                ihr_disabled: true,
                src: "0:b62450b8355ae57d4e1530dda442e17dda60f39cee7cc0a34795566e30630dbf"
                    .parse()
                    .unwrap(),
                dst: "-1:a0b65eadaf741a132467f027eedc971a3d4f0d7ad34cc18edafac9d3c198fd9b"
                    .parse()
                    .unwrap(),
                value: CurrencyCollection::new(969351000),
                fwd_fee: Tokens::new(8206730),
                created_lt: 11129123000005,
                created_at: 1668282519,
                ..Default::default()
            }),
            init: Some(init),
            body: None,
            layout: Some(MessageLayout {
                init_to_cell: true,
                body_to_cell: false,
            }),
        });
        assert_eq!(boc.as_ref(), serialized.as_ref());
    }
}
