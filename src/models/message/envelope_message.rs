use std::cmp::Ordering;

use crate::cell::*;
use crate::error::Error;
use crate::models::{Lazy, Message, MsgInfo, OwnedMessage};

/// Intermediate address
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum IntermediateAddress {
    /// Regular address
    Regular(IntermediateAddressRegular),
    /// Simple address
    Simple(IntermediateAddressSimple),
    /// Extended address
    Ext(IntermediateAddressExt),
}

impl IntermediateAddress {
    pub fn use_src_bits(use_src_bits: u8) -> Result<Self, Error> {
        let ia = IntermediateAddressRegular::with_use_src_bits(use_src_bits)?;
        Ok(IntermediateAddress::Regular(ia))
    }

    pub fn use_dest_bits(use_dest_bits: u8) -> Result<Self, Error> {
        let ia = IntermediateAddressRegular::with_use_dest_bits(use_dest_bits)?;
        Ok(IntermediateAddress::Regular(ia))
    }

    pub fn full_src() -> Self {
        let src = IntermediateAddressRegular::with_use_dest_bits(0).unwrap();
        IntermediateAddress::Regular(src)
    }

    pub fn full_dest() -> Self {
        let dest = IntermediateAddressRegular::with_use_src_bits(0).unwrap();
        IntermediateAddress::Regular(dest)
    }
    pub fn any_masterchain() -> Self {
        let master = IntermediateAddressSimple::with_addr(-1, 0x8000000000000000);
        IntermediateAddress::Simple(master)
    }

    /// Get workchain
    pub fn workchain(&self) -> Result<i8, Error> {
        match self {
            IntermediateAddress::Simple(simple) => Ok(simple.workchain()),
            IntermediateAddress::Ext(ext) => Ok(ext.workchain()),
            _ => Err(Error::UnsupportedAddressType),
        }
    }

    /// Get prefix
    pub fn prefix(&self) -> Result<u64, Error> {
        match self {
            IntermediateAddress::Simple(simple) => Ok(simple.address_prefix()),
            IntermediateAddress::Ext(ext) => Ok(ext.address_prefix()),
            _ => Err(Error::UnsupportedAddressType),
        }
    }
}

impl Default for IntermediateAddress {
    fn default() -> Self {
        IntermediateAddress::full_src()
    }
}

impl PartialOrd<u8> for IntermediateAddress {
    fn partial_cmp(&self, other: &u8) -> Option<Ordering> {
        match self {
            IntermediateAddress::Regular(ia) => Some(ia.use_dest_bits.cmp(other)),
            _ => None,
        }
    }
}

impl PartialEq<u8> for IntermediateAddress {
    fn eq(&self, other: &u8) -> bool {
        match self {
            IntermediateAddress::Regular(ia) => &ia.use_dest_bits == other,
            _ => false,
        }
    }
}

impl Store for IntermediateAddress {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        match self {
            IntermediateAddress::Regular(addr) => {
                builder.store_raw(&[0b00000000], 1)?; // tag = $0
                addr.store_into(builder, context)?;
            }
            IntermediateAddress::Simple(addr) => {
                builder.store_raw(&[0b10000000], 2)?; // tag = $10
                addr.store_into(builder, context)?;
            }
            IntermediateAddress::Ext(addr) => {
                builder.store_raw(&[0b11000000], 2)?; // tag = $11
                addr.store_into(builder, context)?;
            }
        };
        Ok(())
    }
}

impl<'a> Load<'a> for IntermediateAddress {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        if slice.load_bit()? {
            if slice.load_bit()? {
                // tag = 11
                let addr = IntermediateAddressExt::load_from(slice)?;
                Ok(IntermediateAddress::Ext(addr))
            } else {
                // tag = $10
                let addr = IntermediateAddressSimple::load_from(slice)?;
                Ok(IntermediateAddress::Simple(addr))
            }
        } else {
            // tag = $0
            let addr = IntermediateAddressRegular::load_from(slice)?;
            Ok(IntermediateAddress::Regular(addr))
        }
    }
}

/// Intermediate Regular address
#[derive(Clone, Default, Debug, PartialEq, Eq, Hash, Store, Load)]
pub struct IntermediateAddressRegular {
    /// Use dest bits
    use_dest_bits: u8,
}

pub static FULL_BITS: u8 = 96;

impl IntermediateAddressRegular {
    /// Create with use src bits
    pub fn with_use_src_bits(use_src_bits: u8) -> Result<Self, Error> {
        if use_src_bits > FULL_BITS {
            return Err(Error::InvalidArg(format!(
                "use_src_bits must be <= {}",
                FULL_BITS
            )));
        }
        Ok(IntermediateAddressRegular {
            use_dest_bits: FULL_BITS - use_src_bits,
        })
    }

    /// Create with use dest bits
    pub fn with_use_dest_bits(use_dest_bits: u8) -> Result<Self, Error> {
        if use_dest_bits > FULL_BITS {
            return Err(Error::InvalidArg(format!(
                "use_dest_bits must be <= {}",
                FULL_BITS
            )));
        }
        Ok(IntermediateAddressRegular { use_dest_bits })
    }

    /// Get use src bits
    pub fn use_src_bits(&self) -> u8 {
        FULL_BITS - self.use_dest_bits
    }

    /// Get use dest bits
    pub fn use_dest_bits(&self) -> u8 {
        self.use_dest_bits
    }

    /// Set use src bits
    pub fn set_use_src_bits(&mut self, use_src_bits: u8) -> Result<(), Error> {
        if use_src_bits > FULL_BITS {
            return Err(Error::InvalidArg(format!(
                "use_src_bits must be <= {}",
                FULL_BITS
            )));
        }
        self.use_dest_bits = FULL_BITS - use_src_bits;
        Ok(())
    }
}

/// Intermediate Simple address
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, Load, Store)]
pub struct IntermediateAddressSimple {
    /// Workchain ID
    pub workchain: i8,
    /// Address prefix
    pub address_prefix: u64,
}

impl IntermediateAddressSimple {
    /// Create with workchain and address prefix
    pub const fn with_addr(workchain: i8, address_prefix: u64) -> Self {
        Self {
            workchain,
            address_prefix,
        }
    }

    /// Get workchain
    pub const fn workchain(&self) -> i8 {
        self.workchain
    }

    /// Get address prefix
    pub const fn address_prefix(&self) -> u64 {
        self.address_prefix
    }

    /// Set workchain
    pub fn set_workchain(&mut self, workchain: i8) {
        self.workchain = workchain;
    }

    /// Set address prefix
    pub fn set_address_prefix(&mut self, address_prefix: u64) {
        self.address_prefix = address_prefix;
    }
}

/// Intermediate Extended address
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, Store, Load)]
pub struct IntermediateAddressExt {
    pub workchain: i8,
    pub address_prefix: u64,
}

impl IntermediateAddressExt {
    /// Create with workchain and address prefix
    pub const fn with_addr(workchain: i8, address_prefix: u64) -> Self {
        Self {
            workchain,
            address_prefix,
        }
    }

    /// Get workchain
    pub const fn workchain(&self) -> i8 {
        self.workchain
    }

    /// Get address prefix
    pub const fn address_prefix(&self) -> u64 {
        self.address_prefix
    }

    /// Set workchain
    pub fn set_workchain_id(&mut self, workchain: i8) {
        self.workchain = workchain;
    }

    /// Set address prefix
    pub fn set_address_prefix(&mut self, address_prefix: u64) {
        self.address_prefix = address_prefix;
    }
}

/// Message envelope
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MsgEnvelope<'a> {
    /// current address
    cur_addr: IntermediateAddress,
    /// next address
    next_addr: IntermediateAddress,
    /// forward fee remaining
    fwd_fee_remaining: u128,
    /// message
    message: Lazy<Message<'a>>,
}

impl<'a> MsgEnvelope<'a> {
    /// Create Envelope with message and remaining forward fee
    pub fn with_message_and_fee(
        message: &'a Message,
        fwd_fee_remaining: u128,
    ) -> Result<Self, Error> {
        if let MsgInfo::Int(_) = message.info {
            Ok(Self::with_routing(
                Lazy::new(message).unwrap(),
                fwd_fee_remaining,
                IntermediateAddress::full_dest(),
                IntermediateAddress::full_dest(),
            ))
        } else {
            Err(Error::InvalidArg(
                "MsgEnvelope can be made only for internal messages".to_string(),
            ))
        }
    }

    /// Create Envelope with message cell and remaining forward fee
    pub fn with_message_cell_and_fee(cell: Cell, fwd_fee_remaining: u128) -> Self {
        Self::with_routing(
            Lazy::load_from(&mut cell.as_slice().unwrap()).unwrap(),
            fwd_fee_remaining,
            IntermediateAddress::full_dest(),
            IntermediateAddress::full_dest(),
        )
    }

    /// Create Envelope with message and remaining forward fee and routing settings
    pub fn with_routing(
        message: Lazy<Message<'a>>,
        fwd_fee_remaining: u128,
        cur_addr: IntermediateAddress,
        next_addr: IntermediateAddress,
    ) -> Self {
        MsgEnvelope {
            cur_addr,
            next_addr,
            fwd_fee_remaining,
            message,
        }
    }

    /// Read message struct from envelope
    pub fn read_message(&'a self) -> Result<Message<'a>, Error> {
        self.message.load()
    }

    /// Read owned message struct from envelope
    pub fn read_owned_message(&'a self) -> Result<OwnedMessage, Error> {
        self.message.clone().cast_into::<OwnedMessage>().load()
    }

    /// Write message struct to envelope
    pub fn write_message(&mut self, value: &'a Message) -> Result<(), Error> {
        self.message = Lazy::new(value).unwrap();
        Ok(())
    }

    /// Return message cell from envelope
    pub fn message_cell(&self) -> Cell {
        self.message.cell.clone()
    }

    /// Return message hash from envelope
    pub fn message_hash(&self) -> HashBytes {
        *self.message.cell.repr_hash()
    }

    /// Get remaining fee of envelope
    pub fn fwd_fee_remaining(&self) -> u128 {
        self.fwd_fee_remaining
    }

    /// Collect transfer fee from envelope
    pub fn collect_fee(&mut self, fee: u128) -> bool {
        self.fwd_fee_remaining.checked_sub(fee).is_some()
    }

    /// Set current address of envelope
    pub fn set_cur_addr(&mut self, addr: IntermediateAddress) -> &mut Self {
        self.cur_addr = addr;
        self
    }

    /// Set next address of envelope
    pub fn set_next_addr(&mut self, addr: IntermediateAddress) -> &mut Self {
        self.next_addr = addr;
        self
    }

    /// Get current address
    pub fn cur_addr(&self) -> &IntermediateAddress {
        &self.cur_addr
    }

    /// Get next address
    pub fn next_addr(&self) -> &IntermediateAddress {
        &self.next_addr
    }

    /// is message route in one workchain
    pub fn same_workchain(&self) -> Result<bool, Error> {
        let message = self.read_message()?;
        if let MsgInfo::Int(int_msg_info) = message.info {
            let src = int_msg_info.src;
            let dst = int_msg_info.dst;
            Ok(src.workchain() == dst.workchain())
        } else {
            Err(Error::InvalidArg(format!(
                "Message with hash {:x?} is not internal",
                self.message_cell().repr_hash().0
            )))
        }
    }
}

const MSG_ENVELOPE_TAG: u32 = 0x4;

impl<'a> Store for MsgEnvelope<'a> {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_u32(MSG_ENVELOPE_TAG));

        self.cur_addr.store_into(builder, context)?;
        self.next_addr.store_into(builder, context)?;
        ok!(builder.store_u128(self.fwd_fee_remaining));
        ok!(builder.store_reference(self.message.cell.clone()));
        Ok(())
    }
}

impl<'a> Load<'a> for MsgEnvelope<'a> {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let tag = ok!(slice.load_u32());
        if tag != MSG_ENVELOPE_TAG {
            return Err(Error::InvalidCell);
        }

        Ok(Self {
            cur_addr: IntermediateAddress::load_from(slice)?,
            next_addr: IntermediateAddress::load_from(slice)?,
            fwd_fee_remaining: ok!(slice.load_u128()),
            message: Lazy::load_from(slice)?,
        })
    }
}
