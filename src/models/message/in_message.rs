use std::fmt;

use crate::cell::*;
use crate::error::Error;
use crate::models::message::envelope_message::MsgEnvelope;
use crate::models::{CurrencyCollection, Lazy, Message, MsgInfo, OwnedMessage, Transaction};

/// Import fees
#[derive(Default, PartialEq, Eq, Clone, Debug, Store, Load)]
pub struct ImportFees {
    /// Collected fees
    pub fees_collected: u128,
    /// Value imported
    pub value_imported: CurrencyCollection,
}

impl ImportFees {
    /// Create new ImportFees with given u128
    pub fn with_u128(u128: u64) -> Self {
        Self {
            fees_collected: u128.into(),
            value_imported: CurrencyCollection::default(),
        }
    }
}

/// Constructor tag of InMsg variant IMPORT_EXT (only 3 bits are used)
const MSG_IMPORT_EXT: u8 = 0b00000000;
/// Constructor tag of InMsg variant IMPORT_IMM (only 3 bits are used)
const MSG_IMPORT_IMM: u8 = 0b00000011;
/// Constructor tag of InMsg variant IMPORT_FIN (only 3 bits are used)
const MSG_IMPORT_FIN: u8 = 0b00000100;
/// Constructor tag of InMsg variant IMPORT_TR (only 3 bits are used)
const MSG_IMPORT_TR: u8 = 0b00000101;
/// Constructor tag of InMsg variant DISCARD_FIN (only 3 bits are used)
const MSG_DISCARD_FIN: u8 = 0b00000110;
/// Constructor tag of InMsg variant DISCARD_TR (only 3 bits are used)
const MSG_DISCARD_TR: u8 = 0b00000111;

/// Inbound message
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub enum InMsg<'a> {
    /// None
    #[default]
    None,
    /// Inbound external messages
    External(InMsgExternal<'a>),
    /// Internal messages with destinations in this block
    Immediate(InMsgFinal<'a>),
    /// Immediately routed internal messages
    Final(InMsgFinal<'a>),
    /// Transit internal messages
    Transit(InMsgTransit<'a>),
    /// Discarded internal messages with destinations in this block
    DiscardedFinal(InMsgDiscardedFinal<'a>),
    /// Discarded transit internal messages
    DiscardedTransit(InMsgDiscardedTransit<'a>),
}

impl<'a> fmt::Display for InMsg<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let msg_hash = *self.message_cell().unwrap_or_default().repr_hash();
        let tr_hash = *self.transaction_cell().unwrap_or_default().repr_hash();
        match self {
            InMsg::External(_x) => write!(f, "InMsgExternal message hash: {:x?} transaction hash: {:x?}", msg_hash, tr_hash),
            InMsg::Immediate(x) => write!(f, "InMsgImmediate message hash: {:x?} transaction hash: {:x?} fee: {}", msg_hash, tr_hash, x.fwd_fee),
            InMsg::Transit(x) => write!(f, "InMsgTransit in_message hash: {:x?} out_message hash: {:x?} fee: {}", msg_hash, x.out_envelope_message_hash(), x.transit_fee),
            InMsg::Final(x) => write!(f, "InMsgFinal  message hash: {:x?} transaction hash: {:x?} fee: {}", msg_hash, tr_hash, x.fwd_fee),
            InMsg::DiscardedFinal(x) => write!(f, "InMsgDiscardedFinal message hash: {:x?} transaction hash: {} fee: {}", msg_hash, x.transaction_id, x.fwd_fee),
            InMsg::DiscardedTransit(x) => write!(f, "InMsgDiscardedTransit message hash: {:x?} transaction hash: {:x?} fee: {} proof: {:x?}", msg_hash, x.transaction_id, x.fwd_fee, x.proof_delivered.repr_hash()),
            InMsg::None => write!(f, "InMsgNone")
        }
    }
}

impl<'a> InMsg<'a> {
    /// Create external
    pub fn external(msg_cell: Cell, tr_cell: Cell) -> InMsg<'a> {
        InMsg::External(InMsgExternal::with_cells(msg_cell, tr_cell))
    }
    /// Create Immediate
    pub fn immediate(msg_cell: Cell, tr_cell: Cell, fwd_fee: u128) -> InMsg<'a> {
        InMsg::Immediate(InMsgFinal::with_cells(msg_cell, tr_cell, fwd_fee))
    }
    /// Create Final
    pub fn final_msg(msg_cell: Cell, tr_cell: Cell, fwd_fee: u128) -> InMsg<'a> {
        InMsg::Final(InMsgFinal::with_cells(msg_cell, tr_cell, fwd_fee))
    }
    /// Create Transit
    pub fn transit(in_msg_cell: Cell, out_msg_cell: Cell, fwd_fee: u128) -> InMsg<'a> {
        InMsg::Transit(InMsgTransit::with_cells(in_msg_cell, out_msg_cell, fwd_fee))
    }
    /// Create DiscardedFinal
    pub fn discarded_final(env_cell: Cell, tr_id: u64, fwd_fee: u128) -> InMsg<'a> {
        InMsg::DiscardedFinal(InMsgDiscardedFinal::with_cells(env_cell, tr_id, fwd_fee))
    }
    /// Create DiscardedTransit
    pub fn discarded_transit(env_cell: Cell, tr_id: u64, fwd_fee: u128, proof: Cell) -> InMsg<'a> {
        InMsg::DiscardedTransit(InMsgDiscardedTransit::with_cells(
            env_cell, tr_id, fwd_fee, proof,
        ))
    }

    /// Check if is valid message
    pub fn is_valid(&self) -> bool {
        self != &InMsg::None
    }

    /// Get tag
    pub fn tag(&self) -> u8 {
        match self {
            InMsg::External(_) => MSG_IMPORT_EXT,
            InMsg::Immediate(_) => MSG_IMPORT_IMM,
            InMsg::Final(_) => MSG_IMPORT_FIN,
            InMsg::Transit(_) => MSG_IMPORT_TR,
            InMsg::DiscardedFinal(_) => MSG_DISCARD_FIN,
            InMsg::DiscardedTransit(_) => MSG_DISCARD_TR,
            InMsg::None => 8,
        }
    }

    /// Get transaction from inbound message
    /// Transaction exist only in External, IHR, Immediate and Final inbound messages.
    /// For other messages function returned None
    pub fn read_transaction(&self) -> Result<Option<Transaction>, Error> {
        Ok(match self {
            InMsg::External(ref x) => Some(x.read_transaction()?),
            InMsg::Immediate(ref x) => Some(x.read_transaction()?),
            InMsg::Final(ref x) => Some(x.read_transaction()?),
            InMsg::Transit(ref _x) => None,
            InMsg::DiscardedFinal(ref _x) => None,
            InMsg::DiscardedTransit(ref _x) => None,
            InMsg::None => return Err(Error::InvalidArg("Wrong message type".to_string())),
        })
    }

    /// Get transaction cell from inbound message
    /// Transaction exist only in External, IHR, Immediate and Final inbound messages.
    /// For other messages function returned None
    pub fn transaction_cell(&self) -> Option<Cell> {
        match self {
            InMsg::External(ref x) => Some(x.transaction_cell()),
            InMsg::Immediate(ref x) => Some(x.transaction_cell()),
            InMsg::Final(ref x) => Some(x.transaction_cell()),
            InMsg::Transit(ref _x) => None,
            InMsg::DiscardedFinal(ref _x) => None,
            InMsg::DiscardedTransit(ref _x) => None,
            InMsg::None => None,
        }
    }

    /// Get message
    pub fn read_message(&'a self) -> Result<OwnedMessage, Error> {
        match self {
            InMsg::External(x) => x.read_owned_message(),
            InMsg::Immediate(x) => x.read_envelope_in_message(),
            InMsg::Final(x) => x.read_envelope_in_message(),
            InMsg::Transit(x) => x.read_envelope_in_message(),
            InMsg::DiscardedFinal(x) => x.read_envelope_in_message(),
            InMsg::DiscardedTransit(x) => x.read_envelope_in_message(),
            InMsg::None => Err(Error::InvalidArg("Wrong message type".to_string())),
        }
    }

    /// Get message cell
    pub fn message_cell(&self) -> Result<Cell, Error> {
        Ok(match self {
            InMsg::External(ref x) => x.message_cell(),
            InMsg::Immediate(ref x) => x.read_envelope_message()?.message_cell(),
            InMsg::Final(ref x) => x.read_envelope_message()?.message_cell(),
            InMsg::Transit(ref x) => x.read_in_message()?.message_cell(),
            InMsg::DiscardedFinal(ref x) => x.read_envelope_message()?.message_cell(),
            InMsg::DiscardedTransit(ref x) => x.read_envelope_message()?.message_cell(),
            InMsg::None => return Err(Error::InvalidArg("Wrong message type".to_string())),
        })
    }

    /// Get in envelope message cell
    pub fn in_msg_envelope_cell(&self) -> Option<Cell> {
        match self {
            InMsg::External(_) => None,
            InMsg::Immediate(ref x) => Some(x.envelope_message_cell()),
            InMsg::Final(ref x) => Some(x.envelope_message_cell()),
            InMsg::Transit(ref x) => Some(x.in_envelope_message_cell()),
            InMsg::DiscardedFinal(ref x) => Some(x.envelope_message_cell()),
            InMsg::DiscardedTransit(ref x) => Some(x.envelope_message_cell()),
            InMsg::None => None,
        }
    }

    /// Get in envelope message
    pub fn read_in_msg_envelope(&self) -> Result<Option<MsgEnvelope>, Error> {
        Ok(match self {
            InMsg::External(_) => None,
            InMsg::Immediate(ref x) => Some(x.read_envelope_message()?),
            InMsg::Final(ref x) => Some(x.read_envelope_message()?),
            InMsg::Transit(ref x) => Some(x.read_in_message()?),
            InMsg::DiscardedFinal(ref x) => Some(x.read_envelope_message()?),
            InMsg::DiscardedTransit(ref x) => Some(x.read_envelope_message()?),
            InMsg::None => return Err(Error::InvalidArg("Wrong message type".to_string())),
        })
    }

    /// Get out envelope message cell
    pub fn out_msg_envelope_cell(&self) -> Option<Cell> {
        match self {
            InMsg::External(_) => None,
            InMsg::Immediate(_) => None,
            InMsg::Final(_) => None,
            InMsg::Transit(ref x) => Some(x.out_envelope_message_cell()),
            InMsg::DiscardedFinal(_) => None,
            InMsg::DiscardedTransit(_) => None,
            InMsg::None => None,
        }
    }

    /// Get out envelope message
    pub fn read_out_msg_envelope(&self) -> Result<Option<MsgEnvelope>, Error> {
        match self {
            InMsg::External(_) => Ok(None),
            InMsg::Immediate(_) => Ok(None),
            InMsg::Final(_) => Ok(None),
            InMsg::Transit(ref x) => Some(x.read_out_message()).transpose(),
            InMsg::DiscardedFinal(_) => Ok(None),
            InMsg::DiscardedTransit(_) => Ok(None),
            InMsg::None => Err(Error::InvalidArg("Wrong message type".to_string())),
        }
    }

    /// Get fee
    pub fn get_fee(&self) -> Result<ImportFees, Error> {
        let msg = self.read_message()?;
        let info = match msg.info {
            MsgInfo::Int(info) => info,
            _ => return Ok(ImportFees::default()),
        };
        let mut fees = ImportFees::default();
        match self {
            InMsg::External(_) => {}
            InMsg::Immediate(_) => {
                fees.fees_collected = info.fwd_fee.into_inner();
            }
            InMsg::Final(ref x) => {
                let env = x.read_envelope_message()?;
                if env.fwd_fee_remaining() != *x.fwd_fee() {
                    return Err(Error::InvalidArg(
                        "fwd_fee_remaining not equal to fwd_fee".to_string(),
                    ));
                }
                fees.fees_collected = env.fwd_fee_remaining();
                //
                // fees.value_imported = info.value.clone();
                // fees.value_imported.grams.add(env.fwd_fee_remaining())?;
                // fees.value_imported.grams.add(&header.ihr_fee)?;
            }
            InMsg::Transit(ref x) => {
                let env = x.read_in_message()?;
                if env.fwd_fee_remaining() < *x.transit_fee() {
                    return Err(Error::InvalidArg(
                        "fwd_fee_remaining less than transit_fee".to_string(),
                    ));
                }

                fees.fees_collected = *x.transit_fee();

                // fees.value_imported = info.value.clone();
                // fees.value_imported.grams.add(&header.ihr_fee)?;
                // fees.value_imported.grams.add(env.fwd_fee_remaining())?;
            }
            InMsg::DiscardedFinal(_) => {
                fees.fees_collected = info.fwd_fee.into_inner();

                // fees.value_imported.grams = info.fwd_fee;
            }
            InMsg::DiscardedTransit(_) => {
                fees.fees_collected = info.fwd_fee.into_inner();

                // fees.value_imported.grams = info.fwd_fee;
            }
            InMsg::None => return Err(Error::InvalidArg("Wrong InMsg type".to_string())),
        }
        Ok(fees)
    }
}

impl<'a> Store for InMsg<'a> {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        match self {
            InMsg::External(ref x) => {
                ok!(builder.store_u8(MSG_IMPORT_EXT));
                ok!(x.store_into(builder, context));
            }
            InMsg::Immediate(ref x) => {
                ok!(builder.store_u8(MSG_IMPORT_IMM));
                ok!(x.store_into(builder, context));
            }
            InMsg::Final(ref x) => {
                ok!(builder.store_u8(MSG_IMPORT_FIN));
                ok!(x.store_into(builder, context));
            }
            InMsg::Transit(ref x) => {
                ok!(builder.store_u8(MSG_IMPORT_TR));
                ok!(x.store_into(builder, context));
            }
            InMsg::DiscardedFinal(ref x) => {
                ok!(builder.store_u8(MSG_DISCARD_FIN));
                ok!(x.store_into(builder, context));
            }
            InMsg::DiscardedTransit(ref x) => {
                ok!(builder.store_u8(MSG_DISCARD_TR));
                ok!(x.store_into(builder, context));
            }
            InMsg::None => {} // Due to ChildCell it is need sometimes to serialize default InMsg
        }
        Ok(())
    }
}

impl<'a> Load<'a> for InMsg<'a> {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let tag = ok!(slice.load_u8());
        match tag {
            MSG_IMPORT_EXT => Ok(InMsg::External(InMsgExternal::load_from(slice)?)),
            MSG_IMPORT_IMM => Ok(InMsg::Immediate(InMsgFinal::load_from(slice)?)),
            MSG_IMPORT_FIN => Ok(InMsg::Final(InMsgFinal::load_from(slice)?)),
            MSG_IMPORT_TR => Ok(InMsg::Transit(InMsgTransit::load_from(slice)?)),
            MSG_DISCARD_FIN => Ok(InMsg::DiscardedFinal(InMsgDiscardedFinal::load_from(
                slice,
            )?)),
            MSG_DISCARD_TR => Ok(InMsg::DiscardedTransit(InMsgDiscardedTransit::load_from(
                slice,
            )?)),
            tag => Err(Error::InvalidArg(format!("Wrong InMsg type - {tag}"))),
        }
    }
}

/// External message
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InMsgExternal<'a> {
    /// Message
    msg: Lazy<Message<'a>>,
    /// Transaction
    transaction: Lazy<Transaction>,
}

impl<'a> InMsgExternal<'a> {
    /// Create from message and transaction
    pub fn with_cells(msg_cell: Cell, tr_cell: Cell) -> Self {
        InMsgExternal {
            msg: Lazy::load_from(&mut msg_cell.as_slice().unwrap()).unwrap(),
            transaction: Lazy::load_from(&mut tr_cell.as_slice().unwrap()).unwrap(),
        }
    }

    /// Read message
    pub fn read_message(&'a self) -> Result<Message<'a>, Error> {
        self.msg.load()
    }

    /// Read owned message struct from envelope
    pub fn read_owned_message(&'a self) -> Result<OwnedMessage, Error> {
        self.msg.clone().cast_into::<OwnedMessage>().load()
    }

    /// Read message cell
    pub fn message_cell(&self) -> Cell {
        self.msg.cell.clone()
    }

    /// Read transaction
    pub fn read_transaction(&self) -> Result<Transaction, Error> {
        self.transaction.load()
    }

    /// Read transaction cell
    pub fn transaction_cell(&self) -> Cell {
        self.transaction.cell.clone()
    }
}

impl<'a> Store for InMsgExternal<'a> {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        _context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_reference(self.msg.cell.clone()));
        ok!(builder.store_reference(self.transaction.cell.clone()));
        Ok(())
    }
}

impl<'a> Load<'a> for InMsgExternal<'a> {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let msg = ok!(Lazy::load_from(slice));
        let transaction = ok!(Lazy::load_from(slice));
        Ok(Self { msg, transaction })
    }
}

/// Final message
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InMsgFinal<'a> {
    /// Envelope message
    in_msg: Lazy<MsgEnvelope<'a>>,
    /// Transaction
    transaction: Lazy<Transaction>,
    /// Forward fee
    pub fwd_fee: u128,
}

impl<'a> InMsgFinal<'a> {
    /// Create from message and transaction and forward fee
    pub fn with_cells(msg_cell: Cell, tr_cell: Cell, fwd_fee: u128) -> Self {
        InMsgFinal {
            in_msg: Lazy::load_from(&mut msg_cell.as_slice().unwrap()).unwrap(),
            transaction: Lazy::load_from(&mut tr_cell.as_slice().unwrap()).unwrap(),
            fwd_fee,
        }
    }

    /// Read envelope message
    pub fn read_envelope_message(&'a self) -> Result<MsgEnvelope<'a>, Error> {
        self.in_msg.load()
    }

    /// Read envelope in message
    pub fn read_envelope_in_message(&'a self) -> Result<OwnedMessage, Error> {
        self.in_msg.load().and_then(|s| s.read_owned_message())
    }

    /// Read envelope message cell
    pub fn envelope_message_cell(&self) -> Cell {
        self.in_msg.cell.clone()
    }

    /// Read message hash
    pub fn envelope_message_hash(&self) -> HashBytes {
        *self.in_msg.cell.repr_hash()
    }

    /// Read transaction
    pub fn read_transaction(&self) -> Result<Transaction, Error> {
        self.transaction.load()
    }

    /// Read transaction cell
    pub fn transaction_cell(&self) -> Cell {
        self.transaction.cell.clone()
    }

    /// Read forward fee
    pub fn fwd_fee(&self) -> &u128 {
        &self.fwd_fee
    }
}

impl<'a> Store for InMsgFinal<'a> {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        _context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_reference(self.in_msg.cell.clone()));
        ok!(builder.store_reference(self.transaction.cell.clone()));
        ok!(builder.store_u128(self.fwd_fee));
        Ok(())
    }
}

impl<'a> Load<'a> for InMsgFinal<'a> {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let in_msg = ok!(Lazy::load_from(slice));
        let transaction = ok!(Lazy::load_from(slice));
        let fwd_fee = ok!(slice.load_u128());
        Ok(Self {
            in_msg,
            transaction,
            fwd_fee,
        })
    }
}

/// In message transit
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InMsgTransit<'a> {
    /// In message
    in_msg: Lazy<MsgEnvelope<'a>>,
    /// Out message
    out_msg: Lazy<MsgEnvelope<'a>>,
    /// Transit fee
    pub transit_fee: u128,
}

impl<'a> InMsgTransit<'a> {
    /// Create from in message, out message and transit fee
    pub fn with_cells(in_msg_cell: Cell, out_msg_cell: Cell, transit_fee: u128) -> Self {
        Self {
            in_msg: Lazy::load_from(&mut in_msg_cell.as_slice().unwrap()).unwrap(),
            out_msg: Lazy::load_from(&mut out_msg_cell.as_slice().unwrap()).unwrap(),
            transit_fee,
        }
    }

    /// Read in message
    pub fn read_in_message(&'a self) -> Result<MsgEnvelope<'a>, Error> {
        self.in_msg.load()
    }

    /// Read in message cell
    pub fn in_envelope_message_cell(&self) -> Cell {
        self.in_msg.cell.clone()
    }

    /// Read in message hash
    pub fn in_envelope_message_hash(&self) -> HashBytes {
        *self.in_msg.cell.repr_hash()
    }

    /// Read envelope owned message
    pub fn read_envelope_in_message(&'a self) -> Result<OwnedMessage, Error> {
        self.in_msg.load().and_then(|s| s.read_owned_message())
    }

    /// Read out message
    pub fn read_out_message(&'a self) -> Result<MsgEnvelope<'a>, Error> {
        self.out_msg.load()
    }

    /// Read out message cell
    pub fn out_envelope_message_cell(&self) -> Cell {
        self.out_msg.cell.clone()
    }

    /// Read out message hash
    pub fn out_envelope_message_hash(&self) -> HashBytes {
        *self.out_msg.cell.repr_hash()
    }

    /// Read transit fee
    pub fn transit_fee(&self) -> &u128 {
        &self.transit_fee
    }
}

impl<'a> Store for InMsgTransit<'a> {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        _context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_reference(self.in_msg.cell.clone()));
        ok!(builder.store_reference(self.out_msg.cell.clone()));
        ok!(builder.store_u128(self.transit_fee));
        Ok(())
    }
}

impl<'a> Load<'a> for InMsgTransit<'a> {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let in_msg = ok!(Lazy::load_from(slice));
        let out_msg = ok!(Lazy::load_from(slice));
        let transit_fee = ok!(slice.load_u128());
        Ok(Self {
            in_msg,
            out_msg,
            transit_fee,
        })
    }
}

/// In message discarded final
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InMsgDiscardedFinal<'a> {
    /// In message
    in_msg: Lazy<MsgEnvelope<'a>>,
    /// Transaction id
    pub transaction_id: u64,
    /// Forward fee
    pub fwd_fee: u128,
}

impl<'a> InMsgDiscardedFinal<'a> {
    /// Create from in message, transaction id and forward fee
    pub fn with_cells(in_msg_cell: Cell, transaction_id: u64, fee: u128) -> Self {
        Self {
            in_msg: Lazy::load_from(&mut in_msg_cell.as_slice().unwrap()).unwrap(),
            transaction_id,
            fwd_fee: fee,
        }
    }

    /// Read in message
    pub fn read_envelope_message(&'a self) -> Result<MsgEnvelope<'a>, Error> {
        self.in_msg.load()
    }

    /// Read envelope owned message
    pub fn read_envelope_in_message(&'a self) -> Result<OwnedMessage, Error> {
        self.in_msg.load().and_then(|s| s.read_owned_message())
    }

    /// Read in message cell
    pub fn envelope_message_cell(&self) -> Cell {
        self.in_msg.cell.clone()
    }

    /// Read in message hash
    pub fn envelope_message_hash(&self) -> HashBytes {
        *self.in_msg.cell.repr_hash()
    }

    /// Read in message cell
    pub fn message_cell(&self) -> Result<Cell, Error> {
        Ok(self.read_envelope_message()?.message_cell())
    }

    /// Read transaction id
    pub fn transaction_id(&self) -> u64 {
        self.transaction_id
    }

    /// Read forward fee
    pub fn fwd_fee(&self) -> &u128 {
        &self.fwd_fee
    }
}

impl<'a> Store for InMsgDiscardedFinal<'a> {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        _context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_reference(self.in_msg.cell.clone()));
        ok!(builder.store_u64(self.transaction_id));
        ok!(builder.store_u128(self.fwd_fee));
        Ok(())
    }
}

impl<'a> Load<'a> for InMsgDiscardedFinal<'a> {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let in_msg = ok!(Lazy::load_from(slice));
        let transaction_id = ok!(slice.load_u64());
        let fwd_fee = ok!(slice.load_u128());
        Ok(Self {
            in_msg,
            transaction_id,
            fwd_fee,
        })
    }
}

/// In message discarded transit
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InMsgDiscardedTransit<'a> {
    /// In message
    in_msg: Lazy<MsgEnvelope<'a>>,
    /// Transaction id
    transaction_id: u64,
    /// Forward fee
    fwd_fee: u128,
    /// Proof delivered
    proof_delivered: Cell,
}

impl<'a> InMsgDiscardedTransit<'a> {
    /// Create from in message, transaction id, forward fee and proof
    pub fn with_cells(in_msg_cell: Cell, transaction_id: u64, fee: u128, proof: Cell) -> Self {
        InMsgDiscardedTransit {
            in_msg: Lazy::load_from(&mut in_msg_cell.as_slice().unwrap()).unwrap(),
            transaction_id,
            fwd_fee: fee,
            proof_delivered: proof,
        }
    }

    /// Read in message
    pub fn read_envelope_message(&'a self) -> Result<MsgEnvelope<'a>, Error> {
        self.in_msg.load()
    }

    /// Read envelope owned message
    pub fn read_envelope_in_message(&'a self) -> Result<OwnedMessage, Error> {
        self.in_msg.load().and_then(|s| s.read_owned_message())
    }

    /// Read in message cell
    pub fn envelope_message_cell(&self) -> Cell {
        self.in_msg.cell.clone()
    }

    /// Read in message hash
    pub fn envelope_message_hash(&self) -> HashBytes {
        *self.in_msg.cell.repr_hash()
    }

    /// Read in message cell
    pub fn message_cell(&self) -> Result<Cell, Error> {
        Ok(self.read_envelope_message()?.message_cell())
    }

    /// Read transaction id
    pub fn transaction_id(&self) -> u64 {
        self.transaction_id
    }

    /// Read forward fee
    pub fn fwd_fee(&self) -> &u128 {
        &self.fwd_fee
    }

    /// Read proof delivered
    pub fn proof_delivered(&self) -> &Cell {
        &self.proof_delivered
    }
}

impl<'a> Store for InMsgDiscardedTransit<'a> {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        _context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        ok!(builder.store_reference(self.in_msg.cell.clone()));
        ok!(builder.store_u64(self.transaction_id));
        ok!(builder.store_u128(self.fwd_fee));
        ok!(builder.store_reference(self.proof_delivered.clone()));
        Ok(())
    }
}

impl<'a> Load<'a> for InMsgDiscardedTransit<'a> {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let in_msg = ok!(Lazy::load_from(slice));
        let transaction_id = ok!(slice.load_u64());
        let fwd_fee = ok!(slice.load_u128());
        let proof_delivered = ok!(slice.load_reference_cloned());
        Ok(Self {
            in_msg,
            transaction_id,
            fwd_fee,
            proof_delivered,
        })
    }
}
