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
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InMsg {
    /// Inbound external messages
    External(InMsgExternal),
    /// Internal messages with destinations in this block
    Immediate(InMsgFinal),
    /// Immediately routed internal messages
    Final(InMsgFinal),
    /// Transit internal messages
    Transit(InMsgTransit),
    /// Discarded internal messages with destinations in this block
    DiscardedFinal(InMsgDiscardedFinal),
    /// Discarded transit internal messages
    DiscardedTransit(InMsgDiscardedTransit),
}

impl fmt::Display for InMsg {
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
        }
    }
}

impl InMsg {
    /// Create external
    pub fn external(msg_cell: Cell, tr_cell: Cell) -> InMsg {
        InMsg::External(InMsgExternal::with_cells(msg_cell, tr_cell))
    }
    /// Create Immediate
    pub fn immediate(msg_cell: Cell, tr_cell: Cell, fwd_fee: u128) -> InMsg {
        InMsg::Immediate(InMsgFinal::with_cells(msg_cell, tr_cell, fwd_fee))
    }
    /// Create Final
    pub fn final_msg(msg_cell: Cell, tr_cell: Cell, fwd_fee: u128) -> InMsg {
        InMsg::Final(InMsgFinal::with_cells(msg_cell, tr_cell, fwd_fee))
    }
    /// Create Transit
    pub fn transit(in_msg_cell: Cell, out_msg_cell: Cell, fwd_fee: u128) -> InMsg {
        InMsg::Transit(InMsgTransit::with_cells(in_msg_cell, out_msg_cell, fwd_fee))
    }
    /// Create DiscardedFinal
    pub fn discarded_final(env_cell: Cell, tr_id: u64, fwd_fee: u128) -> InMsg {
        InMsg::DiscardedFinal(InMsgDiscardedFinal::with_cells(env_cell, tr_id, fwd_fee))
    }
    /// Create DiscardedTransit
    pub fn discarded_transit(env_cell: Cell, tr_id: u64, fwd_fee: u128, proof: Cell) -> InMsg {
        InMsg::DiscardedTransit(InMsgDiscardedTransit::with_cells(
            env_cell, tr_id, fwd_fee, proof,
        ))
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
        }
    }

    /// Get transaction from inbound message
    /// Transaction exist only in External, IHR, Immediate and Final inbound messages.
    /// For other messages function returned None
    pub fn load_transaction(&self) -> Result<Option<Transaction>, Error> {
        Ok(match self {
            InMsg::External(ref x) => Some(x.load_transaction()?),
            InMsg::Immediate(ref x) => Some(x.load_transaction()?),
            InMsg::Final(ref x) => Some(x.load_transaction()?),
            InMsg::Transit(ref _x) => None,
            InMsg::DiscardedFinal(ref _x) => None,
            InMsg::DiscardedTransit(ref _x) => None,
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
        }
    }

    /// Get message
    pub fn load_message(&self) -> Result<OwnedMessage, Error> {
        match self {
            InMsg::External(x) => x.load_owned_message(),
            InMsg::Immediate(x) => x.load_envelope_in_message(),
            InMsg::Final(x) => x.load_envelope_in_message(),
            InMsg::Transit(x) => x.load_envelope_in_message(),
            InMsg::DiscardedFinal(x) => x.load_envelope_in_message(),
            InMsg::DiscardedTransit(x) => x.load_envelope_in_message(),
        }
    }

    /// Get message cell
    pub fn message_cell(&self) -> Result<Cell, Error> {
        Ok(match self {
            InMsg::External(ref x) => x.msg.clone(),
            InMsg::Immediate(ref x) => x.load_envelope_message()?.message_cell(),
            InMsg::Final(ref x) => x.load_envelope_message()?.message_cell(),
            InMsg::Transit(ref x) => x.load_in_message()?.message_cell(),
            InMsg::DiscardedFinal(ref x) => x.load_envelope_message()?.message_cell(),
            InMsg::DiscardedTransit(ref x) => x.load_envelope_message()?.message_cell(),
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
        }
    }

    /// Get in envelope message
    pub fn load_in_msg_envelope(&self) -> Result<Option<MsgEnvelope>, Error> {
        Ok(match self {
            InMsg::External(_) => None,
            InMsg::Immediate(ref x) => Some(x.load_envelope_message()?),
            InMsg::Final(ref x) => Some(x.load_envelope_message()?),
            InMsg::Transit(ref x) => Some(x.load_in_message()?),
            InMsg::DiscardedFinal(ref x) => Some(x.load_envelope_message()?),
            InMsg::DiscardedTransit(ref x) => Some(x.load_envelope_message()?),
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
        }
    }

    /// Get out envelope message
    pub fn load_out_msg_envelope(&self) -> Result<Option<MsgEnvelope>, Error> {
        match self {
            InMsg::External(_) => Ok(None),
            InMsg::Immediate(_) => Ok(None),
            InMsg::Final(_) => Ok(None),
            InMsg::Transit(ref x) => Some(x.load_out_message()).transpose(),
            InMsg::DiscardedFinal(_) => Ok(None),
            InMsg::DiscardedTransit(_) => Ok(None),
        }
    }

    /// Get fee
    pub fn get_fee(&self) -> Result<ImportFees, Error> {
        let msg = self.load_message()?;
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
                let env = x.load_envelope_message()?;
                if env.fwd_fee_remaining != *x.fwd_fee() {
                    return Err(Error::InvalidData);
                }
                fees.fees_collected = env.fwd_fee_remaining;
                //
                // fees.value_imported = info.value.clone();
                // fees.value_imported.grams.add(env.fwd_fee_remaining())?;
                // fees.value_imported.grams.add(&header.ihr_fee)?;
            }
            InMsg::Transit(ref x) => {
                let env = x.load_in_message()?;
                if env.fwd_fee_remaining < *x.transit_fee() {
                    return Err(Error::InvalidData);
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
        }
        Ok(fees)
    }
}

impl Store for InMsg {
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
        }
        Ok(())
    }
}

impl<'a> Load<'a> for InMsg {
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
            _tag => Err(Error::InvalidData),
        }
    }
}

/// External message
#[derive(Clone, Debug, Eq, PartialEq, Store, Load)]
pub struct InMsgExternal {
    /// Message
    pub msg: Cell,
    /// Transaction
    pub transaction: Lazy<Transaction>,
}

impl InMsgExternal {
    /// Create from message and transaction
    pub fn with_cells(msg_cell: Cell, tr_cell: Cell) -> Self {
        InMsgExternal {
            msg: msg_cell,
            transaction: Lazy::load_from(&mut tr_cell.as_slice().unwrap()).unwrap(),
        }
    }

    /// Load message
    pub fn load_message(&self) -> Result<Message, Error> {
        Message::load_from(&mut self.msg.as_slice()?)
    }

    /// Load owned message struct from envelope
    pub fn load_owned_message(&self) -> Result<OwnedMessage, Error> {
        OwnedMessage::load_from(&mut self.msg.as_slice()?)
    }

    /// Load transaction
    pub fn load_transaction(&self) -> Result<Transaction, Error> {
        self.transaction.load()
    }

    /// Load transaction cell
    pub fn transaction_cell(&self) -> Cell {
        self.transaction.cell.clone()
    }
}

/// Final message
#[derive(Clone, Debug, Eq, PartialEq, Store, Load)]
pub struct InMsgFinal {
    /// Envelope message
    pub in_msg: Lazy<MsgEnvelope>,
    /// Transaction
    pub transaction: Lazy<Transaction>,
    /// Forward fee
    pub fwd_fee: u128,
}

impl InMsgFinal {
    /// Create from message and transaction and forward fee
    pub fn with_cells(msg_cell: Cell, tr_cell: Cell, fwd_fee: u128) -> Self {
        InMsgFinal {
            in_msg: Lazy::load_from(&mut msg_cell.as_slice().unwrap()).unwrap(),
            transaction: Lazy::load_from(&mut tr_cell.as_slice().unwrap()).unwrap(),
            fwd_fee,
        }
    }

    /// Load envelope message
    pub fn load_envelope_message(&self) -> Result<MsgEnvelope, Error> {
        self.in_msg.load()
    }

    /// Load envelope in message
    pub fn load_envelope_in_message(&self) -> Result<OwnedMessage, Error> {
        self.in_msg.load().and_then(|s| s.load_owned_message())
    }

    /// Load envelope message cell
    pub fn envelope_message_cell(&self) -> Cell {
        self.in_msg.cell.clone()
    }

    /// Load message hash
    pub fn envelope_message_hash(&self) -> HashBytes {
        *self.in_msg.cell.repr_hash()
    }

    /// Load transaction
    pub fn load_transaction(&self) -> Result<Transaction, Error> {
        self.transaction.load()
    }

    /// Load transaction cell
    pub fn transaction_cell(&self) -> Cell {
        self.transaction.cell.clone()
    }

    /// Load forward fee
    pub fn fwd_fee(&self) -> &u128 {
        &self.fwd_fee
    }
}

/// In message transit
#[derive(Clone, Debug, Eq, PartialEq, Store, Load)]
pub struct InMsgTransit {
    /// In message
    in_msg: Lazy<MsgEnvelope>,
    /// Out message
    out_msg: Lazy<MsgEnvelope>,
    /// Transit fee
    pub transit_fee: u128,
}

impl InMsgTransit {
    /// Create from in message, out message and transit fee
    pub fn with_cells(in_msg_cell: Cell, out_msg_cell: Cell, transit_fee: u128) -> Self {
        Self {
            in_msg: Lazy::load_from(&mut in_msg_cell.as_slice().unwrap()).unwrap(),
            out_msg: Lazy::load_from(&mut out_msg_cell.as_slice().unwrap()).unwrap(),
            transit_fee,
        }
    }

    /// Load in message
    pub fn load_in_message(&self) -> Result<MsgEnvelope, Error> {
        self.in_msg.load()
    }

    /// Load in message cell
    pub fn in_envelope_message_cell(&self) -> Cell {
        self.in_msg.cell.clone()
    }

    /// Load in message hash
    pub fn in_envelope_message_hash(&self) -> HashBytes {
        *self.in_msg.cell.repr_hash()
    }

    /// Load envelope owned message
    pub fn load_envelope_in_message(&self) -> Result<OwnedMessage, Error> {
        self.in_msg.load().and_then(|s| s.load_owned_message())
    }

    /// Load out message
    pub fn load_out_message(&self) -> Result<MsgEnvelope, Error> {
        self.out_msg.load()
    }

    /// Load out message cell
    pub fn out_envelope_message_cell(&self) -> Cell {
        self.out_msg.cell.clone()
    }

    /// Load out message hash
    pub fn out_envelope_message_hash(&self) -> HashBytes {
        *self.out_msg.cell.repr_hash()
    }

    /// Load transit fee
    pub fn transit_fee(&self) -> &u128 {
        &self.transit_fee
    }
}

/// In message discarded final
#[derive(Clone, Debug, Eq, PartialEq, Store, Load)]
pub struct InMsgDiscardedFinal {
    /// In message
    in_msg: Lazy<MsgEnvelope>,
    /// Transaction id
    pub transaction_id: u64,
    /// Forward fee
    pub fwd_fee: u128,
}

impl InMsgDiscardedFinal {
    /// Create from in message, transaction id and forward fee
    pub fn with_cells(in_msg_cell: Cell, transaction_id: u64, fee: u128) -> Self {
        Self {
            in_msg: Lazy::load_from(&mut in_msg_cell.as_slice().unwrap()).unwrap(),
            transaction_id,
            fwd_fee: fee,
        }
    }

    /// Load in message
    pub fn load_envelope_message(&self) -> Result<MsgEnvelope, Error> {
        self.in_msg.load()
    }

    /// Load envelope owned message
    pub fn load_envelope_in_message(&self) -> Result<OwnedMessage, Error> {
        self.in_msg.load().and_then(|s| s.load_owned_message())
    }

    /// Load in message cell
    pub fn envelope_message_cell(&self) -> Cell {
        self.in_msg.cell.clone()
    }

    /// Load in message hash
    pub fn envelope_message_hash(&self) -> HashBytes {
        *self.in_msg.cell.repr_hash()
    }

    /// Load in message cell
    pub fn message_cell(&self) -> Result<Cell, Error> {
        Ok(self.load_envelope_message()?.message_cell())
    }

    /// Load transaction id
    pub fn transaction_id(&self) -> u64 {
        self.transaction_id
    }

    /// Load forward fee
    pub fn fwd_fee(&self) -> &u128 {
        &self.fwd_fee
    }
}

/// In message discarded transit
#[derive(Clone, Debug, Eq, PartialEq, Store, Load)]
pub struct InMsgDiscardedTransit {
    /// In message
    in_msg: Lazy<MsgEnvelope>,
    /// Transaction id
    transaction_id: u64,
    /// Forward fee
    fwd_fee: u128,
    /// Proof delivered
    proof_delivered: Cell,
}

impl InMsgDiscardedTransit {
    /// Create from in message, transaction id, forward fee and proof
    pub fn with_cells(in_msg_cell: Cell, transaction_id: u64, fee: u128, proof: Cell) -> Self {
        InMsgDiscardedTransit {
            in_msg: Lazy::load_from(&mut in_msg_cell.as_slice().unwrap()).unwrap(),
            transaction_id,
            fwd_fee: fee,
            proof_delivered: proof,
        }
    }

    /// Load in message
    pub fn load_envelope_message(&self) -> Result<MsgEnvelope, Error> {
        self.in_msg.load()
    }

    /// Load envelope owned message
    pub fn load_envelope_in_message(&self) -> Result<OwnedMessage, Error> {
        self.in_msg.load().and_then(|s| s.load_owned_message())
    }

    /// Load in message cell
    pub fn envelope_message_cell(&self) -> Cell {
        self.in_msg.cell.clone()
    }

    /// Load in message hash
    pub fn envelope_message_hash(&self) -> HashBytes {
        *self.in_msg.cell.repr_hash()
    }

    /// Load in message cell
    pub fn message_cell(&self) -> Result<Cell, Error> {
        Ok(self.load_envelope_message()?.message_cell())
    }

    /// Load transaction id
    pub fn transaction_id(&self) -> u64 {
        self.transaction_id
    }

    /// Load forward fee
    pub fn fwd_fee(&self) -> &u128 {
        &self.fwd_fee
    }

    /// Load proof delivered
    pub fn proof_delivered(&self) -> &Cell {
        &self.proof_delivered
    }
}
