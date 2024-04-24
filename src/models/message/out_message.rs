use crate::cell::*;
use crate::error::Error;
use crate::models::envelope_message::MsgEnvelope;
use crate::models::in_message::InMsg;
use crate::models::{CurrencyCollection, Lazy, Message, MsgInfo, OwnedMessage, Transaction};
use crate::prelude::HashBytes;

//constructor tags of OutMsg variant OUT_MSG_EXT
const OUT_MSG_EXT: u8 = 0b000;
//constructor tags of OutMsg variant OUT_MSG_IMM
const OUT_MSG_IMM: u8 = 0b010;
//constructor tags of OutMsg variant OUT_MSG_NEW
const OUT_MSG_NEW: u8 = 0b001;
//constructor tags of OutMsg variant OUT_MSG_DEQ_IMM
const OUT_MSG_DEQ_IMM: u8 = 0b100;
//constructor tags of OutMsg variant OUT_MSG_DEQ_SHORT
const OUT_MSG_DEQ_SHORT: u8 = 0b1101;

/// EnqueuedMsg structure
#[derive(Clone, Debug, Eq, PartialEq, Store, Load)]
pub struct EnqueuedMsg {
    /// Enqueued message lt
    pub enqueued_lt: u64,
    /// Out message
    pub out_msg: Lazy<MsgEnvelope>,
}

impl EnqueuedMsg {
    /// New instance EnqueuedMsg structure
    pub fn with_param(enqueued_lt: u64, env: &MsgEnvelope) -> Result<Self, Error> {
        Ok(EnqueuedMsg {
            enqueued_lt,
            out_msg: Lazy::new(env)?,
        })
    }

    /// created lt
    pub fn created_lt(&self) -> Result<u64, Error> {
        let binding = self.load_message()?;
        let message = binding.load_message()?;

        if let MsgInfo::ExtOut(msg_info) = message.info {
            Ok(msg_info.created_lt)
        } else {
            Err(Error::InvalidData)
        }
    }

    /// enqueued lt
    pub fn enqueued_lt(&self) -> u64 {
        self.enqueued_lt
    }

    /// out msg cell
    pub fn out_msg_cell(&self) -> Cell {
        self.out_msg.cell.clone()
    }

    /// load message
    pub fn load_message(&self) -> Result<MsgEnvelope, Error> {
        self.out_msg.load()
    }
}

/// OutMsg structure
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OutMsg {
    /// External outbound messages, or “messages to nowhere”
    External(OutMsgExternal),
    /// Ordinary (internal) outbound messages
    New(OutMsgNew),
    /// Immediately processed internal outbound messages
    Immediate(OutMsgImmediate),
    /// OutMsgDequeueImmediate
    DequeueImmediate(OutMsgDequeueImmediate),
    /// OutMsgDequeueShort
    DequeueShort(OutMsgDequeueShort),
}

impl OutMsg {
    /// Create External
    pub fn external(msg_cell: Cell, tr_cell: Cell) -> OutMsg {
        OutMsg::External(OutMsgExternal::with_cells(msg_cell, tr_cell))
    }
    /// Create Ordinary internal message
    pub fn new(env_cell: Cell, tr_cell: Cell) -> OutMsg {
        OutMsg::New(OutMsgNew::with_cells(env_cell, tr_cell))
    }
    /// Create Immediate internal message
    pub fn immediate(env_cell: Cell, tr_cell: Cell, reimport_msg_cell: Cell) -> OutMsg {
        OutMsg::Immediate(OutMsgImmediate::with_cells(
            env_cell,
            tr_cell,
            reimport_msg_cell,
        ))
    }

    /// Create Dequeue Short internal message
    pub fn dequeue_short(
        msg_env_hash: HashBytes,
        next_workchain: i8,
        next_addr_pfx: u64,
        import_block_lt: u64,
    ) -> OutMsg {
        OutMsg::DequeueShort(OutMsgDequeueShort {
            msg_env_hash,
            next_workchain,
            next_addr_pfx,
            import_block_lt,
        })
    }

    /// Create Dequeue immediate message
    pub fn dequeue_immediate(env_cell: Cell, reimport_msg_cell: Cell) -> OutMsg {
        OutMsg::DequeueImmediate(OutMsgDequeueImmediate::with_cells(
            env_cell,
            reimport_msg_cell,
        ))
    }

    /// tag
    pub fn tag(&self) -> u8 {
        match self {
            OutMsg::External(_) => OUT_MSG_EXT,
            OutMsg::Immediate(_) => OUT_MSG_IMM,
            OutMsg::New(_) => OUT_MSG_NEW,
            OutMsg::DequeueShort(_) => OUT_MSG_DEQ_SHORT, // 4 bits
            OutMsg::DequeueImmediate(_) => OUT_MSG_DEQ_IMM,
        }
    }

    /// message envelop (if exists)
    pub fn load_out_message(&self) -> Result<Option<MsgEnvelope>, Error> {
        Ok(match self {
            OutMsg::External(_) => None,
            OutMsg::Immediate(ref x) => Some(x.load_envelope_message()?),
            OutMsg::New(ref x) => Some(x.load_envelope_message()?),
            OutMsg::DequeueShort(_) => None,
            OutMsg::DequeueImmediate(ref x) => Some(x.load_envelope_message()?),
        })
    }

    /// message envelop (if exists) cell
    pub fn out_message_cell(&self) -> Option<Cell> {
        match self {
            OutMsg::External(_) => None,
            OutMsg::Immediate(ref x) => Some(x.out_message_cell()),
            OutMsg::New(ref x) => Some(x.out_message_cell()),
            OutMsg::DequeueShort(_) => None,
            OutMsg::DequeueImmediate(ref x) => Some(x.out_message_cell()),
        }
    }

    /// load message (if exists)
    pub fn load_message(&self) -> Result<Option<OwnedMessage>, Error> {
        Ok(match self {
            OutMsg::External(ref x) => Some(x.load_owned_message()?),
            OutMsg::Immediate(ref x) => {
                let msg_envelope = x.load_envelope_message()?;
                Some(msg_envelope.load_owned_message()?)
            }
            OutMsg::New(ref x) => {
                let msg_envelope = x.load_envelope_message()?;
                Some(msg_envelope.load_owned_message()?)
            }
            OutMsg::DequeueShort(_) => None,
            OutMsg::DequeueImmediate(ref x) => {
                let msg_envelope = x.load_envelope_message()?;
                Some(msg_envelope.load_owned_message()?)
            }
        })
    }

    /// message hash
    pub fn read_message_hash(&self) -> Result<HashBytes, Error> {
        Ok(match self {
            OutMsg::External(ref x) => *x.message_cell().repr_hash(),
            OutMsg::Immediate(ref x) => x.load_envelope_message()?.message_hash(),
            OutMsg::New(ref x) => x.load_envelope_message()?.message_hash(),
            OutMsg::DequeueShort(_) => return Err(Error::InvalidData),
            OutMsg::DequeueImmediate(ref x) => x.load_envelope_message()?.message_hash(),
        })
    }

    /// message cell (if exists)
    pub fn message_cell(&self) -> Result<Option<Cell>, Error> {
        Ok(match self {
            OutMsg::External(ref x) => Some(x.message_cell()),
            OutMsg::Immediate(ref x) => Some(x.load_envelope_message()?.message_cell()),
            OutMsg::New(ref x) => Some(x.load_envelope_message()?.message_cell()),
            OutMsg::DequeueShort(_) => None,
            OutMsg::DequeueImmediate(ref x) => Some(x.load_envelope_message()?.message_cell()),
        })
    }

    /// message envelope hash (if exists)
    pub fn envelope_message_hash(&self) -> Option<HashBytes> {
        match self {
            OutMsg::External(_) => None,
            OutMsg::Immediate(ref x) => Some(*x.out_message_cell().repr_hash()),
            OutMsg::New(ref x) => Some(*x.out_message_cell().repr_hash()),
            OutMsg::DequeueShort(ref x) => Some(x.msg_env_hash),
            OutMsg::DequeueImmediate(ref x) => Some(*x.out_message_cell().repr_hash()),
        }
    }

    /// transaction_cell
    pub fn transaction_cell(&self) -> Option<Cell> {
        match self {
            OutMsg::External(ref x) => Some(x.transaction_cell()),
            OutMsg::Immediate(ref x) => Some(x.transaction_cell()),
            OutMsg::New(ref x) => Some(x.transaction_cell()),
            OutMsg::DequeueShort(ref _x) => None,
            OutMsg::DequeueImmediate(ref _x) => None,
        }
    }

    /// load_transaction
    pub fn load_transaction(&self) -> Result<Option<Transaction>, Error> {
        match self.transaction_cell() {
            Some(cell) => Ok(Some(Transaction::load_from(&mut cell.as_slice().unwrap())?)),
            None => Ok(None),
        }
    }

    /// Load reimport message
    pub fn load_reimport_message(&self) -> Result<Option<InMsg>, Error> {
        match self {
            OutMsg::Immediate(ref x) => Some(x.load_reimport_message()).transpose(),
            OutMsg::DequeueImmediate(ref x) => Some(x.load_reimport_message()).transpose(),
            _ => Ok(None),
        }
    }

    /// Reimport cell
    pub fn reimport_cell(&self) -> Option<Cell> {
        match self {
            OutMsg::Immediate(ref x) => Some(x.reimport_message_cell()),
            OutMsg::DequeueImmediate(ref x) => Some(x.reimport_message_cell()),
            _ => None,
        }
    }

    /// Exported value
    pub fn exported_value(&self) -> Result<CurrencyCollection, Error> {
        let mut exported = CurrencyCollection::default();
        if let OutMsg::New(ref x) = self {
            let env = x.load_envelope_message()?;
            exported.tokens += env.fwd_fee_remaining;
        }
        Ok(exported)
    }

    /// At and lt
    pub fn at_and_lt(&self) -> Result<Option<(u32, u64)>, Error> {
        if let Some(m) = self.load_message()? {
            if let MsgInfo::ExtOut(msg_info) = m.info {
                return Ok(Some((msg_info.created_at, msg_info.created_lt)));
            }
        }
        Ok(None)
    }
}

impl Store for OutMsg {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        match self {
            OutMsg::External(ref x) => {
                ok!(builder.store_u8(OUT_MSG_EXT));
                ok!(x.store_into(builder, context));
            }
            OutMsg::Immediate(ref x) => {
                ok!(builder.store_u8(OUT_MSG_IMM));
                ok!(x.store_into(builder, context));
            }
            OutMsg::New(ref x) => {
                ok!(builder.store_u8(OUT_MSG_NEW));
                ok!(x.store_into(builder, context));
            }
            OutMsg::DequeueShort(ref x) => {
                ok!(builder.store_u8(OUT_MSG_DEQ_SHORT));
                ok!(x.store_into(builder, context));
            }
            OutMsg::DequeueImmediate(ref x) => {
                ok!(builder.store_u8(OUT_MSG_DEQ_IMM));
                ok!(x.store_into(builder, context));
            }
        }
        Ok(())
    }
}

impl<'a> Load<'a> for OutMsg {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let tag = ok!(slice.load_u8());
        match tag {
            OUT_MSG_EXT => Ok(OutMsg::External(OutMsgExternal::load_from(slice)?)),
            OUT_MSG_IMM => Ok(OutMsg::Immediate(OutMsgImmediate::load_from(slice)?)),
            OUT_MSG_NEW => Ok(OutMsg::New(OutMsgNew::load_from(slice)?)),
            OUT_MSG_DEQ_IMM => Ok(OutMsg::DequeueImmediate(OutMsgDequeueImmediate::load_from(
                slice,
            )?)),
            OUT_MSG_DEQ_SHORT => Ok(OutMsg::DequeueShort(OutMsgDequeueShort::load_from(slice)?)),
            _tag => Err(Error::InvalidData),
        }
    }
}

/// External message
#[derive(Clone, Debug, Eq, PartialEq, Store, Load)]
pub struct OutMsgExternal {
    /// message cell
    pub msg: Cell,
    /// transaction
    pub transaction: Lazy<Transaction>,
}

impl OutMsgExternal {
    /// create with cells
    pub fn with_cells(msg_cell: Cell, tr_cell: Cell) -> Self {
        OutMsgExternal {
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

    /// Message cell
    pub fn message_cell(&self) -> Cell {
        self.msg.clone()
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

/// Out message Immediate
#[derive(Clone, Debug, Eq, PartialEq, Store, Load)]
pub struct OutMsgImmediate {
    /// out message cell
    pub out_msg: Lazy<MsgEnvelope>,
    /// transaction
    pub transaction: Lazy<Transaction>,
    /// reimport message
    pub reimport: Lazy<InMsg>,
}

impl OutMsgImmediate {
    /// create with cells
    pub fn with_cells(out_msg: Cell, tr_cell: Cell, reimport_msg_cell: Cell) -> OutMsgImmediate {
        OutMsgImmediate {
            out_msg: Lazy::load_from(&mut out_msg.as_slice().unwrap()).unwrap(),
            transaction: Lazy::load_from(&mut tr_cell.as_slice().unwrap()).unwrap(),
            reimport: Lazy::load_from(&mut reimport_msg_cell.as_slice().unwrap()).unwrap(),
        }
    }

    /// Load envelope message
    pub fn load_envelope_message(&self) -> Result<MsgEnvelope, Error> {
        self.out_msg.load()
    }

    /// Out message cell
    pub fn out_message_cell(&self) -> Cell {
        self.out_msg.cell.clone()
    }

    /// Load transaction
    pub fn load_transaction(&self) -> Result<Transaction, Error> {
        self.transaction.load()
    }

    /// Load transaction cell
    pub fn transaction_cell(&self) -> Cell {
        self.transaction.cell.clone()
    }

    /// Load reimport message
    pub fn load_reimport_message(&self) -> Result<InMsg, Error> {
        self.reimport.load()
    }

    /// Reimport message cell
    pub fn reimport_message_cell(&self) -> Cell {
        self.reimport.cell.clone()
    }
}

/// OutMsgNew
#[derive(Clone, Debug, Eq, PartialEq, Store, Load)]
pub struct OutMsgNew {
    /// out message cell
    pub out_msg: Lazy<MsgEnvelope>,
    /// transaction
    pub transaction: Lazy<Transaction>,
}

impl OutMsgNew {
    /// create with cells
    pub fn with_cells(out_msg: Cell, tr_cell: Cell) -> Self {
        OutMsgNew {
            out_msg: Lazy::load_from(&mut out_msg.as_slice().unwrap()).unwrap(),
            transaction: Lazy::load_from(&mut tr_cell.as_slice().unwrap()).unwrap(),
        }
    }

    /// Load envelope message
    pub fn load_envelope_message(&self) -> Result<MsgEnvelope, Error> {
        self.out_msg.load()
    }

    /// Out message cell
    pub fn out_message_cell(&self) -> Cell {
        self.out_msg.cell.clone()
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

/// OutMsgDequeueImmediate
#[derive(Clone, Debug, Eq, PartialEq, Store, Load)]
pub struct OutMsgDequeueImmediate {
    /// Out message
    pub out_msg: Lazy<MsgEnvelope>,
    /// reimport message
    pub reimport: Lazy<InMsg>,
}

impl OutMsgDequeueImmediate {
    /// create with cells
    pub fn with_cells(out_msg: Cell, reimport_msg_cell: Cell) -> Self {
        OutMsgDequeueImmediate {
            out_msg: Lazy::load_from(&mut out_msg.as_slice().unwrap()).unwrap(),
            reimport: Lazy::load_from(&mut reimport_msg_cell.as_slice().unwrap()).unwrap(),
        }
    }

    /// Load envelope message
    pub fn load_envelope_message(&self) -> Result<MsgEnvelope, Error> {
        self.out_msg.load()
    }

    /// Out message cell
    pub fn out_message_cell(&self) -> Cell {
        self.out_msg.cell.clone()
    }

    /// Load reimport message
    pub fn load_reimport_message(&self) -> Result<InMsg, Error> {
        self.reimport.load()
    }

    /// Reimport message cell
    pub fn reimport_message_cell(&self) -> Cell {
        self.reimport.cell.clone()
    }
}

/// OutMsgDequeueShort
#[derive(Clone, Debug, Default, Eq, PartialEq, Store, Load)]
pub struct OutMsgDequeueShort {
    /// Msg env hash
    pub msg_env_hash: HashBytes,
    /// Next workchain
    pub next_workchain: i8,
    /// Next addr pfx
    pub next_addr_pfx: u64,
    /// Import block lt
    pub import_block_lt: u64,
}
