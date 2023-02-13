//! Message models.

use everscale_types_proc::*;

use crate::cell::*;
use crate::dict::{self, Dict};
use crate::error::*;
use crate::num::*;
use crate::util::*;

use crate::models::account::AccountStatus;
use crate::models::currency::CurrencyCollection;
use crate::models::message::Message;
use crate::models::Lazy;

pub use self::phases::*;

mod phases;

/// Blockchain transaction.
#[derive(CustomDebug, CustomClone, CustomEq)]
pub struct Transaction<C: CellFamily> {
    /// Account on which this transaction was produced.
    #[debug(with = "DisplayHash")]
    pub account: CellHash,
    /// Logical time when the transaction was created.
    pub lt: u64,
    /// The hash of the previous transaction on the same account.
    #[debug(with = "DisplayHash")]
    pub prev_trans_hash: CellHash,
    /// The logical time of the previous transaction on the same account.
    pub prev_trans_lt: u64,
    /// Unix timestamp when the transaction was created.
    pub now: u32,
    /// The number of outgoing messages.
    pub out_msg_count: Uint15,
    /// Account status before this transaction.
    pub orig_status: AccountStatus,
    /// Account status after this transaction.
    pub end_status: AccountStatus,
    /// Optional incoming message.
    pub in_msg: Option<CellContainer<C>>,
    /// Outgoing messages.
    pub out_msgs: Dict<C, Uint15, CellContainer<C>>,
    /// Total transaction fees (including extra fwd fees).
    pub total_fees: CurrencyCollection<C>,
    /// Account state hashes.
    pub state_update: Lazy<C, HashUpdate>,
    /// Detailed transaction info.
    pub info: Lazy<C, TxInfo<C>>,
}

impl<C: CellFamily> Transaction<C> {
    /// Tries to load the incoming message, if present.
    pub fn load_in_msg(&self) -> Result<Option<Message<'_, C>>, Error> {
        match &self.in_msg {
            Some(in_msg) => match Message::<C>::load_from(&mut in_msg.as_ref().as_slice()) {
                Some(message) => Ok(Some(message)),
                None => Err(Error::CellUnderflow),
            },
            None => Ok(None),
        }
    }

    /// Tries to load the detailed transaction info from the lazy cell.
    pub fn load_info(&self) -> Option<TxInfo<C>> {
        self.info.load()
    }
}

impl<C> Transaction<C>
where
    for<'c> C: CellFamily + 'c,
{
    /// Gets an iterator over the output messages of this transaction, in order by lt.
    /// The iterator element type is `Result<Message<'a, C>>`.
    ///
    /// If the dictionary or message is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn iter_out_msgs(&'_ self) -> TxOutMsgIter<'_, C> {
        TxOutMsgIter {
            inner: self.out_msgs.raw_values(),
        }
    }
}

/// An iterator over the transaction output messages.
///
/// This struct is created by the [`iter_out_msgs`] method on [`Transaction`].
/// See its documentation for more.
///
/// [`iter_out_msgs`]: Transaction::iter_out_msgs
#[derive(CustomClone)]
pub struct TxOutMsgIter<'a, C: CellFamily> {
    inner: dict::RawValues<'a, C>,
}

impl<'a, C: CellFamily + 'a> Iterator for TxOutMsgIter<'a, C>
where
    for<'c> C: CellFamily + 'c,
{
    type Item = Result<Message<'a, C>, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next()? {
            Ok(mut value) => {
                if let Some(value) = value.load_reference() {
                    if let Some(message) = Message::<'a, C>::load_from(&mut value.as_slice()) {
                        return Some(Ok(message));
                    }
                }
                Some(Err(self.inner.finish(Error::CellUnderflow)))
            }
            Err(e) => Some(Err(e)),
        }
    }
}

impl<C: CellFamily> Transaction<C> {
    const TAG: u8 = 0b0111;
}

impl<C: CellFamily> Store<C> for Transaction<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        let messages = {
            let mut builder = CellBuilder::<C>::new();
            if self.in_msg.store_into(&mut builder, finalizer)
                && self.out_msgs.store_into(&mut builder, finalizer)
            {
                match builder.build_ext(finalizer) {
                    Some(cell) => cell,
                    None => return false,
                }
            } else {
                return false;
            }
        };

        builder.store_small_uint(Self::TAG, 4)
            && builder.store_u256(&self.account)
            && builder.store_u64(self.lt)
            && builder.store_u256(&self.prev_trans_hash)
            && builder.store_u64(self.prev_trans_lt)
            && builder.store_u32(self.now)
            && self.out_msg_count.store_into(builder, finalizer)
            && self.orig_status.store_into(builder, finalizer)
            && self.end_status.store_into(builder, finalizer)
            && builder.store_reference(messages)
            && self.total_fees.store_into(builder, finalizer)
            && self.state_update.store_into(builder, finalizer)
            && self.info.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for Transaction<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if slice.load_small_uint(4)? != Self::TAG {
            return None;
        }

        let (in_msg, out_msgs) = {
            let slice = &mut slice.load_reference()?.as_slice();
            let in_msg = Option::<CellContainer<C>>::load_from(slice)?;
            let out_msgs = Dict::load_from(slice)?;
            (in_msg, out_msgs)
        };

        Some(Self {
            account: slice.load_u256()?,
            lt: slice.load_u64()?,
            prev_trans_hash: slice.load_u256()?,
            prev_trans_lt: slice.load_u64()?,
            now: slice.load_u32()?,
            out_msg_count: Uint15::load_from(slice)?,
            orig_status: AccountStatus::load_from(slice)?,
            end_status: AccountStatus::load_from(slice)?,
            in_msg,
            out_msgs,
            total_fees: CurrencyCollection::<C>::load_from(slice)?,
            state_update: Lazy::<C, HashUpdate>::load_from(slice)?,
            info: Lazy::<C, TxInfo<C>>::load_from(slice)?,
        })
    }
}

/// Detailed transaction info.
#[derive(CustomDebug, CustomClone, CustomEq)]
pub enum TxInfo<C: CellFamily> {
    /// Ordinary transaction info.
    Ordinary(OrdinaryTxInfo<C>),
    /// Tick-tock transaction info.
    TickTock(TickTockTxInfo),
}

impl<C: CellFamily> Store<C> for TxInfo<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        match self {
            Self::Ordinary(info) => {
                builder.store_small_uint(0b0000, 4) && info.store_into(builder, finalizer)
            }
            Self::TickTock(info) => {
                builder.store_small_uint(0b001, 3) && info.store_into(builder, finalizer)
            }
        }
    }
}

impl<'a, C: CellFamily> Load<'a, C> for TxInfo<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let tag_part = slice.load_small_uint(3)?;
        Some(if tag_part == 0b001 {
            Self::TickTock(TickTockTxInfo::load_from(slice)?)
        } else if tag_part == 0b000 && !slice.load_bit()? {
            Self::Ordinary(OrdinaryTxInfo::<C>::load_from(slice)?)
        } else {
            return None;
        })
    }
}

/// Ordinary transaction info.
#[derive(CustomDebug, CustomClone, CustomEq)]
pub struct OrdinaryTxInfo<C: CellFamily> {
    /// Whether the credit phase was executed first
    /// (usually set when incoming message has `bounce: false`).
    pub credit_first: bool,
    /// Storage phase info.
    ///
    /// Skipped if the account did not exist prior to execution.
    pub storage_phase: Option<StoragePhase>,
    /// Credit phase info.
    ///
    /// Skipped if the incoming message is external.
    pub credit_phase: Option<CreditPhase<C>>,
    /// Compute phase info.
    pub compute_phase: ComputePhase,
    /// Action phase info.
    ///
    /// Skipped if the transaction was aborted at the compute phase.
    pub action_phase: Option<ActionPhase>,
    /// Whether the transaction was reverted.
    pub aborted: bool,
    /// Bounce phase info.
    ///
    /// Only present if the incoming message had `bounce: true` and
    /// the compute phase failed.
    pub bounce_phase: Option<BouncePhase>,
    /// Whether the account was destroyed during this transaction.
    pub destroyed: bool,
}

impl<C: CellFamily> Store<C> for OrdinaryTxInfo<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        let action_phase = match &self.action_phase {
            Some(action_phase) => {
                let mut builder = CellBuilder::<C>::new();
                if !action_phase.store_into(&mut builder, finalizer) {
                    return false;
                }
                match builder.build_ext(finalizer) {
                    Some(cell) => Some(cell),
                    None => return false,
                }
            }
            None => None,
        };

        builder.store_bit(self.credit_first)
            && self.storage_phase.store_into(builder, finalizer)
            && self.credit_phase.store_into(builder, finalizer)
            && self.compute_phase.store_into(builder, finalizer)
            && action_phase.store_into(builder, finalizer)
            && builder.store_bit(self.aborted)
            && self.bounce_phase.store_into(builder, finalizer)
            && builder.store_bit(self.destroyed)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for OrdinaryTxInfo<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            credit_first: slice.load_bit()?,
            storage_phase: Option::<StoragePhase>::load_from(slice)?,
            credit_phase: Option::<CreditPhase<C>>::load_from(slice)?,
            compute_phase: ComputePhase::load_from(slice)?,
            action_phase: match Option::<CellContainer<C>>::load_from(slice)? {
                Some(cell) => Some(ActionPhase::load_from(&mut cell.as_ref().as_slice())?),
                None => None,
            },
            aborted: slice.load_bit()?,
            bounce_phase: Option::<BouncePhase>::load_from(slice)?,
            destroyed: slice.load_bit()?,
        })
    }
}

/// Tick-tock transaction info.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TickTockTxInfo {
    /// Tick-tock transaction execution edge.
    pub kind: TickTock,
    /// Storage phase info.
    pub storage_phase: StoragePhase,
    /// Compute phase info.
    pub compute_phase: ComputePhase,
    /// Action phase info.
    ///
    /// Skipped if the transaction was aborted at the compute phase.
    pub action_phase: Option<ActionPhase>,
    /// Whether the transaction was reverted.
    pub aborted: bool,
    /// Whether the account was destroyed during this transaction.
    pub destroyed: bool,
}

impl<C: CellFamily> Store<C> for TickTockTxInfo {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        let action_phase = match &self.action_phase {
            Some(action_phase) => {
                let mut builder = CellBuilder::<C>::new();
                if !action_phase.store_into(&mut builder, finalizer) {
                    return false;
                }
                match builder.build_ext(finalizer) {
                    Some(cell) => Some(cell),
                    None => return false,
                }
            }
            None => None,
        };

        let flags = ((self.aborted as u8) << 1) | (self.destroyed as u8);

        self.kind.store_into(builder, finalizer)
            && self.storage_phase.store_into(builder, finalizer)
            && self.compute_phase.store_into(builder, finalizer)
            && action_phase.store_into(builder, finalizer)
            && builder.store_small_uint(flags, 2)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for TickTockTxInfo {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let kind = TickTock::load_from(slice)?;
        let storage_phase = StoragePhase::load_from(slice)?;
        let compute_phase = ComputePhase::load_from(slice)?;
        let action_phase = match Option::<CellContainer<C>>::load_from(slice)? {
            Some(cell) => Some(ActionPhase::load_from(&mut cell.as_ref().as_slice())?),
            None => None,
        };
        let flags = slice.load_small_uint(2)?;

        Some(Self {
            kind,
            storage_phase,
            compute_phase,
            action_phase,
            aborted: flags & 0b10 != 0,
            destroyed: flags & 0b01 != 0,
        })
    }
}

/// Tick-tock transaction execution edge.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TickTock {
    /// Start of the block.
    Tick = 0,
    /// End of the block.
    Tock = 1,
}

impl<C: CellFamily> Store<C> for TickTock {
    #[inline]
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        builder.store_bit(*self == Self::Tock)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for TickTock {
    #[inline]
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(if slice.load_bit()? {
            Self::Tock
        } else {
            Self::Tick
        })
    }
}

/// Account state hash update.
#[derive(CustomDebug, Clone, Copy, Eq, PartialEq)]
pub struct HashUpdate {
    /// Old account state hash.
    #[debug(with = "DisplayHash")]
    pub old: CellHash,
    /// New account state hash.
    #[debug(with = "DisplayHash")]
    pub new: CellHash,
}

impl HashUpdate {
    /// The number of data bits that this struct occupies.
    pub const BITS: u16 = 8 + 256 + 256;

    /// update_hashes#72
    const TAG: u8 = 0x72;
}

impl<C: CellFamily> Store<C> for HashUpdate {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        builder.has_capacity(Self::BITS, 0)
            && builder.store_u8(Self::TAG)
            && builder.store_u256(&self.old)
            && builder.store_u256(&self.new)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for HashUpdate {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if unlikely(!slice.has_remaining(Self::BITS, 0)) {
            return None;
        }

        if slice.load_u8()? != Self::TAG {
            return None;
        }

        Some(Self {
            old: slice.load_u256()?,
            new: slice.load_u256()?,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::{RcBoc, RcCell, RcCellBuilder, RcCellFamily};

    use super::*;

    fn serialize_tx(tx: Transaction<RcCellFamily>) -> RcCell {
        let mut builder = RcCellBuilder::new();
        assert!(tx.store_into(&mut builder, &mut RcCellFamily::default_finalizer()));
        builder.build().unwrap()
    }

    fn check_tx(boc: &str) -> RcCell {
        let boc = RcBoc::decode_base64(boc).unwrap();
        let tx = Transaction::load_from(&mut boc.as_slice()).unwrap();
        println!("tx: {tx:#?}");

        let in_msg = tx.load_in_msg().unwrap();
        println!("In message: {in_msg:?}");

        for (i, entry) in tx.out_msgs.iter().enumerate() {
            let (number, cell) = entry.unwrap();
            let message = Message::load_from(&mut cell.as_slice()).unwrap();
            assert_eq!(number, i as u16);
            println!("Out message: {i}, message: {message:?}");
        }
        assert_eq!(
            tx.out_msg_count.into_inner() as usize,
            tx.out_msgs.raw_values().count()
        );

        let mut out_msg_count = 0;
        for msg in tx.iter_out_msgs() {
            msg.unwrap();
            out_msg_count += 1;
        }
        assert_eq!(out_msg_count, tx.out_msg_count);

        let info = tx.load_info().unwrap();
        println!("info: {info:#?}");

        let serialized = serialize_tx(tx);
        assert_eq!(serialized.as_ref(), boc.as_ref());
        serialized
    }

    #[test]
    fn ordinary_tx_without_outgoing() {
        check_tx("te6ccgECCgEAAiQAA7V2SOift2eyC7fBlt0WiLN/0hA462V/fPMQ8oEsnBB3G7AAAfY9R6LMZN1w7hT1VtMZQ34vff1IakzKvRM4657r3GeupIvoJIpQAAH2PT8NiIY8hJ2wABRl0zgoBQQBAhcEREkBdGUCGGXTNhEDAgBbwAAAAAAAAAAAAAAAAS1FLaRJ5QuM990nhh8UYSKv4bVGu4tw/IIW8MYUE5+OBACeQX3MBfVUAAAAAAAAAABSAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACCck/lB91WD5Bky9xy1ywXY/bG7iqNzr+1DG27jQVp5OUxkl947E8nAzF+NHA+zqGpqCuZL3eq9YgWEJBLelAikwoBAaAGAbFoAYPlFQowDFvzLx17ZmWrhW1pi0YpTuBN6LYhOh6J98IfABkjon7dnsgu3wZbdFoizf9IQOOtlf3zzEPKBLJwQdxu0BdGUCAGMGa6AAA+x6j0WYjHkJO2wAcBSwAAAAtACVRPdAch0GHCu0sq7u4086DOMvZRilq2LylASpak+6fYCAGjgAvHaUKSILpcQdjjdbO/WOS2BHQw8Rn8vBldFsPGUGfY4AAAAAAAAAAAAAAAAAdlcwAAAAAAAAAAAAAAAAAAAAAgAAAAAAAAAAAAAAAAB19IkAkAIAAAAAAAAAAAAAAAAAA6+kQ=");
    }

    #[test]
    fn ordinary_tx_with_outgoing() {
        check_tx("te6ccgECGgEABPQAA7d9z+fCq1SjdzIW3cWMo/2pYrA4pkV/IS8ngy0EVS/oG5AAAfax/zS4OpRftPiDkS8YMj1KWTiQwQSYK7NlTiRqhW4I9QG+p38AAAH2sEpsUDY8me7AAJaARP9tSAUEAQIbBIjbiSysaa4YgEBlWhMDAgBv3NuB/iZJWlgAAAAAAAQAAAAAAAQBHCsIhRCq5P8FMG8flwwgRNH2WhuPUG/uZDiNwGJxGSFIVP4AnlB8TD0JAAAAAAAAAAADTQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgnLZb3+dbs+xByMvmHutLzN3GyE8lMcQeTvr3SCQc3ScC5CuyJZa+rsW68PLm0COuucbYY14eIvIDQmENZPKyY2kAgHgFwYCAdsPBwIBIAoIAQEgCQCxSAG5/PhVapRu5kLbuLGUf7UsVgcUyK/kJeTwZaCKpf0DcwAjvLvDBBHD2FKY9lF2tlW2KfekP/IutbAthrLnsm7NJJB9QV1IBhRYYAAAPtY/5pcOx5M92EABASALAbFoAbn8+FVqlG7mQtu4sZR/tSxWBxTIr+Ql5PBloIql/QNzAB5aJdM28ct7yt8uYEgbborLmhcxBQFKEZnnpDch5N3r0BdGUCAGMGa6AAA+1j/mlwzHkz3YwAwBSwAAAAxABeO0oUkQXS4g7HG62d+sclsCOhh4jP5eDK6LYeMoM+x4DQGjgBHlfKxhXeft5K5sKDIIOm/wpEkrIrCamVABvEzcpCOfYAAAAAAAAAAAAAAAAF4N1iAAAAAAAAAAAAAAAAAAAAAgAAAAAAAAAAAAArefTpzAEA4AIAAAAAAAAAAAAAAAAAAAAAACASAUEAEBIBEBs2gBufz4VWqUbuZC27ixlH+1LFYHFMiv5CXk8GWgiqX9A3MANSuO7zsQ3zhNZmTONopY8im0iF8AkI6GP8iVZHBTWkAUBD3i/+AGNFPwAAA+1j/mlwrHkz3YwBIB0AAAASwAAABqAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAC8G6xAAAAAAAAAAAAAAAAAAAAAQD6URtVYTw4eBTWuXZchYWswosdVGZn3Ylvat6GUWKKEwCHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEHh/KJtPYiKAHHeP+Pt9pjQLZJg34+cx3nVl6KuuadUFZSDUopwW3S1hIkgBASAVAbFoAbn8+FVqlG7mQtu4sZR/tSxWBxTIr+Ql5PBloIql/QNzADUrju87EN84TWZkzjaKWPIptIhfAJCOhj/IlWRwU1pAEF8RKIAGGaKOAAA+1j/mlwjHkz3YwBYAKAAAABIAAAAAAAAAP/0O2lP7jIWgAbFoAalcd3nYhvnCazMmcbRSx5FNpEL4BIR0Mf5EqyOCmtIBADc/nwqtUo3cyFt3FjKP9qWKwOKZFfyEvJ4MtBFUv6BuUsrGmuAGKPR2AAA+1j/mlwTHkz3YwBgBiwAAAM1ACr7GCbsSjAfOP/evdEGNiCizc88BZrZyQlXjm8okJa7wD6URtVYTw4eBTWuXZchYWswosdVGZn3Ylvat6GUWKKgZAEGAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIPD+UTaexEUA=");
    }

    #[test]
    fn ordinary_tx_with_external() {
        check_tx("te6ccgECEAEABCwAA7d/+1dDaSA3L2uibiQKv/JnIaNNn9WJtYieOs24uU8oUyAAARC3HEQsF4sbMIVMw2GJZ6YXtDxBuuUMHi11U9pKdB3vZW20NyawAAEQtwCcGBYUWY9AADSAMRKM6AUEAQIPDFnGHvr8xEADAgBvyaoTfE1Qm+AAAAAAAAIAAAAAAAK4sbHPs40L/+ZOYZTx8kBg3rDrUQKTevced6g9zSjJoEHQjiwAnUcl4xOIAAAAAAAAAABNwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACAAgnJJi+OXTuW6+ukeF09C5U7aOyCCB2vTGGfIBMpUz1N36QkaLDsxwWPePHHr9YTX1v135KTbkfOo5mdye6UVZ0BdAgHgCgYBAd8HAZ/gB/2robSQG5e10TcSBV/5M5DRps/qxNrETx1m3FynlCmTAIviBVbU9tFL6ORp6Y+Q3g5gYbQ8ZrQIVg/sKlYsewVEAAARC3HEQsJhRZj0YAgBdnfSJj9hRZj0ABIAYUWYtGFFmPQAAAAXSHboABUxNjMxOTE4NzQ1NTY4AAAAAAAAAAAAAAAAAAAAAAAACQFDgAY9rky4OsV5MdwUCx+JS2GQSGNJFcUhkbPBdDzyiZIMEAwBRYgB/2robSQG5e10TcSBV/5M5DRps/qxNrETx1m3FynlCmQMCwHhoZC88bv/ZdGKH/CXOHkHxWN5IyQlL5eBgvUZlCXejnT+k2B0aVKhFWtkDByRuBjlhyZMEngedFiTBMk/FS//AkgwHXhXMBNEwUCGrfyLQvMIa7ago3bhFgPvpwjzuUIpQAAAXv33KOMYUaDHWnklGGAMAf57Im5vbmNlIjoiYWM1ZmE2MDAxYzVhNjJiOTBlMzI5ZThmNTIyZmQwZGY2M2ZmMTA5MWY1ODcxMjYzIiwiYmFzZTY0IjoiUHZlc1BWRHo2ckFhQlpvd1Nkekp1ZTZoQVAvUkxwclJBcVR0eFpoSENWV0ZPRFgrR0NlcndKQ0VMDQH+eG82R1pGaHlJR29DK3lJaHlvelVRem9aYlcyTHk3QWxxTGtOc1JNRFlhZWFDZENPa043V0hmV2l6ZVJyMU02VklKSERXTXJjTktoeFdUSnl1eUNQUTlueEZSaEt0QmJ6aWE1Y3pnTVdHbDVGcEtwZGFSKzMvbmxSTUZFSFBLUA4B/mZwTi9RbXNPSEFjWmM0QnQ4QXM0VTBVdlNBRW1GRFJTK3UyNTV1elR3NW0vNHhING5sZ2NySTZWWVFicU93PT0iLCJwdWJfa2V5IjoiMjkwNGEwN2MzNTljMzE3YWQzNDMwMWU4MjVmNjE4NGIyOWYxNGI1YzZiNzMzMTU1ZTAPACBhZWI2MmI4YmZiZWUwNCJ9");
    }

    #[test]
    fn ordinary_bounce() {
        // Ok, no state
        check_tx("te6ccgECCAEAAdkAA7V1mlCYYM8b7NOFt7rztgCKPqqX5CQlGJJYLGKJ2Xtj2BAAAfayVBU8wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAY8mf7wAD5gosIIAwIBAB8ECRj/+U1BwDBRYQMKLDBAAIJykK7Illr6uxbrw8ubQI665xthjXh4i8gNCYQ1k8rJjaSQrsiWWvq7FuvDy5tAjrrnG2GNeHiLyA0JhDWTysmNpAIB4AYEAQHfBQD5WACzShMMGeN9mnC29152wBFH1VL8hISjEksFjFE7L2x7AwAZ1ptY/J+PyTUHShgQ6koay4+trhPpMMwjMKDPvb1TWhGPwovUBhRYYAAAPtZKgqeax5M/3n////+BdwdxAAAAwuXMTVMAAAAAAAAAAAAAAIuyyXAAQAjiWEABsWgAzrTax+T8fkmoOlDAh1JQ1lx9bXCfSYZhGYUGfe3qmtEAFmlCYYM8b7NOFt7rztgCKPqqX5CQlGJJYLGKJ2Xtj2BRj/+U1AYgXoYAAD7WSoKnlseTP97ABwB7Au4O4gAAAYXLmJqmAAAAAAAAAAAAAAEXZZLgAIARxLDMBKJ9M0q/RXwQrCjTj5yjT6tEsu6rHO/eV5Jw9pA=");

        // NoFunds
        check_tx("te6ccgECBgEAAXEAA7d0XhMZi+e9SzhsQrBsY7gPnCKq299VsH5C63y8SRRRpMAAAaVqFwSIZbzAOEp/YjBJHOmFMdmJVZSnJ7/WUho73oMUXVuJHV0AAAGlahcEiEYuFylAABSFiSrsCAQDAQEhBAkLElbR0IWJKuwNAMPQkBACAKhhasuMLVlwAf///+UAC2QDAAAO8wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgnKWgrG3bY1QSltXmrTHAt5/OnOO6mlvzVOT3CgQ6A5fKlEFVtRu1kb0kWrMbHz20Ag4AZKdZI9LU9YcapS6G7paAQGgBQC5aACLwmMxfPepZw2IVg2MdwHzhFVbe+q2D8hdb5eJIoo0mQAReExmL571LOGxCsGxjuA+cIqrb31WwfkLrfLxJFFGkxCxJW0cBhRYYAAANK1C4JEKxcLlKAVRhK5A");
    }

    #[test]
    fn tick_tock_tx() {
        // Tock
        check_tx("te6ccgECBgEAASwAA691VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVAAAfax88MIPSw0moITCuvilvszvMTwjAWqBNl6BXOXvVmKdtxaKU8AAAH2sfLO5DY8meygABQIBQQBAgUwMCQDAgBbwAAAAAAAAAAAAAAAAS1FLaRJ5QuM990nhh8UYSKv4bVGu4tw/IIW8MYUE5+OBACgQVxQF9eEAAAAAAAAAAAAQgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgnImgq+NHcQq6sTadKlyN/JVsIjCmWhcl81ZK/uRSGSbXHd22xrbnN+GPXJpoXBZ6pxl7sArfWoZr5BuYa29vanoAAEg");

        // Tick
        check_tx("te6ccgECBgEAASwAA69zMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzAAAfax88MIGhxBVccog1yEGiaTdf1fIS97n6H7Nx0kV91X6d2gb3JgAAH2sfLO5CY8meygABQIBQQBAgUgMCQDAgBbwAAAAAAAAAAAAAAAAS1FLaRJ5QuM990nhh8UYSKv4bVGu4tw/IIW8MYUE5+OBACgQsMQF9eEAAAAAAAAAAAAiAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgnKdvt2OBw9r4/ZICoIsb9ckq/90a1fWXhthgXldZUG1cEPP/jeD7UbLLMewICVZHh9eY00PRU4gZB47Vtmn9I7zAAEg");
    }
}
