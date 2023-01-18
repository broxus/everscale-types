//! Message models.

use crate::cell::*;
use crate::num::*;
use crate::util::{unlikely, DisplayHash};

use super::account::*;
use super::message::*;
use super::Lazy;

#[derive(Clone, Eq, PartialEq)]
pub struct Transaction<'a, C: CellFamily> {
    pub account: CellHash,
    pub lt: u64,
    pub prev_trans_hash: CellHash,
    pub prev_trans_lt: u64,
    pub now: u32,
    pub out_msg_count: Uint15,
    pub orig_status: AccountStatus,
    pub end_status: AccountStatus,
    pub in_msg: Option<Lazy<C, Message<'a, C>>>,
    pub out_msgs: Option<CellContainer<C>>,
    pub total_fees: CurrencyCollection<C>,
    pub state_update: Lazy<C, HashUpdate>,
    pub info: Lazy<C, TxInfo<C>>,
}

impl<'a, C: CellFamily> std::fmt::Debug for Transaction<'a, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Transaction")
            .field("account", &DisplayHash(&self.account))
            .field("lt", &self.lt)
            .field("prev_trans_hash", &DisplayHash(&self.prev_trans_hash))
            .field("prev_trans_lt", &self.prev_trans_lt)
            .field("now", &self.now)
            .field("out_msg_count", &self.out_msg_count)
            .field("orig_status", &self.orig_status)
            .field("end_status", &self.end_status)
            .field("in_msg", &self.in_msg)
            .field("out_msgs", &self.out_msgs)
            .field("total_fees", &self.total_fees)
            .field("state_update", &self.state_update)
            .field("info", &self.info)
            .finish()
    }
}

impl<'a, C: CellFamily> Transaction<'a, C> {
    pub const TAG: u8 = 0b0111;
}

impl<'a, C: CellFamily> Store<C> for Transaction<'a, C> {
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

impl<'a, C: CellFamily> Load<'a, C> for Transaction<'a, C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if slice.load_small_uint(4)? != Self::TAG {
            return None;
        }

        let (in_msg, out_msgs) = {
            let slice = &mut slice.load_reference()?.as_slice();
            let in_msg = Option::<Lazy<C, Message<'a, C>>>::load_from(slice)?;
            let out_msgs = Option::<CellContainer<C>>::load_from(slice)?;
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

pub enum TxInfo<C: CellFamily> {
    Ordinary(OrdinaryTxInfo<C>),
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
        } else if tag_part == 0b000 && slice.load_bit()? {
            Self::Ordinary(OrdinaryTxInfo::<C>::load_from(slice)?)
        } else {
            return None;
        })
    }
}

pub struct OrdinaryTxInfo<C: CellFamily> {
    pub credit_first: bool,
    pub storage_phase: Option<StoragePhase>,
    pub credit_phase: Option<CreditPhase<C>>,
    pub compute_phase: ComputePhase,
    pub action_phase: Option<ActionPhase>,
    pub aborted: bool,
    pub bounce_phase: Option<BouncePhase>,
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

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TickTockTxInfo {
    pub kind: TickTock,
    pub storage_phase: StoragePhase,
    pub compute_phase: ComputePhase,
    pub action_phase: Option<ActionPhase>,
    pub aborted: bool,
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
    Tick = 0,
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

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct StoragePhase {
    pub storage_fees_collected: Tokens,
    pub storage_fees_due: Option<Tokens>,
    pub status_change: AccountStatusChange,
}

impl<C: CellFamily> Store<C> for StoragePhase {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.storage_fees_collected.store_into(builder, finalizer)
            && self.storage_fees_due.store_into(builder, finalizer)
            && self.status_change.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for StoragePhase {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            storage_fees_collected: Tokens::load_from(slice)?,
            storage_fees_due: Option::<Tokens>::load_from(slice)?,
            status_change: AccountStatusChange::load_from(slice)?,
        })
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct CreditPhase<C: CellFamily> {
    pub due_fees_collected: Option<Tokens>,
    pub credit: CurrencyCollection<C>,
}

impl<C: CellFamily> Store<C> for CreditPhase<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.due_fees_collected.store_into(builder, finalizer)
            && self.credit.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for CreditPhase<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            due_fees_collected: Option::<Tokens>::load_from(slice)?,
            credit: CurrencyCollection::<C>::load_from(slice)?,
        })
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ComputePhase {
    Skipped(SkippedComputePhase),
    Executed(ExecutedComputePhase),
}

impl<C: CellFamily> Store<C> for ComputePhase {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        match self {
            Self::Skipped(phase) => {
                builder.store_bit_zero() && phase.store_into(builder, finalizer)
            }
            Self::Executed(phase) => {
                let cell = {
                    let mut builder = CellBuilder::<C>::new();
                    if phase.gas_used.store_into(&mut builder, finalizer)
                        && phase.gas_credit.store_into(&mut builder, finalizer)
                        && builder.store_u8(phase.mode as u8)
                        && builder.store_u32(phase.exit_code as u32)
                        && phase.exit_arg.store_into(&mut builder, finalizer)
                        && builder.store_u32(phase.vm_steps)
                        && builder.store_u256(&phase.vm_init_state_hash)
                        && builder.store_u256(&phase.vm_final_state_hash)
                    {
                        match builder.build_ext(finalizer) {
                            Some(cell) => cell,
                            None => return false,
                        }
                    } else {
                        return false;
                    }
                };

                let flags = 0b1000u8
                    | ((phase.success as u8) << 2)
                    | ((phase.msg_state_used as u8) << 1)
                    | (phase.account_activated as u8);
                builder.store_small_uint(flags, 4)
                    && phase.gas_fees.store_into(builder, finalizer)
                    && builder.store_reference(cell)
            }
        }
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ComputePhase {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if !slice.load_bit()? {
            return Some(Self::Skipped(SkippedComputePhase::load_from(slice)?));
        }

        let flags = slice.load_small_uint(3)?;
        let slice = &mut slice.load_reference()?.as_slice();
        Some(Self::Executed(ExecutedComputePhase {
            success: flags & 0b100 != 0,
            msg_state_used: flags & 0b010 != 0,
            account_activated: flags & 0b001 != 0,
            gas_fees: Tokens::load_from(slice)?,
            gas_used: VarUint56::load_from(slice)?,
            gas_limit: VarUint56::load_from(slice)?,
            gas_credit: VarUint56::load_from(slice)?,
            mode: slice.load_u8()? as i8,
            exit_code: slice.load_u32()? as i32,
            exit_arg: Option::<i32>::load_from(slice)?,
            vm_steps: slice.load_u32()?,
            vm_init_state_hash: slice.load_u256()?,
            vm_final_state_hash: slice.load_u256()?,
        }))
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ExecutedComputePhase {
    pub success: bool,
    pub msg_state_used: bool,
    pub account_activated: bool,
    pub gas_fees: Tokens,
    pub gas_used: VarUint56,
    pub gas_limit: VarUint56,
    pub gas_credit: VarUint56,
    pub mode: i8,
    pub exit_code: i32,
    pub exit_arg: Option<i32>,
    pub vm_steps: u32,
    pub vm_init_state_hash: CellHash,
    pub vm_final_state_hash: CellHash,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct SkippedComputePhase {
    pub reason: ComputePhaseSkipReason,
}

impl<C: CellFamily> Store<C> for SkippedComputePhase {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.reason.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for SkippedComputePhase {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            reason: ComputePhaseSkipReason::load_from(slice)?,
        })
    }
}

/// Enum with reasons for skipping compute phase.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ComputePhaseSkipReason {
    /// Contract doesn't have state to execute.
    NoState = 0b00,
    /// Contract state is invalid.
    BadState = 0b01,
    /// Not enough gas to execute compute phase.
    NoGas = 0b10,
}

impl<C: CellFamily> Store<C> for ComputePhaseSkipReason {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        builder.store_small_uint(*self as u8, 2)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ComputePhaseSkipReason {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let ty = slice.load_small_uint(2)?;
        Some(match ty {
            0b00 => Self::NoState,
            0b01 => Self::BadState,
            0b10 => Self::NoGas,
            _ => return None,
        })
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ActionPhase {
    pub success: bool,
    pub valid: bool,
    pub no_funds: bool,
    pub status_change: AccountStatusChange,
    pub total_fwd_fees: Option<Tokens>,
    pub total_action_fees: Option<Tokens>,
    pub result_code: i32,
    pub result_arg: Option<i32>,
    pub total_actions: u16,
    pub special_actions: u16,
    pub skipped_actions: u16,
    pub messages_created: u16,
    pub action_list_hash: CellHash,
    pub total_message_size: StorageUsedShort,
}

impl<C: CellFamily> Store<C> for ActionPhase {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        let flags = ((self.success as u8) << 2) | ((self.valid as u8) << 1) | self.no_funds as u8;
        let counts = ((self.total_actions as u64) << 48)
            | ((self.special_actions as u64) << 32)
            | ((self.skipped_actions as u64) << 16)
            | self.messages_created as u64;

        builder.store_small_uint(flags, 3)
            && self.status_change.store_into(builder, finalizer)
            && self.total_fwd_fees.store_into(builder, finalizer)
            && self.total_action_fees.store_into(builder, finalizer)
            && builder.store_u32(self.result_code as u32)
            && self.result_arg.store_into(builder, finalizer)
            && builder.store_u64(counts)
            && builder.store_u256(&self.action_list_hash)
            && self.total_message_size.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ActionPhase {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let flags = slice.load_small_uint(3)?;

        let status_change = AccountStatusChange::load_from(slice)?;
        let total_fwd_fees = Option::<Tokens>::load_from(slice)?;
        let total_action_fees = Option::<Tokens>::load_from(slice)?;
        let result_code = slice.load_u32()? as i32;
        let result_arg = Option::<i32>::load_from(slice)?;

        let counts = slice.load_u64()?;

        Some(Self {
            success: flags & 0b100 != 0,
            valid: flags & 0b010 != 0,
            no_funds: flags & 0b001 != 0,
            status_change,
            total_fwd_fees,
            total_action_fees,
            result_code,
            result_arg,
            total_actions: (counts >> 48) as u16,
            special_actions: (counts >> 32) as u16,
            skipped_actions: (counts >> 16) as u16,
            messages_created: counts as u16,
            action_list_hash: slice.load_u256()?,
            total_message_size: StorageUsedShort::load_from(slice)?,
        })
    }
}

pub enum BouncePhase {
    NegativeFunds,
    NoFunds(NoFundsBouncePhase),
    Executed(ExecutedBouncePhase),
}

impl<C: CellFamily> Store<C> for BouncePhase {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        match self {
            Self::NegativeFunds => builder.store_small_uint(0b00, 2),
            Self::NoFunds(phase) => {
                builder.store_small_uint(0b01, 2) && phase.store_into(builder, finalizer)
            }
            Self::Executed(phase) => {
                builder.store_bit_one() && phase.store_into(builder, finalizer)
            }
        }
    }
}

impl<'a, C: CellFamily> Load<'a, C> for BouncePhase {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(if slice.load_bit()? {
            Self::Executed(ExecutedBouncePhase::load_from(slice)?)
        } else if slice.load_bit()? {
            Self::NoFunds(NoFundsBouncePhase::load_from(slice)?)
        } else {
            Self::NegativeFunds
        })
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct NoFundsBouncePhase {
    pub msg_size: StorageUsedShort,
    pub req_fwd_fees: Tokens,
}

impl<C: CellFamily> Store<C> for NoFundsBouncePhase {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.msg_size.store_into(builder, finalizer)
            && self.req_fwd_fees.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for NoFundsBouncePhase {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            msg_size: StorageUsedShort::load_from(slice)?,
            req_fwd_fees: Tokens::load_from(slice)?,
        })
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ExecutedBouncePhase {
    pub msg_size: StorageUsedShort,
    pub msg_fees: Tokens,
    pub fwd_fees: Tokens,
}

impl<C: CellFamily> Store<C> for ExecutedBouncePhase {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.msg_size.store_into(builder, finalizer)
            && self.msg_fees.store_into(builder, finalizer)
            && self.fwd_fees.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ExecutedBouncePhase {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            msg_size: StorageUsedShort::load_from(slice)?,
            msg_fees: Tokens::load_from(slice)?,
            fwd_fees: Tokens::load_from(slice)?,
        })
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum AccountStatusChange {
    /// Account status has not changed.
    Unchanged = 0b0,
    /// Account has been frozen.
    Frozen = 0b10,
    /// Account deleted.
    Deleted = 0b11,
}

impl<C: CellFamily> Store<C> for AccountStatusChange {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        if *self == Self::Unchanged {
            builder.store_bit_zero()
        } else {
            builder.store_small_uint(*self as u8, 2)
        }
    }
}

impl<'a, C: CellFamily> Load<'a, C> for AccountStatusChange {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(if !slice.load_bit()? {
            Self::Unchanged
        } else if slice.load_bit()? {
            Self::Deleted
        } else {
            Self::Frozen
        })
    }
}

/// Account state hash update.
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct HashUpdate {
    pub old: CellHash,
    pub new: CellHash,
}

impl HashUpdate {
    /// The number of data bits that this struct occupies.
    pub const BITS: u16 = 8 + 256 + 256;

    /// update_hashes#72
    pub const TAG: u8 = 0x72;
}

impl std::fmt::Debug for HashUpdate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("HashUpdate")
            .field("old", &DisplayHash(&self.old))
            .field("new", &DisplayHash(&self.new))
            .finish()
    }
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
        println!("tx: {:#?}", tx);

        let serialized = serialize_tx(tx);
        serialized
    }

    #[test]
    fn ordinary_tx() {
        check_tx("te6ccgECCgEAAiQAA7V2SOift2eyC7fBlt0WiLN/0hA462V/fPMQ8oEsnBB3G7AAAfY9R6LMZN1w7hT1VtMZQ34vff1IakzKvRM4657r3GeupIvoJIpQAAH2PT8NiIY8hJ2wABRl0zgoBQQBAhcEREkBdGUCGGXTNhEDAgBbwAAAAAAAAAAAAAAAAS1FLaRJ5QuM990nhh8UYSKv4bVGu4tw/IIW8MYUE5+OBACeQX3MBfVUAAAAAAAAAABSAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACCck/lB91WD5Bky9xy1ywXY/bG7iqNzr+1DG27jQVp5OUxkl947E8nAzF+NHA+zqGpqCuZL3eq9YgWEJBLelAikwoBAaAGAbFoAYPlFQowDFvzLx17ZmWrhW1pi0YpTuBN6LYhOh6J98IfABkjon7dnsgu3wZbdFoizf9IQOOtlf3zzEPKBLJwQdxu0BdGUCAGMGa6AAA+x6j0WYjHkJO2wAcBSwAAAAtACVRPdAch0GHCu0sq7u4086DOMvZRilq2LylASpak+6fYCAGjgAvHaUKSILpcQdjjdbO/WOS2BHQw8Rn8vBldFsPGUGfY4AAAAAAAAAAAAAAAAAdlcwAAAAAAAAAAAAAAAAAAAAAgAAAAAAAAAAAAAAAAB19IkAkAIAAAAAAAAAAAAAAAAAA6+kQ=");
    }
}
