//! Message models.

use crate::cell::*;
use crate::num::*;
use crate::util::{unlikely, DisplayHash};

use super::account::*;
use super::message::*;
use super::Lazy;

/// Blockchain transaction.
#[derive(Clone, Eq, PartialEq)]
pub struct Transaction<'a, C: CellFamily> {
    /// Account on which this transaction was produced.
    pub account: CellHash,
    /// Logical time when the transaction was created.
    pub lt: u64,
    /// The hash of the previous transaction on the same account.
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
    pub in_msg: Option<Lazy<C, Message<'a, C>>>,
    /// Outgoing messages.
    pub out_msgs: Option<CellContainer<C>>,
    /// Total transaction fees (including extra fwd fees).
    pub total_fees: CurrencyCollection<C>,
    /// Account state hashes.
    pub state_update: Lazy<C, HashUpdate>,
    /// Detailed transaction info.
    pub info: Lazy<C, TxInfo<C>>,
}

impl<'a, C: CellFamily> Transaction<'a, C> {
    /// Tries to load the detailed transaction info from the lazy cell.
    pub fn load_info(&self) -> Option<TxInfo<C>> {
        self.info.load()
    }
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
    const TAG: u8 = 0b0111;
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

/// Detailed transaction info.
#[derive(Debug, Clone, Eq, PartialEq)]
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
#[derive(Debug, Clone, Eq, PartialEq)]
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

/// Storage phase info.
///
/// At this phase account pays for storing its state.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct StoragePhase {
    /// Amount of tokens collected for storing this contract for some time.
    pub storage_fees_collected: Tokens,
    /// Amount of tokens which this account owes to the network
    /// (if there was not enough balance to pay storage fee).
    pub storage_fees_due: Option<Tokens>,
    /// Account status change during execution of this phase.
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

/// Credit phase info.
///
/// At this phase message balance is added to the account balance.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct CreditPhase<C: CellFamily> {
    /// Amount of tokens paid for the debt.
    pub due_fees_collected: Option<Tokens>,
    /// Amount of tokens added to the account balance from the remaining
    /// message balance.
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

/// Compute phase info.
///
/// At this phase the VM is executed to produce a list of actions.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ComputePhase {
    /// Compute phase was skipped.
    Skipped(SkippedComputePhase),
    /// Compute phase was executed.
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
        let gas_fees = Tokens::load_from(slice)?;

        let slice = &mut slice.load_reference()?.as_slice();
        Some(Self::Executed(ExecutedComputePhase {
            success: flags & 0b100 != 0,
            msg_state_used: flags & 0b010 != 0,
            account_activated: flags & 0b001 != 0,
            gas_fees,
            gas_used: VarUint56::load_from(slice)?,
            gas_limit: VarUint56::load_from(slice)?,
            gas_credit: Option::<VarUint24>::load_from(slice)?,
            mode: slice.load_u8()? as i8,
            exit_code: slice.load_u32()? as i32,
            exit_arg: Option::<i32>::load_from(slice)?,
            vm_steps: slice.load_u32()?,
            vm_init_state_hash: slice.load_u256()?,
            vm_final_state_hash: slice.load_u256()?,
        }))
    }
}

/// Executed compute phase info.
#[derive(Clone, Eq, PartialEq)]
pub struct ExecutedComputePhase {
    /// Whether the execution was successful.
    pub success: bool,
    /// Whether the `init` from the incoming message was used.
    pub msg_state_used: bool,
    /// Whether the account state changed to `Active` during this phase.
    pub account_activated: bool,
    /// Total amount of tokens spent to execute this phase.
    pub gas_fees: Tokens,
    /// Amount of gas used by the VM to execute this phase.
    pub gas_used: VarUint56,
    /// Max gas amount which could be used.
    pub gas_limit: VarUint56,
    /// Max gas amount which could be used before accepting this transaction.
    pub gas_credit: Option<VarUint24>,
    /// Execution mode.
    pub mode: i8,
    /// VM exit code.
    pub exit_code: i32,
    /// Additional VM exit argument.
    pub exit_arg: Option<i32>,
    /// The number of VM steps it took to complete this phase.
    pub vm_steps: u32,
    /// Hash of the initial state of the VM.
    pub vm_init_state_hash: CellHash,
    /// Hash of the VM state after executing this phase.
    pub vm_final_state_hash: CellHash,
}

impl std::fmt::Debug for ExecutedComputePhase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExecutedComputePhase")
            .field("success", &self.success)
            .field("msg_state_used", &self.msg_state_used)
            .field("account_activated", &self.account_activated)
            .field("gas_fees", &self.gas_fees)
            .field("gas_used", &self.gas_used)
            .field("gas_limit", &self.gas_limit)
            .field("gas_credit", &self.gas_credit)
            .field("mode", &self.mode)
            .field("exit_code", &self.exit_code)
            .field("exit_arg", &self.exit_arg)
            .field("vm_steps", &self.vm_steps)
            .field("vm_init_state_hash", &DisplayHash(&self.vm_init_state_hash))
            .field(
                "vm_final_state_hash",
                &DisplayHash(&self.vm_final_state_hash),
            )
            .finish()
    }
}

/// Skipped compute phase info.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct SkippedComputePhase {
    /// The reason this step was skipped.
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

/// Action phase info.
///
/// At this phase the list of actions from the compute phase
/// is converted into updates and outgoing messages.
#[derive(Clone, Eq, PartialEq)]
pub struct ActionPhase {
    /// Whether the execution was successful.
    pub success: bool,
    /// Whether the action list was valid.
    pub valid: bool,
    /// There were no funds to create an outgoing message.
    pub no_funds: bool,
    /// Account status change during execution of this phase.
    pub status_change: AccountStatusChange,
    /// Total forwarding fee for outgoing messages.
    pub total_fwd_fees: Option<Tokens>,
    /// Total fees for processing all actions.
    pub total_action_fees: Option<Tokens>,
    /// Result code of the phase.
    pub result_code: i32,
    /// Optional result argument of the phase.
    pub result_arg: Option<i32>,
    /// The total number of processed actions.
    pub total_actions: u16,
    /// The number of special actions (`ReserveCurrency`, `SetCode`, `ChangeLibrary`, copyleft).
    pub special_actions: u16,
    /// The number of skipped actions.
    pub skipped_actions: u16,
    /// The number of outgoing messages created by the compute phase.
    pub messages_created: u16,
    /// The hash of the actions list.
    pub action_list_hash: CellHash,
    /// The total number of unique cells (bits / refs) of produced messages.
    pub total_message_size: StorageUsedShort,
}

impl std::fmt::Debug for ActionPhase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ActionPhase")
            .field("success", &self.success)
            .field("valid", &self.valid)
            .field("no_funds", &self.no_funds)
            .field("status_change", &self.status_change)
            .field("total_fwd_fees", &self.total_fwd_fees)
            .field("total_action_fees", &self.total_action_fees)
            .field("result_code", &self.result_code)
            .field("result_arg", &self.result_arg)
            .field("total_actions", &self.total_actions)
            .field("special_actions", &self.special_actions)
            .field("skipped_actions", &self.skipped_actions)
            .field("messages_created", &self.messages_created)
            .field("action_list_hash", &DisplayHash(&self.action_list_hash))
            .field("total_message_size", &self.total_message_size)
            .finish()
    }
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

/// Bounce phase info.
///
/// At this stage some funds are returned back to the sender.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum BouncePhase {
    /// Default phase state.
    ///
    /// Probably unused.
    NegativeFunds,
    /// There were not enough funds to execute this phase.
    NoFunds(NoFundsBouncePhase),
    /// Bounce phase was executed.
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

/// Skipped bounce phase info.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct NoFundsBouncePhase {
    /// The total number of unique cells (bits / refs) of the bounced message.
    pub msg_size: StorageUsedShort,
    /// Required amount of tokens to send the bounced message.
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

/// Executed bounce phase info.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ExecutedBouncePhase {
    /// The total number of unique cells (bits / refs) of the bounced message.
    pub msg_size: StorageUsedShort,
    /// The part of fees which fo to the validators.
    pub msg_fees: Tokens,
    /// Message forwarding fee.
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

/// Account status change during transaction execution.
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
    /// Old account state hash.
    pub old: CellHash,
    /// New account state hash.
    pub new: CellHash,
}

impl HashUpdate {
    /// The number of data bits that this struct occupies.
    pub const BITS: u16 = 8 + 256 + 256;

    /// update_hashes#72
    const TAG: u8 = 0x72;
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
