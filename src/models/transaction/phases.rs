use everscale_types_proc::*;

use crate::cell::*;
use crate::num::*;
use crate::util::DisplayHash;

use crate::models::account::StorageUsedShort;
use crate::models::currency::CurrencyCollection;

/// Storage phase info.
///
/// At this phase account pays for storing its state.
#[derive(Debug, Clone, Eq, PartialEq, Load)]
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

/// Credit phase info.
///
/// At this phase message balance is added to the account balance.
#[derive(CustomDebug, CustomClone, CustomEq, Load)]
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
#[derive(CustomDebug, Clone, Eq, PartialEq)]
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
    #[debug(with = "DisplayHash")]
    pub vm_init_state_hash: CellHash,
    /// Hash of the VM state after executing this phase.
    #[debug(with = "DisplayHash")]
    pub vm_final_state_hash: CellHash,
}

/// Skipped compute phase info.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Load)]
pub struct SkippedComputePhase {
    /// The reason this step was skipped.
    pub reason: ComputePhaseSkipReason,
}

impl<C: CellFamily> Store<C> for SkippedComputePhase {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.reason.store_into(builder, finalizer)
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
#[derive(CustomDebug, Clone, Eq, PartialEq)]
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
    #[debug(with = "DisplayHash")]
    pub action_list_hash: CellHash,
    /// The total number of unique cells (bits / refs) of produced messages.
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
#[derive(Debug, Clone, Eq, PartialEq, Load)]
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

/// Executed bounce phase info.
#[derive(Debug, Clone, Eq, PartialEq, Load)]
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
