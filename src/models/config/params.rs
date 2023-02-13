use std::num::{NonZeroU16, NonZeroU32, NonZeroU8};

use everscale_types_proc::*;

use crate::cell::*;
use crate::dict::Dict;
use crate::num::{Tokens, Uint12};
use crate::util::*;

use crate::models::block::ShardIdent;
use crate::models::Lazy;

/// Config voting setup params.
#[derive(CustomDebug, CustomClone, CustomEq)]
pub struct ConfigVotingSetup<C: CellFamily> {
    /// Proposal configuration for non-critical params.
    pub normal_params: Lazy<C, ConfigProposalSetup>,
    /// Proposal configuration for critical params.
    pub critical_params: Lazy<C, ConfigProposalSetup>,
}

impl<C: CellFamily> ConfigVotingSetup<C> {
    const TAG: u8 = 0x91;
}

impl<C: CellFamily> Store<C> for ConfigVotingSetup<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        builder.store_u8(Self::TAG)
            && self.normal_params.store_into(builder, finalizer)
            && self.critical_params.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ConfigVotingSetup<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if slice.load_u8()? != Self::TAG {
            return None;
        }
        Some(Self {
            normal_params: Lazy::load_from(slice)?,
            critical_params: Lazy::load_from(slice)?,
        })
    }
}

/// Config proposal setup params.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ConfigProposalSetup {
    /// The minimal number of voting rounds for the proposal.
    pub min_total_rounds: u8,
    /// The maximum number of voting rounds for the proposal.
    pub max_total_rounds: u8,
    /// The minimum number of winned voting rounds.
    pub min_wins: u8,
    /// The maximum number of lost voting rounds.
    pub max_losses: u8,
    /// The minimal proposal lifetime duration in seconds.
    pub min_store_sec: u32,
    /// The maximum proposal lifetime duration in seconds.
    pub max_store_sec: u32,
    /// Bit price for storage price computation.
    pub bit_price: u32,
    /// Cell price for storage price computation.
    pub cell_price: u32,
}

impl ConfigProposalSetup {
    const TAG: u8 = 0x36;
}

impl<C: CellFamily> Store<C> for ConfigProposalSetup {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        builder.store_u8(Self::TAG)
            && builder.store_u8(self.min_total_rounds)
            && builder.store_u8(self.max_total_rounds)
            && builder.store_u8(self.min_wins)
            && builder.store_u8(self.max_losses)
            && builder.store_u32(self.min_store_sec)
            && builder.store_u32(self.max_store_sec)
            && builder.store_u32(self.bit_price)
            && builder.store_u32(self.cell_price)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ConfigProposalSetup {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if slice.load_u8()? != Self::TAG {
            return None;
        }
        Some(Self {
            min_total_rounds: slice.load_u8()?,
            max_total_rounds: slice.load_u8()?,
            min_wins: slice.load_u8()?,
            max_losses: slice.load_u8()?,
            min_store_sec: slice.load_u32()?,
            max_store_sec: slice.load_u32()?,
            bit_price: slice.load_u32()?,
            cell_price: slice.load_u32()?,
        })
    }
}

/// Workchain description.
#[derive(CustomDebug, Clone, Eq, PartialEq)]
pub struct WorkchainDescription {
    /// Unix timestamp from which blocks can be produced.
    pub enabled_since: u32,
    /// Unused stub.
    pub actual_min_split: u8,
    /// The minimal shards split depths.
    pub min_split: u8,
    /// The maximum shards split depths.
    pub max_split: u8,
    /// Whether the workchain is enabled.
    pub active: bool,
    /// Whether the workchain accepts messages.
    pub accept_msgs: bool,
    /// A hash of the zerostate root cell.
    #[debug(with = "DisplayHash")]
    pub zerostate_root_hash: CellHash,
    /// A hash of the zerostate file.
    #[debug(with = "DisplayHash")]
    pub zerostate_file_hash: CellHash,
    /// Workchain version.
    pub version: u32,
    /// Workchain format description.
    pub format: WorkchainFormat,
}

impl WorkchainDescription {
    const TAG: u8 = 0xa6;

    /// Returns `true` if the workchain description is valid.
    pub fn is_valid(&self) -> bool {
        self.min_split <= self.max_split
            && self.max_split <= ShardIdent::MAX_SPLIT_DEPTH
            && self.format.is_valid()
    }
}

impl<C: CellFamily> Store<C> for WorkchainDescription {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        let flags: u16 = ((self.format.is_basic() as u16) << 15)
            | ((self.active as u16) << 14)
            | ((self.accept_msgs as u16) << 13);
        self.is_valid()
            && builder.store_u8(Self::TAG)
            && builder.store_u32(self.enabled_since)
            && builder.store_u8(self.actual_min_split)
            && builder.store_u8(self.min_split)
            && builder.store_u8(self.max_split)
            && builder.store_u16(flags)
            && builder.store_u256(&self.zerostate_root_hash)
            && builder.store_u256(&self.zerostate_file_hash)
            && builder.store_u32(self.version)
            && self.format.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for WorkchainDescription {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if slice.load_u8()? != Self::TAG {
            return None;
        }
        let enabled_since = slice.load_u32()?;
        let actual_min_split = slice.load_u8()?;
        let min_split = slice.load_u8()?;
        let max_split = slice.load_u8()?;
        let flags = slice.load_u16()?;
        if flags << 3 != 0 {
            return None;
        }

        let result = Self {
            enabled_since,
            actual_min_split,
            min_split,
            max_split,
            active: flags & 0b0100_0000_0000_0000 != 0,
            accept_msgs: flags & 0b0010_0000_0000_0000 != 0,
            zerostate_root_hash: slice.load_u256()?,
            zerostate_file_hash: slice.load_u256()?,
            version: slice.load_u32()?,
            format: WorkchainFormat::load_from(slice)?,
        };

        let basic = flags & 0b1000_0000_0000_0000 != 0;
        if basic != result.format.is_basic() {
            return None;
        }

        Some(result)
    }
}

/// Workchain format description.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum WorkchainFormat {
    /// Basic workchain format.
    Basic(WorkchainFormatBasic),
    /// Extended workchain format.
    Extended(WorkchainFormatExtended),
}

impl WorkchainFormat {
    /// Returns `true` if the workchain format is valid.
    pub fn is_valid(&self) -> bool {
        match self {
            Self::Basic(_) => true,
            Self::Extended(format) => format.is_valid(),
        }
    }

    /// Returns `true` if the workchain format is [`Basic`].
    ///
    /// [`Basic`]: WorkchainFormatBasic
    pub fn is_basic(&self) -> bool {
        matches!(self, Self::Basic(_))
    }
}

impl<C: CellFamily> Store<C> for WorkchainFormat {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        match self {
            Self::Basic(value) => {
                builder.store_small_uint(0x1, 4) && value.store_into(builder, finalizer)
            }
            Self::Extended(value) => {
                builder.store_small_uint(0x0, 4) && value.store_into(builder, finalizer)
            }
        }
    }
}

impl<'a, C: CellFamily> Load<'a, C> for WorkchainFormat {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(match slice.load_small_uint(4)? {
            0x1 => Self::Basic(WorkchainFormatBasic::load_from(slice)?),
            0x0 => Self::Extended(WorkchainFormatExtended::load_from(slice)?),
            _ => return None,
        })
    }
}

/// Basic workchain format description.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Store, Load)]
pub struct WorkchainFormatBasic {
    /// VM version.
    pub vm_version: i32,
    /// VM mode.
    pub vm_mode: u64,
}

/// Extended workchain format description.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct WorkchainFormatExtended {
    /// The minimal address length in bits.
    pub min_addr_len: Uint12,
    /// The maximal address length in bits.
    pub max_addr_len: Uint12,
    /// Address length step in bits.
    pub addr_len_step: Uint12,
    /// Extended workchain type id.
    pub workchain_type_id: NonZeroU32,
}

impl WorkchainFormatExtended {
    /// Returns `true` if the workchain format is valid.
    pub fn is_valid(&self) -> bool {
        self.min_addr_len >= Uint12::new(64)
            && self.min_addr_len <= self.max_addr_len
            && self.max_addr_len <= Uint12::new(1023)
            && self.addr_len_step <= Uint12::new(1023)
    }
}

impl<C: CellFamily> Store<C> for WorkchainFormatExtended {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.is_valid()
            && self.min_addr_len.store_into(builder, finalizer)
            && self.max_addr_len.store_into(builder, finalizer)
            && self.addr_len_step.store_into(builder, finalizer)
            && builder.store_u32(self.workchain_type_id.get())
    }
}

impl<'a, C: CellFamily> Load<'a, C> for WorkchainFormatExtended {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let result = Self {
            min_addr_len: Uint12::load_from(slice)?,
            max_addr_len: Uint12::load_from(slice)?,
            addr_len_step: Uint12::load_from(slice)?,
            workchain_type_id: NonZeroU32::load_from(slice)?,
        };
        result.is_valid().then_some(result)
    }
}

/// Block creation reward.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct BlockCreationRewards {
    /// Reward for each created masterchain block.
    pub masterchain_block_fee: Tokens,
    /// Base reward for basechain blocks.
    pub basechain_block_fee: Tokens,
}

impl BlockCreationRewards {
    const TAG: u8 = 0x6b;
}

impl<C: CellFamily> Store<C> for BlockCreationRewards {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        builder.store_u8(Self::TAG)
            && self.masterchain_block_fee.store_into(builder, finalizer)
            && self.basechain_block_fee.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for BlockCreationRewards {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if slice.load_u8()? != Self::TAG {
            return None;
        }
        Some(Self {
            masterchain_block_fee: Tokens::load_from(slice)?,
            basechain_block_fee: Tokens::load_from(slice)?,
        })
    }
}

/// Validators election timings.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Store, Load)]
pub struct ElectionTimings {
    /// Validation round length in seconds.
    pub validators_elected_for: u32,
    /// Duration in seconds until the end of the validation round when the election starts.
    pub elections_start_before: u32,
    /// Duration in seconds until the end of the validation round when the election ends.
    pub elections_end_before: u32,
    /// How long validator stake will be frozen after the validation round end.
    pub stake_held_for: u32,
}

/// Range of number of validators.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Store, Load)]
pub struct ValidatorCountParams {
    /// The maximum number of validators.
    pub max_validators: u16,
    /// The maximum number of masterchain validators.
    pub max_main_validators: u16,
    /// The minimum number of validators.
    pub min_validators: u16,
}

/// Validator stake range and factor.
#[derive(Debug, Clone, Eq, PartialEq, Store, Load)]
pub struct ValidatorStakeParams {
    /// The minimum validator stake.
    pub min_stake: Tokens,
    /// The maximum validator stake.
    pub max_stake: Tokens,
    /// The minimum required total stake for elections to be successful.
    pub min_total_stake: Tokens,
    /// Stake constraint (shifted by 16 bits).
    pub max_stake_factor: u32,
}

/// Storage prices for some interval.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct StoragePrices {
    /// Unix timestamp since which this prices are used.
    pub utime_since: u32,
    /// Bit price in base workchain.
    pub bit_price_ps: u64,
    /// Cell price in base workchain.
    pub cell_price_ps: u64,
    /// Bit price in masterchain.
    pub mc_bit_price_ps: u64,
    /// Cell price in masterchain.
    pub mc_cell_price_ps: u64,
}

impl StoragePrices {
    const TAG: u8 = 0xcc;
}

impl<C: CellFamily> Store<C> for StoragePrices {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        builder.store_u8(Self::TAG)
            && builder.store_u32(self.utime_since)
            && builder.store_u64(self.bit_price_ps)
            && builder.store_u64(self.cell_price_ps)
            && builder.store_u64(self.mc_bit_price_ps)
            && builder.store_u64(self.mc_cell_price_ps)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for StoragePrices {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if slice.load_u8()? != Self::TAG {
            return None;
        }
        Some(Self {
            utime_since: slice.load_u32()?,
            bit_price_ps: slice.load_u64()?,
            cell_price_ps: slice.load_u64()?,
            mc_bit_price_ps: slice.load_u64()?,
            mc_cell_price_ps: slice.load_u64()?,
        })
    }
}

/// Gas limits and prices.
#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub struct GasLimitsPrices {
    /// The price of gas unit.
    pub gas_price: u64,
    /// The maximum amount of gas available for a compute phase of an ordinary transaction.
    pub gas_limit: u64,
    /// The maximum amount of gas available for a compute phase of a special transaction.
    pub special_gas_limit: u64,
    /// The maximum amount of gas available before `ACCEPT`.
    pub gas_credit: u64,
    /// The maximum amount of gas units per block.
    pub block_gas_limit: u64,
    /// Amount of debt (in tokens) after which the account will be frozen.
    pub freeze_due_limit: u64,
    /// Amount of debt (in tokens) after which the contract will be deleted.
    pub delete_due_limit: u64,
    /// Size of the first portion of gas with different price.
    pub flat_gas_limit: u64,
    /// The gas price for the first portion determinted by [`flat_gas_limit`].
    ///
    /// [`flat_gas_limit`]: GasLimitsPrices::flat_gas_limit
    pub flat_gas_price: u64,
}

impl GasLimitsPrices {
    const TAG_BASE: u8 = 0xdd;
    const TAG_EXT: u8 = 0xde;
    const TAG_FLAT_PFX: u8 = 0xd1;
}

impl<C: CellFamily> Store<C> for GasLimitsPrices {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        builder.store_u8(Self::TAG_FLAT_PFX)
            && builder.store_u64(self.flat_gas_limit)
            && builder.store_u64(self.flat_gas_price)
            && builder.store_u8(Self::TAG_EXT)
            && builder.store_u64(self.gas_price)
            && builder.store_u64(self.gas_limit)
            && builder.store_u64(self.special_gas_limit)
            && builder.store_u64(self.gas_credit)
            && builder.store_u64(self.block_gas_limit)
            && builder.store_u64(self.freeze_due_limit)
            && builder.store_u64(self.delete_due_limit)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for GasLimitsPrices {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let mut result = Self::default();
        loop {
            match slice.load_u8()? {
                Self::TAG_FLAT_PFX => {
                    result.flat_gas_limit = slice.load_u64()?;
                    result.flat_gas_price = slice.load_u64()?;
                }
                Self::TAG_EXT => {
                    result.gas_price = slice.load_u64()?;
                    result.gas_limit = slice.load_u64()?;
                    result.special_gas_limit = slice.load_u64()?;
                    result.gas_credit = slice.load_u64()?;
                    result.block_gas_limit = slice.load_u64()?;
                    result.freeze_due_limit = slice.load_u64()?;
                    result.delete_due_limit = slice.load_u64()?;
                    return Some(result);
                }
                Self::TAG_BASE => {
                    result.gas_price = slice.load_u64()?;
                    result.gas_limit = slice.load_u64()?;
                    result.gas_credit = slice.load_u64()?;
                    result.block_gas_limit = slice.load_u64()?;
                    result.freeze_due_limit = slice.load_u64()?;
                    result.delete_due_limit = slice.load_u64()?;
                    return Some(result);
                }
                _ => return None,
            }
        }
    }
}

/// Block limits parameter.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct BlockParamLimits {
    /// Value below which the parameter is considered underloaded.
    pub underload: u32,
    /// Soft limit.
    pub soft_limit: u32,
    /// Hard limit.
    pub hard_limit: u32,
}

impl BlockParamLimits {
    const TAG: u8 = 0xc3;

    /// Returns `true` if parameter limits are valid.
    pub fn is_valid(&self) -> bool {
        self.underload <= self.soft_limit && self.soft_limit <= self.hard_limit
    }
}

impl<C: CellFamily> Store<C> for BlockParamLimits {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        builder.store_u8(Self::TAG)
            && builder.store_u32(self.underload)
            && builder.store_u32(self.soft_limit)
            && builder.store_u32(self.hard_limit)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for BlockParamLimits {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if slice.load_u8()? != Self::TAG {
            return None;
        }
        Some(Self {
            underload: slice.load_u32()?,
            soft_limit: slice.load_u32()?,
            hard_limit: slice.load_u32()?,
        })
    }
}

/// Block limits.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct BlockLimits {
    /// Block size limits in bytes.
    pub bytes: BlockParamLimits,
    /// Gas limits.
    pub gas: BlockParamLimits,
    /// Logical time delta limits.
    pub lt_delta: BlockParamLimits,
}

impl BlockLimits {
    const TAG: u8 = 0x5d;
}

impl<C: CellFamily> Store<C> for BlockLimits {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        builder.store_u8(Self::TAG)
            && self.bytes.store_into(builder, finalizer)
            && self.gas.store_into(builder, finalizer)
            && self.lt_delta.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for BlockLimits {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if slice.load_u8()? != Self::TAG {
            return None;
        }
        Some(Self {
            bytes: BlockParamLimits::load_from(slice)?,
            gas: BlockParamLimits::load_from(slice)?,
            lt_delta: BlockParamLimits::load_from(slice)?,
        })
    }
}

/// Message forwarding prices.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct MsgForwardPrices {
    /// Fixed price in addition to the dynamic part.
    pub lump_price: u64,
    /// The price of bits in the message (bits in the root cell are not included).
    pub bit_price: u64,
    /// The price of cells in the message.
    pub cell_price: u64,
    /// TODO: add docs
    pub ihr_price_factor: u32,
    /// TODO: add docs
    pub first_frac: u16,
    /// TODO: add docs
    pub next_frac: u16,
}

impl MsgForwardPrices {
    const TAG: u8 = 0xea;
}

impl<C: CellFamily> Store<C> for MsgForwardPrices {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        builder.store_u8(Self::TAG)
            && builder.store_u64(self.lump_price)
            && builder.store_u64(self.bit_price)
            && builder.store_u64(self.cell_price)
            && builder.store_u32(self.ihr_price_factor)
            && builder.store_u16(self.first_frac)
            && builder.store_u16(self.next_frac)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for MsgForwardPrices {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if slice.load_u8()? != Self::TAG {
            return None;
        }
        Some(Self {
            lump_price: slice.load_u64()?,
            bit_price: slice.load_u64()?,
            cell_price: slice.load_u64()?,
            ihr_price_factor: slice.load_u32()?,
            first_frac: slice.load_u16()?,
            next_frac: slice.load_u16()?,
        })
    }
}

/// Catchain configuration params.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct CatchainConfig {
    /// Exclude masterchain validators from a validators list for a base workchain.
    pub isolate_mc_validators: bool,
    /// Change the order of validators in the masterchain validators list.
    pub shuffle_mc_validators: bool,
    /// Masterchain catchain session lifetime in seconds.
    pub mc_catchain_lifetime: u32,
    /// Catchain session lifetime for shards in seconds.
    pub shard_catchain_lifetime: u32,
    /// Period in seconds for which the subset of validators is selected for each shard.
    pub shard_validators_lifetime: u32,
    /// The number of validators per shard.
    pub shard_validators_num: u32,
}

impl CatchainConfig {
    const TAG_V1: u8 = 0xc1;
    const TAG_V2: u8 = 0xc2;
}

impl<C: CellFamily> Store<C> for CatchainConfig {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        let flags = ((self.isolate_mc_validators as u8) << 1) | (self.shuffle_mc_validators as u8);
        builder.store_u8(Self::TAG_V2)
            && builder.store_u8(flags)
            && builder.store_u32(self.mc_catchain_lifetime)
            && builder.store_u32(self.shard_catchain_lifetime)
            && builder.store_u32(self.shard_validators_lifetime)
            && builder.store_u32(self.shard_validators_num)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for CatchainConfig {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let flags = match slice.load_u8()? {
            Self::TAG_V1 => 0,
            Self::TAG_V2 => slice.load_u8()?,
            _ => return None,
        };
        if flags >> 2 != 0 {
            return None;
        }
        Some(Self {
            isolate_mc_validators: flags & 0b10 != 0,
            shuffle_mc_validators: flags & 0b01 != 0,
            mc_catchain_lifetime: slice.load_u32()?,
            shard_catchain_lifetime: slice.load_u32()?,
            shard_validators_lifetime: slice.load_u32()?,
            shard_validators_num: slice.load_u32()?,
        })
    }
}

/// Consensus configuration params.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ConsensusConfig {
    /// Allow new catchain ids.
    pub new_catchain_ids: bool,
    /// Number of block candidates per round.
    pub round_candidates: NonZeroU32,
    /// Delay in seconds before proposing a new candidate.
    pub next_candidate_delay_ms: u32,
    /// Catchain processing timeout in seconds.
    pub consensus_timeout_ms: u32,
    /// Maximum number of attempts per round.
    pub fast_attempts: u32,
    /// Duration of a round attempt in seconds.
    pub attempt_duration: u32,
    /// The maximum number of dependencies to merge.
    pub catchain_max_deps: u32,
    /// The maximum block size in bytes.
    pub max_block_bytes: u32,
    /// THe maximum size of a collated data in bytes.
    pub max_collated_bytes: u32,
}

impl ConsensusConfig {
    const TAG_V1: u8 = 0xd6;
    const TAG_V2: u8 = 0xd7;
}

impl<C: CellFamily> Store<C> for ConsensusConfig {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        let flags = self.new_catchain_ids as u8;

        builder.store_u8(Self::TAG_V2)
            && builder.store_u8(flags)
            && builder.store_u8(self.round_candidates.get() as u8)
            && builder.store_u32(self.next_candidate_delay_ms)
            && builder.store_u32(self.consensus_timeout_ms)
            && builder.store_u32(self.fast_attempts)
            && builder.store_u32(self.attempt_duration)
            && builder.store_u32(self.catchain_max_deps)
            && builder.store_u32(self.max_block_bytes)
            && builder.store_u32(self.max_collated_bytes)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ConsensusConfig {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let (flags, round_candidates) = match slice.load_u8()? {
            Self::TAG_V1 => (0, NonZeroU32::load_from(slice)?),
            Self::TAG_V2 => {
                let flags = slice.load_u8()?;
                if flags >> 1 != 0 {
                    return None;
                }
                (0, NonZeroU8::load_from(slice)?.into())
            }
            _ => return None,
        };
        Some(Self {
            new_catchain_ids: flags & 0b1 != 0,
            round_candidates,
            next_candidate_delay_ms: slice.load_u32()?,
            consensus_timeout_ms: slice.load_u32()?,
            fast_attempts: slice.load_u32()?,
            attempt_duration: slice.load_u32()?,
            catchain_max_deps: slice.load_u32()?,
            max_block_bytes: slice.load_u32()?,
            max_collated_bytes: slice.load_u32()?,
        })
    }
}

/// Validator set.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ValidatorSet {
    /// Unix timestamp from which this set will be active.
    pub utime_since: u32,
    /// Unix timestamp until which this set will be active.
    pub utime_until: u32,
    /// The number of masterchain validators.
    pub main: NonZeroU16,
    /// Total validators weight.
    pub total_weight: u64,
    /// Validators.
    pub list: Vec<ValidatorDescription>,
}

impl ValidatorSet {
    const TAG_V1: u8 = 0x11;
    const TAG_V2: u8 = 0x12;
}

impl<C> Store<C> for ValidatorSet
where
    for<'c> C: CellFamily + 'c,
{
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        let Ok(total) = u16::try_from(self.list.len()) else { return false };

        let mut validators = Dict::<C, u16, ValidatorDescription>::new();
        for (i, item) in self.list.iter().enumerate() {
            if validators.set_ext(i as u16, item, finalizer).is_err() {
                return false;
            }
        }

        builder.store_u8(Self::TAG_V2)
            && builder.store_u32(self.utime_since)
            && builder.store_u32(self.utime_until)
            && builder.store_u16(total)
            && builder.store_u16(self.main.get())
            && builder.store_u64(self.total_weight)
            && validators.store_into(builder, finalizer)
    }
}

impl<'a, C> Load<'a, C> for ValidatorSet
where
    for<'c> C: DefaultFinalizer + 'c,
{
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let with_total_weight = match slice.load_u8()? {
            Self::TAG_V1 => false,
            Self::TAG_V2 => true,
            _ => return None,
        };

        let utime_since = slice.load_u32()?;
        let utime_until = slice.load_u32()?;
        let total = slice.load_u16()? as usize;
        let main = NonZeroU16::load_from(slice)?;
        if main.get() as usize > total {
            return None;
        }

        let finalizer = &mut C::default_finalizer();

        let (mut total_weight, validators) = if with_total_weight {
            let total_weight = slice.load_u64()?;
            let dict = Dict::<C, u16, ValidatorDescription>::load_from(slice)?;
            (total_weight, dict)
        } else {
            let dict = Dict::<C, u16, ValidatorDescription>::load_from_root_ext(slice, finalizer)?;
            (0, dict)
        };

        let mut computed_total_weight = 0u64;
        let mut list = Vec::with_capacity(std::cmp::min(total, 512));
        for (i, entry) in validators.iter().enumerate().take(total) {
            let descr = match entry {
                Ok((idx, descr)) if idx as usize == i => descr,
                _ => return None,
            };

            computed_total_weight += descr.weight;
            list.push(descr);
        }

        if list.is_empty() {
            return None;
        }

        if with_total_weight {
            if total_weight != computed_total_weight {
                return None;
            }
        } else {
            total_weight = computed_total_weight;
        }

        Some(Self {
            utime_since,
            utime_until,
            main,
            total_weight,
            list,
        })
    }
}

/// Validator description.
#[derive(CustomDebug, Clone, Eq, PartialEq)]
pub struct ValidatorDescription {
    /// Validator public key.
    #[debug(with = "DisplayHash")]
    pub public_key: CellHash, // TODO: replace with everscale_crypto::ed25519::PublicKey ?
    /// Validator weight in some units.
    pub weight: u64,
    /// Optional validator ADNL address.
    #[debug(with = "DisplayOptionalHash")]
    pub adnl_addr: Option<CellHash>,
    /// Since which seqno this validator will be active.
    pub mc_seqno_since: u32,
}

impl ValidatorDescription {
    const TAG_BASIC: u8 = 0x53;
    const TAG_WITH_ADNL: u8 = 0x73;
    const TAG_WITH_MC_SEQNO: u8 = 0x93;

    const PUBKEY_TAG: u32 = 0x8e81278a;
}

impl<C: CellFamily> Store<C> for ValidatorDescription {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        let tag = if self.mc_seqno_since != 0 {
            Self::TAG_WITH_MC_SEQNO
        } else if self.adnl_addr.is_some() {
            Self::TAG_WITH_ADNL
        } else {
            Self::TAG_BASIC
        };

        if !(builder.store_u8(tag)
            && builder.store_u32(Self::PUBKEY_TAG)
            && builder.store_u256(&self.public_key)
            && builder.store_u64(self.weight))
        {
            return false;
        }

        let mut adnl = self.adnl_addr.as_ref();
        if self.mc_seqno_since != 0 {
            adnl = Some(&[0; 32]);
        }

        if let Some(adnl) = adnl {
            if !builder.store_u256(adnl) {
                return false;
            }
        }

        self.mc_seqno_since == 0 || builder.store_u32(self.mc_seqno_since)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ValidatorDescription {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let (with_adnl, with_mc_seqno) = match slice.load_u8()? {
            Self::TAG_BASIC => (false, false),
            Self::TAG_WITH_ADNL => (true, false),
            Self::TAG_WITH_MC_SEQNO => (true, true),
            _ => return None,
        };

        Some(Self {
            public_key: {
                if slice.load_u32()? != Self::PUBKEY_TAG {
                    return None;
                }
                slice.load_u256()?
            },
            weight: slice.load_u64()?,
            adnl_addr: if with_adnl {
                Some(slice.load_u256()?)
            } else {
                None
            },
            mc_seqno_since: if with_mc_seqno { slice.load_u32()? } else { 0 },
        })
    }
}
