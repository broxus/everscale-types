use crate::cell::*;
use crate::dict::{AugDict, AugDictExtra, Dict};
use crate::error::Error;
use crate::num::*;

use crate::models::block::{BlockRef, ShardHashes};
use crate::models::config::BlockchainConfig;
use crate::models::currency::CurrencyCollection;

/// Additional content for masterchain state.
///
/// # TLB scheme
///
/// ```text
/// copyleft_rewards#_ counters:(HashmapE 256 Grams) = CopyleftRewards;
///
/// masterchain_state_extra#cc26
///     shard_hashes:ShardHashes
///     config:ConfigParams
///     ^[
///         flags:(## 16) { flags <= 7 }
///         validator_info:ValidatorInfo
///         prev_blocks:OldMcBlocksInfo
///         after_key_block:Bool
///         last_key_block:(Maybe ExtBlkRef)
///         block_create_stats:(flags . 0)?BlockCreateStats
///         copyleft_rewards:(flags . 1)?CopyleftRewards
///         consensus_info:(flags . 2)?ConsensusInfo
///     ]
///     global_balance:CurrencyCollection
///     = McStateExtra;
/// ```
#[derive(Debug, Clone)]
pub struct McStateExtra {
    /// A tree of the most recent descriptions for all currently existing shards
    /// for all workchains except the masterchain.
    pub shards: ShardHashes,
    /// The most recent blockchain config (if the block is a key block).
    pub config: BlockchainConfig,
    /// Brief validator info.
    pub validator_info: ValidatorInfo,
    /// Brief consensus bounds info.
    #[cfg(feature = "tycho")]
    pub consensus_info: ConsensusInfo,
    /// A dictionary with previous masterchain blocks.
    pub prev_blocks: AugDict<u32, KeyMaxLt, KeyBlockRef>,
    /// Whether this state was produced after the key block.
    pub after_key_block: bool,
    /// Optional reference to the latest known key block.
    pub last_key_block: Option<BlockRef>,
    /// Block creation stats for validators from the current set.
    pub block_create_stats: Option<Dict<HashBytes, CreatorStats>>,
    /// Total balance of all accounts.
    pub global_balance: CurrencyCollection,
    /// Optional copyleft rewards.
    pub copyleft_rewards: Dict<HashBytes, Tokens>,
}

impl McStateExtra {
    const TAG: u16 = 0xcc26;
    const BLOCK_STATS_TAG: u8 = 0x17;
}

impl Store for McStateExtra {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        #[allow(unused_mut)]
        let mut flags = ((!self.copyleft_rewards.is_empty() as u16) << 1)
            | (self.block_create_stats.is_some() as u16);

        #[cfg(feature = "tycho")]
        let has_consensus_info = {
            let non_default_info = !self.consensus_info.is_zerostate();
            flags |= (non_default_info as u16) << 2;
            non_default_info
        };

        let cell = {
            let mut builder = CellBuilder::new();
            ok!(builder.store_u16(flags));
            ok!(self.validator_info.store_into(&mut builder, context));
            ok!(self.prev_blocks.store_into(&mut builder, context));
            ok!(builder.store_bit(self.after_key_block));
            ok!(self.last_key_block.store_into(&mut builder, context));

            if let Some(stats) = &self.block_create_stats {
                ok!(builder.store_u8(Self::BLOCK_STATS_TAG));
                ok!(stats.store_into(&mut builder, context));
            }

            if !self.copyleft_rewards.is_empty() {
                ok!(self.copyleft_rewards.store_into(&mut builder, context));
            }

            #[cfg(feature = "tycho")]
            if has_consensus_info {
                ok!(self.consensus_info.store_into(&mut builder, context));
            }

            ok!(builder.build_ext(context))
        };

        ok!(builder.store_u16(Self::TAG));
        ok!(self.shards.store_into(builder, context));
        ok!(self.config.store_into(builder, context));
        ok!(builder.store_reference(cell));
        self.global_balance.store_into(builder, context)
    }
}

impl<'a> Load<'a> for McStateExtra {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        match slice.load_u16() {
            Ok(Self::TAG) => {}
            Ok(_) => return Err(Error::InvalidTag),
            Err(e) => return Err(e),
        }

        let shards = ok!(ShardHashes::load_from(slice));
        let config = ok!(BlockchainConfig::load_from(slice));

        let child_slice = &mut ok!(slice.load_reference_as_slice());
        let flags = ok!(child_slice.load_u16());

        #[cfg(not(feature = "tycho"))]
        const RESERVED_BITS: usize = 2;
        #[cfg(feature = "tycho")]
        const RESERVED_BITS: usize = 3;

        if flags >> RESERVED_BITS != 0 {
            return Err(Error::InvalidData);
        }

        Ok(Self {
            shards,
            config,
            validator_info: ok!(ValidatorInfo::load_from(child_slice)),
            prev_blocks: ok!(AugDict::load_from(child_slice)),
            after_key_block: ok!(child_slice.load_bit()),
            last_key_block: ok!(Option::<BlockRef>::load_from(child_slice)),
            block_create_stats: if flags & 0b001 != 0 {
                if ok!(child_slice.load_u8()) != Self::BLOCK_STATS_TAG {
                    return Err(Error::InvalidTag);
                }
                Some(ok!(Dict::load_from(child_slice)))
            } else {
                None
            },
            global_balance: ok!(CurrencyCollection::load_from(slice)),
            copyleft_rewards: if flags & 0b010 != 0 {
                ok!(Dict::load_from(child_slice))
            } else {
                Dict::new()
            },
            #[cfg(feature = "tycho")]
            consensus_info: if flags & 0b100 != 0 {
                ok!(ConsensusInfo::load_from(child_slice))
            } else {
                ConsensusInfo::ZEROSTATE
            },
        })
    }
}

/// Brief validator info.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Store, Load)]
pub struct ValidatorInfo {
    /// Last 4 bytes of the hash of the validator list.
    pub validator_list_hash_short: u32,
    /// Seqno of the catchain session.
    pub catchain_seqno: u32,
    /// Whether the value of catchain seqno has been incremented
    /// and will it also be incremented in the next block.
    pub nx_cc_updated: bool,
}

/// Brief validator basic info.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Store, Load)]
pub struct ValidatorBaseInfo {
    /// Last 4 bytes of the hash of the validator list.
    pub validator_list_hash_short: u32,
    /// Seqno of the catchain session.
    pub catchain_seqno: u32,
}

/// Brief consensus bounds info.
///
/// ```text
/// consensus_info#_
///     vset_switch_round:uint32
///     prev_vset_switch_round:uint32
///     genesis_info:GenesisInfo
///     prev_shuffle_mc_validators:Bool
///     = ConsensusInfo;
/// ```
#[derive(Default, Debug, Copy, Clone, Eq, PartialEq, Store, Load)]
pub struct ConsensusInfo {
    /// The most recent round from which the mempool session starts.
    pub vset_switch_round: u32,

    /// The round from which the previous mempool session was started.
    pub prev_vset_switch_round: u32,

    /// The last applied genesis params
    /// Can be changed in node configs to start new session
    pub genesis_info: GenesisInfo,

    /// Previous state of the `shuffle_mc_validators` flags.
    pub prev_shuffle_mc_validators: bool,
}

/// Brief genesis info.
///
/// ```text
/// genesis_info#_
///     start_round:uint32
///     millis:uint64
///     = GenesisInfo;
/// ```
#[derive(Default, Debug, Copy, Clone, Eq, PartialEq, Store, Load)]
pub struct GenesisInfo {
    /// Unaligned genesis round that corresponds to the last (maybe partially) processed anchor
    /// from the last master chain block signed by majority.
    /// Aligned (a bit increased or left unchanged) genesis round affects the overlay id.
    pub start_round: u32,

    /// Timestamp in milliseconds to include into mempool genesis point.
    /// Newly produced points are required to have greater value.
    /// Unchanged value affects the overlay id.
    pub millis: u64,
}

impl ConsensusInfo {
    /// Initial consensus info state.
    pub const ZEROSTATE: Self = Self {
        vset_switch_round: 0,
        prev_vset_switch_round: 0,
        genesis_info: GenesisInfo {
            start_round: 0,
            millis: 0,
        },
        prev_shuffle_mc_validators: false,
    };

    /// Returns whether this info corresponds to the zerostate info.
    pub fn is_zerostate(&self) -> bool {
        self == &Self::ZEROSTATE
    }
}

/// Entry value for the [`OldMcBlocksInfo`] dictionary.
#[derive(Debug, Clone, Eq, PartialEq, Store, Load)]
pub struct KeyBlockRef {
    /// Whether the referenced block is a key block.
    pub is_key_block: bool,
    /// Reference to the block.
    pub block_ref: BlockRef,
}

/// Value augmentation for the [`OldMcBlocksInfo`] dictionary.
#[derive(Debug, Default, Copy, Clone, Eq, PartialEq, Store, Load)]
pub struct KeyMaxLt {
    /// Has key block in a subtree.
    pub has_key_block: bool,
    /// The maximum logical time in a subtree.
    pub max_end_lt: u64,
}

impl AugDictExtra for KeyMaxLt {
    fn comp_add(
        left: &mut CellSlice,
        right: &mut CellSlice,
        b: &mut CellBuilder,
        cx: &mut dyn CellContext,
    ) -> Result<(), Error> {
        let left = ok!(Self::load_from(left));
        let right = ok!(Self::load_from(right));
        Self {
            has_key_block: left.has_key_block || right.has_key_block,
            max_end_lt: std::cmp::max(left.max_end_lt, right.max_end_lt),
        }
        .store_into(b, cx)
    }
}

/// Block production statistics for the single validator.
#[derive(Debug, Clone, Eq, PartialEq, Store, Load)]
#[tlb(tag = "#4")]
pub struct CreatorStats {
    /// Masterchain block production statistics.
    pub mc_blocks: BlockCounters,
    /// Block production statistics for other workchains.
    pub shard_blocks: BlockCounters,
}

/// Block counters with absolute value and rates.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Store, Load)]
pub struct BlockCounters {
    /// Unix timestamp in seconds of the last counters update.
    pub updated_at: u32,
    /// Total counter value.
    pub total: u64,
    /// Scaled counter rate.
    pub cnt2048: u64,
    /// Scaled counter rate (better precision).
    pub cnt65536: u64,
}
