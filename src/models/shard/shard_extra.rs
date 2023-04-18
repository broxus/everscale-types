use crate::cell::*;
use crate::dict::{AugDict, Dict};
use crate::error::Error;
use crate::num::*;

use crate::models::block::{BlockRef, ShardHashes};
use crate::models::config::BlockchainConfig;
use crate::models::currency::CurrencyCollection;

/// Additional content for masterchain state.
#[derive(Debug, Clone)]
pub struct McStateExtra {
    /// A tree of the most recent descriptions for all currently existing shards
    /// for all workchains except the masterchain.
    pub shards: ShardHashes,
    /// The most recent blockchain config (if the block is a key block).
    pub config: BlockchainConfig,
    /// Brief validator info.
    pub validator_info: ValidatorInfo,
    /// A dictionary with previous masterchain blocks.
    pub prev_blocks: OldMcBlocksInfo,
    /// Whether this state was produced after the key block.
    pub after_key_block: bool,
    /// Optional reference to the latest known key block.
    pub last_key_block: Option<BlockRef>,
    /// Block creation stats for validators from the current set.
    pub block_create_stats: Option<Dict<CellHash, CreatorStats>>,
    /// Total balance of all accounts.
    pub global_balance: CurrencyCollection,
    /// Optional copyleft rewards.
    pub copyleft_rewards: Dict<CellHash, Tokens>,
}

impl McStateExtra {
    const TAG: u16 = 0xcc26;
    const BLOCK_STATS_TAG: u8 = 0x17;
}

impl Store for McStateExtra {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        let flags = ((!self.copyleft_rewards.is_empty() as u16) << 1)
            | (self.block_create_stats.is_some() as u16);

        let cell = {
            let mut builder = CellBuilder::new();
            ok!(builder.store_u16(flags));
            ok!(self.validator_info.store_into(&mut builder, finalizer));
            ok!(self.prev_blocks.store_into(&mut builder, finalizer));
            ok!(builder.store_bit(self.after_key_block));
            ok!(self.last_key_block.store_into(&mut builder, finalizer));

            if let Some(stats) = &self.block_create_stats {
                ok!(builder.store_u8(Self::BLOCK_STATS_TAG));
                ok!(stats.store_into(&mut builder, finalizer));
            }

            if !self.copyleft_rewards.is_empty() {
                ok!(self.copyleft_rewards.store_into(&mut builder, finalizer));
            }

            ok!(builder.build_ext(finalizer))
        };

        ok!(builder.store_u16(Self::TAG));
        ok!(self.shards.store_into(builder, finalizer));
        ok!(self.config.store_into(builder, finalizer));
        ok!(builder.store_reference(cell));
        self.global_balance.store_into(builder, finalizer)
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

        let child_slice = &mut ok!(slice.load_reference()).as_slice();
        let flags = ok!(child_slice.load_u16());

        if flags >> 2 != 0 {
            return Err(Error::InvalidData);
        }

        Ok(Self {
            shards,
            config,
            validator_info: ok!(ValidatorInfo::load_from(child_slice)),
            prev_blocks: ok!(OldMcBlocksInfo::load_from(child_slice)),
            after_key_block: ok!(child_slice.load_bit()),
            last_key_block: ok!(Option::<BlockRef>::load_from(child_slice)),
            block_create_stats: if flags & 0b01 != 0 {
                if ok!(child_slice.load_u8()) != Self::BLOCK_STATS_TAG {
                    return Err(Error::InvalidTag);
                }
                Some(ok!(Dict::load_from(child_slice)))
            } else {
                None
            },
            global_balance: ok!(CurrencyCollection::load_from(slice)),
            copyleft_rewards: if flags & 0b10 != 0 {
                ok!(Dict::load_from(child_slice))
            } else {
                Dict::new()
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

/// A dictionary with old masterchain blocks by seqno.
#[derive(Debug, Clone, Store, Load)]
pub struct OldMcBlocksInfo(AugDict<u32, KeyMaxLt, KeyBlockRef>);

/// Entry value for the [`OldMcBlocksInfo`] dictionary.
#[derive(Debug, Clone, Eq, PartialEq, Store, Load)]
pub struct KeyBlockRef {
    /// Whether the referenced block is a key block.
    pub is_key_block: bool,
    /// Reference to the block.
    pub block_ref: BlockRef,
}

/// Value augmentation for the [`OldMcBlocksInfo`] dictionary.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Store, Load)]
pub struct KeyMaxLt {
    /// Has key block in a subtree.
    pub has_key_block: bool,
    /// The maximum logical time in a subtree.
    pub max_end_lt: u64,
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
