//! Shard state models.

#[cfg(feature = "sync")]
use std::sync::OnceLock;

use crate::cell::*;
use crate::dict::Dict;
use crate::error::*;

use crate::models::block::{BlockRef, ShardIdent};
use crate::models::currency::CurrencyCollection;
use crate::models::Lazy;

#[cfg(feature = "tycho")]
use crate::models::ShardIdentFull;

pub use self::shard_accounts::*;
pub use self::shard_extra::*;

#[cfg(feature = "venom")]
use super::ShardBlockRefs;

mod shard_accounts;
mod shard_extra;

#[cfg(test)]
mod tests;

/// Applied shard state.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ShardState {
    /// The next indivisible state in the shard.
    Unsplit(ShardStateUnsplit),
    /// Next indivisible states after shard split.
    Split(ShardStateSplit),
}

impl Store for ShardState {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        match self {
            Self::Unsplit(state) => state.store_into(builder, context),
            Self::Split(state) => state.store_into(builder, context),
        }
    }
}

impl<'a> Load<'a> for ShardState {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        Ok(if ok!(slice.get_bit(0)) {
            match ShardStateUnsplit::load_from(slice) {
                Ok(state) => Self::Unsplit(state),
                Err(e) => return Err(e),
            }
        } else {
            match ShardStateSplit::load_from(slice) {
                Ok(state) => Self::Split(state),
                Err(e) => return Err(e),
            }
        })
    }
}

/// State of the single shard.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ShardStateUnsplit {
    /// Global network id.
    pub global_id: i32,
    /// Id of the shard.
    pub shard_ident: ShardIdent,
    /// Sequence number of the corresponding block.
    pub seqno: u32,
    /// Vertical sequcent number of the corresponding block.
    pub vert_seqno: u32,
    /// Unix timestamp when the block was created.
    pub gen_utime: u32,
    /// Milliseconds part of the timestamp when the block was created.
    #[cfg(any(feature = "venom", feature = "tycho"))]
    pub gen_utime_ms: u16,
    /// Logical time when the state was created.
    pub gen_lt: u64,
    /// Minimal referenced seqno of the masterchain block.
    pub min_ref_mc_seqno: u32,

    /// Output messages queue info (stub).
    #[cfg(not(feature = "tycho"))]
    pub out_msg_queue_info: Cell,

    /// Processed up to info for externals and internals.
    #[cfg(feature = "tycho")]
    pub processed_upto: Lazy<ProcessedUptoInfo>,

    /// Whether this state was produced before the shards split.
    pub before_split: bool,
    /// Reference to the dictionary with shard accounts.
    pub accounts: Lazy<ShardAccounts>,
    /// Mask for the overloaded blocks.
    pub overload_history: u64,
    /// Mask for the underloaded blocks.
    pub underload_history: u64,
    /// Total balance for all currencies.
    pub total_balance: CurrencyCollection,
    /// Total pending validator fees.
    pub total_validator_fees: CurrencyCollection,
    /// Dictionary with all libraries and its providers.
    pub libraries: Dict<HashBytes, LibDescr>,
    /// Optional reference to the masterchain block.
    pub master_ref: Option<BlockRef>,
    /// Shard state additional info.
    pub custom: Option<Lazy<McStateExtra>>,
    /// References to the latest known blocks from all shards.
    #[cfg(feature = "venom")]
    pub shard_block_refs: Option<ShardBlockRefs>,
}

#[cfg(feature = "sync")]
impl Default for ShardStateUnsplit {
    fn default() -> Self {
        Self {
            global_id: 0,
            shard_ident: ShardIdent::MASTERCHAIN,
            seqno: 0,
            vert_seqno: 0,
            gen_utime: 0,
            #[cfg(any(feature = "venom", feature = "tycho"))]
            gen_utime_ms: 0,
            gen_lt: 0,
            min_ref_mc_seqno: 0,
            #[cfg(not(feature = "tycho"))]
            out_msg_queue_info: Cell::default(),
            #[cfg(feature = "tycho")]
            processed_upto: Self::empty_processed_upto_info().clone(),
            before_split: false,
            accounts: Self::empty_shard_accounts().clone(),
            overload_history: 0,
            underload_history: 0,
            total_balance: CurrencyCollection::ZERO,
            total_validator_fees: CurrencyCollection::ZERO,
            libraries: Dict::new(),
            master_ref: None,
            custom: None,
            #[cfg(feature = "venom")]
            shard_block_refs: None,
        }
    }
}

impl ShardStateUnsplit {
    const TAG_V1: u32 = 0x9023afe2;
    #[cfg(any(feature = "venom", feature = "tycho"))]
    const TAG_V2: u32 = 0x9023aeee;

    /// Returns a static reference to the empty processed up to info.
    #[cfg(all(feature = "sync", feature = "tycho"))]
    pub fn empty_processed_upto_info() -> &'static Lazy<ProcessedUptoInfo> {
        static PROCESSED_UPTO_INFO: OnceLock<Lazy<ProcessedUptoInfo>> = OnceLock::new();
        PROCESSED_UPTO_INFO.get_or_init(|| Lazy::new(&ProcessedUptoInfo::default()).unwrap())
    }

    /// Returns a static reference to the empty shard accounts.
    #[cfg(feature = "sync")]
    pub fn empty_shard_accounts() -> &'static Lazy<ShardAccounts> {
        static SHARD_ACCOUNTS: OnceLock<Lazy<ShardAccounts>> = OnceLock::new();
        SHARD_ACCOUNTS.get_or_init(|| Lazy::new(&ShardAccounts::new()).unwrap())
    }

    /// Tries to load shard accounts dictionary.
    pub fn load_accounts(&self) -> Result<ShardAccounts, Error> {
        self.accounts.load()
    }

    /// Tries to load additional masterchain data.
    pub fn load_custom(&self) -> Result<Option<McStateExtra>, Error> {
        match &self.custom {
            Some(custom) => match custom.load() {
                Ok(custom) => Ok(Some(custom)),
                Err(e) => Err(e),
            },
            None => Ok(None),
        }
    }

    /// Tries to set additional masterchain data.
    pub fn set_custom(&mut self, value: Option<&McStateExtra>) -> Result<(), Error> {
        match (&mut self.custom, value) {
            (None, None) => Ok(()),
            (None, Some(value)) => {
                self.custom = Some(ok!(Lazy::new(value)));
                Ok(())
            }
            (Some(_), None) => {
                self.custom = None;
                Ok(())
            }
            (Some(custom), Some(value)) => custom.set(value),
        }
    }
}

impl Store for ShardStateUnsplit {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        let child_cell = {
            let mut builder = CellBuilder::new();
            ok!(builder.store_u64(self.overload_history));
            ok!(builder.store_u64(self.underload_history));
            ok!(self.total_balance.store_into(&mut builder, context));
            ok!(self.total_validator_fees.store_into(&mut builder, context));
            ok!(self.libraries.store_into(&mut builder, context));
            ok!(self.master_ref.store_into(&mut builder, context));
            ok!(builder.build_ext(context))
        };

        #[cfg(not(any(feature = "venom", feature = "tycho")))]
        ok!(builder.store_u32(Self::TAG_V1));
        #[cfg(any(feature = "venom", feature = "tycho"))]
        ok!(builder.store_u32(Self::TAG_V2));

        ok!(builder.store_u32(self.global_id as u32));
        ok!(self.shard_ident.store_into(builder, context));
        ok!(builder.store_u32(self.seqno));
        ok!(builder.store_u32(self.vert_seqno));
        ok!(builder.store_u32(self.gen_utime));

        #[cfg(any(feature = "venom", feature = "tycho"))]
        ok!(builder.store_u16(self.gen_utime_ms));

        ok!(builder.store_u64(self.gen_lt));
        ok!(builder.store_u32(self.min_ref_mc_seqno));
        #[cfg(not(feature = "tycho"))]
        ok!(self.out_msg_queue_info.store_into(builder, context));
        #[cfg(feature = "tycho")]
        ok!(self.processed_upto.store_into(builder, context));
        ok!(builder.store_bit(self.before_split));
        ok!(builder.store_reference(self.accounts.cell.clone()));
        ok!(builder.store_reference(child_cell));

        #[cfg(not(feature = "venom"))]
        ok!(self.custom.store_into(builder, context));

        #[cfg(feature = "venom")]
        if self.custom.is_some() && self.shard_block_refs.is_some() {
            return Err(Error::InvalidData);
        } else if let Some(refs) = &self.shard_block_refs {
            ok!(refs.store_into(builder, context));
        } else {
            ok!(self.custom.store_into(builder, context));
        }

        Ok(())
    }
}

impl<'a> Load<'a> for ShardStateUnsplit {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let fast_finality = match slice.load_u32() {
            Ok(Self::TAG_V1) => false,
            #[cfg(any(feature = "venom", feature = "tycho"))]
            Ok(Self::TAG_V2) => true,
            Ok(_) => return Err(Error::InvalidTag),
            Err(e) => return Err(e),
        };

        #[cfg(not(any(feature = "venom", feature = "tycho")))]
        let _ = fast_finality;

        #[cfg(not(feature = "tycho"))]
        let out_msg_queue_info = ok!(<_>::load_from(slice));

        #[cfg(feature = "tycho")]
        let processed_upto = ok!(Lazy::load_from(slice));

        let accounts = ok!(Lazy::load_from(slice));

        let child_slice = &mut ok!(slice.load_reference_as_slice());

        let global_id = ok!(slice.load_u32()) as i32;
        let shard_ident = ok!(ShardIdent::load_from(slice));

        Ok(Self {
            global_id,
            shard_ident,
            seqno: ok!(slice.load_u32()),
            vert_seqno: ok!(slice.load_u32()),
            gen_utime: ok!(slice.load_u32()),
            #[cfg(any(feature = "venom", feature = "tycho"))]
            gen_utime_ms: if fast_finality {
                ok!(slice.load_u16())
            } else {
                0
            },
            gen_lt: ok!(slice.load_u64()),
            min_ref_mc_seqno: ok!(slice.load_u32()),
            before_split: ok!(slice.load_bit()),
            accounts,
            overload_history: ok!(child_slice.load_u64()),
            underload_history: ok!(child_slice.load_u64()),
            total_balance: ok!(CurrencyCollection::load_from(child_slice)),
            total_validator_fees: ok!(CurrencyCollection::load_from(child_slice)),
            libraries: ok!(Dict::load_from(child_slice)),
            master_ref: ok!(Option::<BlockRef>::load_from(child_slice)),
            #[cfg(not(feature = "tycho"))]
            out_msg_queue_info,
            #[cfg(feature = "tycho")]
            processed_upto,
            #[allow(unused_labels)]
            custom: 'custom: {
                #[cfg(feature = "venom")]
                if !shard_ident.is_masterchain() {
                    break 'custom None;
                }
                ok!(Option::<Lazy<McStateExtra>>::load_from(slice))
            },
            #[cfg(feature = "venom")]
            shard_block_refs: if shard_ident.is_masterchain() {
                None
            } else {
                Some(ok!(ShardBlockRefs::load_from(slice)))
            },
        })
    }
}

/// Next indivisible states after shard split.
#[derive(Debug, Clone, Eq, PartialEq, Store, Load)]
#[tlb(tag = "#5f327da5")]
pub struct ShardStateSplit {
    /// Reference to the state of the left shard.
    pub left: Lazy<ShardStateUnsplit>,
    /// Reference to the state of the right shard.
    pub right: Lazy<ShardStateUnsplit>,
}

/// Shared libraries currently can be present only in masterchain blocks.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LibDescr {
    /// Library code.
    pub lib: Cell,
    /// Accounts in the masterchain that store this library.
    pub publishers: Dict<HashBytes, ()>,
}

impl Store for LibDescr {
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn CellContext) -> Result<(), Error> {
        ok!(builder.store_small_uint(0, 2));
        ok!(builder.store_reference(self.lib.clone()));
        match self.publishers.root() {
            Some(root) => builder.store_reference(root.clone()),
            None => Err(Error::InvalidData),
        }
    }
}

impl<'a> Load<'a> for LibDescr {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        if ok!(slice.load_small_uint(2)) != 0 {
            return Err(Error::InvalidTag);
        }
        Ok(Self {
            lib: ok!(slice.load_reference_cloned()),
            publishers: ok!(Dict::load_from_root_ext(slice, &mut Cell::empty_context())),
        })
    }
}

/// Processed upto info for externals and internals.
#[cfg(feature = "tycho")]
#[derive(Debug, Default, Clone, Store, Load)]
#[tlb(tag = "#c1")]
pub struct ProcessedUptoInfo {
    /// Externals read range and processed to info.
    pub externals: ExternalsProcessedUpto,

    /// We split internals storage by partitions.
    /// There are at least 2: normal and low-priority.
    /// And inside partitions we split messages by source shard.
    pub internals: InternalsProcessedUpto,
}

/// Describes the processed to point and ranges of externals
/// that we should read to reproduce the same messages buffer
/// on which the previous block collation stopped.
#[cfg(feature = "tycho")]
#[derive(Debug, Default, Clone, Store, Load)]
#[tlb(tag = "#c2")]
pub struct ExternalsProcessedUpto {
    /// Externals processed to (anchor id, msgs offset).
    /// All externals up to this point
    /// already processed during previous blocks collations.
    pub processed_to: (u32, u64),

    /// Externals read ranges map by block seqno.
    pub ranges: Dict<u32, ExternalsRange>,
}

/// Describes externals read range.
#[cfg(feature = "tycho")]
#[derive(Debug, Default, Clone, Store, Load)]
#[tlb(tag = "#c3")]
pub struct ExternalsRange {
    /// From mempool anchor id and msgs offset.
    pub from: (u32, u64),
    /// To mempool anchor id and msgs offset.
    pub to: (u32, u64),

    /// Chain time of the block when range was read.
    pub ct: u64,

    /// How many times external messages were collected from the ranges buffers.
    /// Every range contains offset that was reached when range was the last.
    /// So the current last range contains the actual offset.
    pub processed_offset: u32,
}

/// Contains internals processed upto info.
#[cfg(feature = "tycho")]
#[derive(Debug, Default, Clone, Store, Load)]
#[tlb(tag = "#c4")]
pub struct InternalsProcessedUpto {
    /// Internals processed upto info by partitions.
    pub partitions: Dict<u8, PartitionProcessedUpto>,
}

/// Describes the processed to point and ranges of internals
/// that we should read to reproduce the same messages buffer
/// on which the previous block collation stopped.
#[cfg(feature = "tycho")]
#[derive(Debug, Default, Clone, Store, Load)]
#[tlb(tag = "#c5")]
pub struct PartitionProcessedUpto {
    /// Internals processed to (LT, HASH) by source shards.
    /// All internals up to this point
    /// already processed during previous blocks collations.
    pub processed_to: Dict<ShardIdentFull, (u64, HashBytes)>,

    /// Internals read ranges map by block seqno.
    pub ranges: Dict<u32, InternalsRange>,
}

/// Describes internals read range.
#[cfg(feature = "tycho")]
#[derive(Debug, Default, Clone, Store, Load)]
#[tlb(tag = "#c6")]
pub struct InternalsRange {
    /// How many times internal messages were collected from the ranges buffers.
    /// Every range contains offset that was reached when range was the last.
    /// So the current last range contains the actual offset.
    pub processed_offset: u32,

    /// Internals read ranges by source shards.
    pub shards: Dict<ShardIdentFull, ShardRange>,
}

/// Describes internals read range from one shard.
#[cfg(feature = "tycho")]
#[derive(Debug, Default, Clone, Store, Load)]
#[tlb(tag = "#c7")]
pub struct ShardRange {
    /// From LT.
    pub from: u64,
    /// To LT.
    pub to: u64,
}
