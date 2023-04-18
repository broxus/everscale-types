use crate::cell::*;
use crate::dict::{self, Dict, DictKey};
use crate::error::Error;
use crate::num::Tokens;
use crate::util::*;

use crate::models::block::block_id::{BlockId, ShardIdent};
use crate::models::currency::CurrencyCollection;

/// A tree of the most recent descriptions for all currently existing shards
/// for all workchains except the masterchain.
#[derive(Debug, Clone, Eq, PartialEq, Store, Load)]
pub struct ShardHashes(Dict<i32, Cell>);

impl ShardHashes {
    /// Gets an iterator over the entries of the shard description trees, sorted by
    /// shard ident. The iterator element is `Result<(ShardIdent, ShardDescription)>`.
    ///
    /// If the dict or tree is invalid, finishes after the first invalid element.
    /// returning an error.
    pub fn iter(&self) -> ShardHashesIter<'_> {
        ShardHashesIter::new(self.0.root())
    }

    /// Gets an iterator over the raw entries of the shard description trees, sorted by
    /// shard ident. The iterator element is `Result<(ShardIdent, CellSlice)>`.
    ///
    /// If the dict or tree is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn raw_iter(&self) -> ShardHashesRawIter<'_> {
        ShardHashesRawIter::new(self.0.root())
    }

    /// Gets an iterator over the latest blocks in all shards, sorted by
    /// shard ident. The iterator element is `Result<BlockId>`.
    ///
    /// If the dict or tree is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn latest_blocks(&self) -> LatestBlocksIter<'_> {
        LatestBlocksIter::new(self.0.root())
    }

    /// Returns a shards description tree root for the specified workchain.
    pub fn get_workchain_shards(
        &self,
        workchain: i32,
    ) -> Result<Option<WorkchainShardHashes>, Error> {
        match self.0.get(workchain) {
            Ok(Some(root)) => Ok(Some(WorkchainShardHashes { workchain, root })),
            Ok(None) => Ok(None),
            Err(e) => Err(e),
        }
    }

    /// Returns `true` if the dictionary contains a workchain for the specified id.
    pub fn contains_workchain<Q>(&self, workchain: i32) -> Result<bool, Error> {
        self.0.contains_key(workchain)
    }
}

/// A tree of the most recent descriptions for all currently existing shards
/// for a single workchain.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct WorkchainShardHashes {
    workchain: i32,
    root: Cell,
}

impl WorkchainShardHashes {
    /// Gets an iterator over the keys of the shard descriptions tree, sorted by key.
    /// The iterator element type is `Result<CellSlice>`.
    ///
    /// If the tree is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn keys(&self) -> WorkchainShardHashesKeysIter<'_> {
        WorkchainShardHashesKeysIter::new(self.workchain, self.root.as_ref())
    }

    /// Gets an iterator over the entries of the shard descriptions tree, sorted by key.
    /// The iterator element type is `Result<(ShardIdent, ShardDescription)>`.
    ///
    /// If the tree is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn iter(&self) -> WorkchainShardHashesIter<'_> {
        WorkchainShardHashesIter::new(self.workchain, self.root.as_ref())
    }

    /// Gets an iterator over the latest block in the current workchain, sorted by key.
    /// The iterator element type is `Result<BlockId>`.
    ///
    /// If the tree is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn latest_blocks(&self) -> WorkchainLatestBlocksIter<'_> {
        WorkchainLatestBlocksIter::new(self.workchain, self.root.as_ref())
    }

    /// Gets an iterator over the raw entries of the shard descriptions tree, sorted by key.
    /// The iterator element type is `Result<(ShardIdent, CellSlice)>`.
    ///
    /// If the tree is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn raw_iter(&self) -> WorkchainShardHashesRawIter<'_> {
        WorkchainShardHashesRawIter::new(self.workchain, self.root.as_ref())
    }

    /// Gets an iterator over the raw values of the shard descriptions tree, sorted by key.
    /// The iterator element type is `Result<CellSlice>`.
    ///
    /// If the tree is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn raw_values(&self) -> WorkchainShardHashesRawValuesIter<'_> {
        WorkchainShardHashesRawValuesIter::new(self.workchain, self.root.as_ref())
    }
}

/// An iterator over the entries of a [`ShardHashes`].
///
/// This struct is created by the [`iter`] method on [`ShardHashes`].
/// See its documentation for more.
///
/// [`iter`]: ShardHashes::iter
#[derive(Clone)]
pub struct ShardHashesIter<'a> {
    inner: ShardHashesRawIter<'a>,
}

impl<'a> ShardHashesIter<'a> {
    fn new(dict: &'a Option<Cell>) -> Self {
        Self {
            inner: ShardHashesRawIter::new(dict),
        }
    }
}

impl Iterator for ShardHashesIter<'_> {
    type Item = Result<(ShardIdent, ShardDescription), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.inner.next()? {
            Ok((shard_ident, mut value)) => match ShardDescription::load_from(&mut value) {
                Ok(value) => Ok((shard_ident, value)),
                Err(e) => Err(self.inner.finish(e)),
            },
            Err(e) => Err(e),
        })
    }
}

/// An iterator over the raw entries of a [`ShardHashes`].
///
/// This struct is created by the [`raw_iter`] method on [`ShardHashes`].
/// See its documentation for more.
///
/// [`raw_iter`]: ShardHashes::raw_iter
#[derive(Clone)]
pub struct ShardHashesRawIter<'a> {
    dict_iter: dict::RawIter<'a>,
    shard_hashes_iter: Option<WorkchainShardHashesRawIter<'a>>,
    status: IterStatus,
}

impl<'a> ShardHashesRawIter<'a> {
    fn new(dict: &'a Option<Cell>) -> Self {
        Self {
            dict_iter: dict::RawIter::new(dict, 32),
            shard_hashes_iter: None,
            status: IterStatus::Valid,
        }
    }

    #[inline(always)]
    fn finish(&mut self, error: Error) -> Error {
        self.status = IterStatus::Broken;
        error
    }
}

impl<'a> Iterator for ShardHashesRawIter<'a> {
    type Item = Result<(ShardIdent, CellSlice<'a>), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if unlikely(!self.status.is_valid()) {
            return if self.status.is_pruned() {
                self.status = IterStatus::Broken;
                Some(Err(Error::PrunedBranchAccess))
            } else {
                None
            };
        }

        loop {
            // Try to read next item from the current shards tree
            if let Some(iter) = &mut self.shard_hashes_iter {
                match iter.next() {
                    Some(next_item) => break Some(next_item),
                    None => self.shard_hashes_iter = None,
                }
            }

            // Try to get a shards tree for the next workchain
            self.shard_hashes_iter = Some(match self.dict_iter.next()? {
                Ok((key, value)) => {
                    // Parse workchain id from the raw iterator
                    let workchain = match i32::from_raw_data(key.raw_data()) {
                        Some(workchain) => workchain,
                        None => return Some(Err(self.finish(Error::CellUnderflow))),
                    };

                    // Shards tree is in the first reference in each value
                    let tree_root = match value.get_reference(0) {
                        Ok(cell) => cell,
                        Err(e) => break Some(Err(self.finish(e))),
                    };

                    // Create shards tree iterator
                    WorkchainShardHashesRawIter::new(workchain, tree_root)
                }
                Err(e) => break Some(Err(self.finish(e))),
            });
        }
    }
}

/// An iterator over the latest blocks of a [`ShardHashes`].
///
/// This struct is created by the [`latest_blocks`] method on [`ShardHashes`].
/// See its documentation for more.
///
/// [`latest_blocks`]: ShardHashes::latest_blocks
#[derive(Clone)]
pub struct LatestBlocksIter<'a> {
    inner: ShardHashesRawIter<'a>,
}

impl<'a> LatestBlocksIter<'a> {
    /// Creates an iterator over the latest blocks of a [`ShardHashes`].
    pub fn new(dict: &'a Option<Cell>) -> Self {
        Self {
            inner: ShardHashesRawIter::new(dict),
        }
    }
}

impl Iterator for LatestBlocksIter<'_> {
    type Item = Result<BlockId, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.inner.next()? {
            Ok((shard_ident, value)) => match parse_block_id(shard_ident, value) {
                Ok(value) => Ok(value),
                Err(e) => Err(self.inner.finish(e)),
            },
            Err(e) => Err(e),
        })
    }
}

/// An iterator over the entries of a [`WorkchainShardHashes`].
///
/// This struct is created by the [`iter`] method on [`WorkchainShardHashes`].
/// See its documentation for more.
///
/// [`iter`]: WorkchainShardHashes::iter
#[derive(Clone)]
pub struct WorkchainShardHashesIter<'a> {
    inner: WorkchainShardHashesRawIter<'a>,
}

impl<'a> WorkchainShardHashesIter<'a> {
    /// Creates an iterator over the entries of a [`WorkchainShardHashes`].
    pub fn new(workchain: i32, root: &'a DynCell) -> Self {
        Self {
            inner: WorkchainShardHashesRawIter::new(workchain, root),
        }
    }
}

impl Iterator for WorkchainShardHashesIter<'_> {
    type Item = Result<(ShardIdent, ShardDescription), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.inner.next()? {
            Ok((shard_ident, mut value)) => match ShardDescription::load_from(&mut value) {
                Ok(value) => Ok((shard_ident, value)),
                Err(e) => Err(self.inner.finish(e)),
            },
            Err(e) => Err(e),
        })
    }
}

/// An iterator over the raw entries of a [`WorkchainShardHashes`].
///
/// This struct is created by the [`raw_iter`] method on [`WorkchainShardHashes`].
/// See its documentation for more.
///
/// [`raw_iter`]: WorkchainShardHashes::raw_iter
#[derive(Clone)]
pub struct WorkchainShardHashesRawIter<'a> {
    workchain: i32,
    leaf: Option<CellSlice<'a>>,
    segments: Vec<IterSegment<'a>>,
    status: IterStatus,
}

impl<'a> WorkchainShardHashesRawIter<'a> {
    /// Creates an iterator over the raw entries of a [`WorkchainShardHashes`].
    pub fn new(workchain: i32, root: &'a DynCell) -> Self {
        let status = 'error: {
            if root.descriptor().is_pruned_branch() {
                break 'error IterStatus::Pruned;
            }

            let mut slice = root.as_slice();

            let is_fork = match slice.load_bit() {
                Ok(bit) => bit,
                Err(_) => break 'error IterStatus::Broken,
            };

            let mut result = Self {
                workchain,
                leaf: None,
                segments: Vec::new(),
                status: IterStatus::Valid,
            };

            if is_fork {
                result.segments.push(IterSegment {
                    data: root,
                    is_right: false,
                });
            } else {
                result.leaf = Some(slice);
            }

            return result;
        };

        // Fallback to broken iterator
        Self {
            workchain,
            leaf: None,
            segments: Vec::new(),
            status,
        }
    }

    fn finish(&mut self, err: Error) -> Error {
        self.status = IterStatus::Broken;
        err
    }
}

impl<'a> Iterator for WorkchainShardHashesRawIter<'a> {
    type Item = Result<(ShardIdent, CellSlice<'a>), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        fn build_shard_prefix(segments: &[IterSegment<'_>]) -> u64 {
            let mut result = ShardIdent::PREFIX_FULL;
            for segment in segments {
                result = (ShardIdent::PREFIX_FULL * segment.is_right as u64) | result >> 1;
            }
            result
        }

        if unlikely(!self.status.is_valid()) {
            return if self.status.is_pruned() {
                self.status = IterStatus::Broken;
                Some(Err(Error::PrunedBranchAccess))
            } else {
                None
            };
        }

        let leaf = match self.leaf.take() {
            Some(leaf) => leaf,
            None => loop {
                let segment = self.segments.last()?;
                let mut slice = match segment.data.get_reference_as_slice(segment.is_right as u8) {
                    Ok(child) => child,
                    Err(e) => return Some(Err(self.finish(e))),
                };

                match slice.load_bit() {
                    // Break on leaf
                    Ok(false) => break slice,
                    // Add segment on fork
                    Ok(true) if self.segments.len() < ShardIdent::MAX_SPLIT_DEPTH as usize => {
                        self.segments.push(IterSegment {
                            data: slice.cell(),
                            is_right: false,
                        })
                    }
                    _ => return Some(Err(self.finish(Error::CellUnderflow))),
                };
            },
        };

        // Build shard prefix from segments
        // SAFETY: segments lengths is guaranteed to be in range 1..=ShardIdent::MAX_SPLIT_DEPTH
        let shard_prefix = unsafe {
            ShardIdent::new_unchecked(self.workchain, build_shard_prefix(&self.segments))
        };

        // Remove all finished segments from the top of the stack
        while matches!(self.segments.last(), Some(segment) if segment.is_right) {
            self.segments.pop();
        }

        // Move last bit
        if let Some(segment) = self.segments.last_mut() {
            segment.is_right = true;
        }

        Some(Ok((shard_prefix, leaf)))
    }
}

/// An iterator over the latest blocks of a [`WorkchainShardHashes`].
///
/// This struct is created by the [`latest_blocks`] method on [`WorkchainShardHashes`].
/// See its documentation for more.
///
/// [`latest_blocks`]: WorkchainShardHashes::latest_blocks
#[derive(Clone)]
pub struct WorkchainLatestBlocksIter<'a> {
    inner: WorkchainShardHashesRawIter<'a>,
}

impl<'a> WorkchainLatestBlocksIter<'a> {
    /// Creates an iterator over the latest blocks of a [`WorkchainShardHashes`].
    pub fn new(workchain: i32, root: &'a DynCell) -> Self {
        Self {
            inner: WorkchainShardHashesRawIter::new(workchain, root),
        }
    }
}

impl Iterator for WorkchainLatestBlocksIter<'_> {
    type Item = Result<BlockId, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.inner.next()? {
            Ok((shard_ident, value)) => match parse_block_id(shard_ident, value) {
                Ok(block_id) => Ok(block_id),
                Err(e) => Err(self.inner.finish(e)),
            },
            Err(e) => Err(e),
        })
    }
}

/// An iterator over the keys of a [`WorkchainShardHashes`].
///
/// This struct is created by the [`keys`] method on [`WorkchainShardHashes`].
/// See its documentation for more.
///
/// [`keys`]: WorkchainShardHashes::keys
#[derive(Clone)]
pub struct WorkchainShardHashesKeysIter<'a> {
    inner: WorkchainShardHashesRawIter<'a>,
}

impl<'a> WorkchainShardHashesKeysIter<'a> {
    /// Creates an iterator over the keys of a [`WorkchainShardHashes`].
    pub fn new(workchain: i32, root: &'a DynCell) -> Self {
        Self {
            inner: WorkchainShardHashesRawIter::new(workchain, root),
        }
    }
}

impl<'a> Iterator for WorkchainShardHashesKeysIter<'a> {
    type Item = Result<ShardIdent, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next()? {
            Ok((key, _)) => Some(Ok(key)),
            Err(e) => Some(Err(e)),
        }
    }
}

/// An iterator over the raw values of a [`WorkchainShardHashes`].
///
/// This struct is created by the [`raw_values`] method on [`WorkchainShardHashes`].
/// See its documentation for more.
///
/// [`raw_values`]: WorkchainShardHashes::raw_values
#[derive(Clone)]
pub struct WorkchainShardHashesRawValuesIter<'a> {
    inner: WorkchainShardHashesRawIter<'a>,
}

impl<'a> WorkchainShardHashesRawValuesIter<'a> {
    /// Creates an iterator over the raw values of a [`WorkchainShardHashes`].
    pub fn new(workchain: i32, root: &'a DynCell) -> Self {
        Self {
            inner: WorkchainShardHashesRawIter::new(workchain, root),
        }
    }
}

impl<'a> Iterator for WorkchainShardHashesRawValuesIter<'a> {
    type Item = Result<CellSlice<'a>, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next()? {
            Ok((_, value)) => Some(Ok(value)),
            Err(e) => Some(Err(e)),
        }
    }
}

#[derive(Clone)]
struct IterSegment<'a> {
    data: &'a DynCell,
    is_right: bool,
}

impl Copy for IterSegment<'_> {}

/// Description of the most recent state of the shard.
#[derive(CustomDebug, Clone, Eq, PartialEq)]
pub struct ShardDescription {
    /// Sequence number of the latest block in the shard.
    pub seqno: u32,
    /// The latest known masterchain block at the time of shard generation.
    pub reg_mc_seqno: u32,
    /// The beginning of the logical time range since the last MC block.
    pub start_lt: u64,
    /// The end of the logical time range since the last MC block.
    pub end_lt: u64,
    /// Representation hash of the root cell of the latest block in the shard.
    #[debug(with = "DisplayHash")]
    pub root_hash: CellHash,
    /// Hash of the BOC encoded root cell of the latest block in the shard.
    #[debug(with = "DisplayHash")]
    pub file_hash: CellHash,
    /// Whether this shard splits in the next block.
    pub before_split: bool,
    /// Whether this shard merges in the next block.
    pub before_merge: bool,
    /// Hint that this shard should split.
    pub want_split: bool,
    /// Hint that this shard should merge.
    pub want_merge: bool,
    /// Whether the value of catchain seqno has been incremented
    /// and will it also be incremented in the next block.
    pub nx_cc_updated: bool,
    /// Catchain seqno in the next block.
    pub next_catchain_seqno: u32,
    /// Duplicates the shard ident for the latest block in this shard.
    pub next_validator_shard: u64,
    /// Minimal referenced seqno of the masterchain block.
    pub min_ref_mc_seqno: u32,
    /// Unix timestamp when the latest block in this shard was created.
    pub gen_utime: u32,
    /// Planned split/merge time window if present.
    pub split_merge_at: Option<FutureSplitMerge>,
    /// Amount of fees collected in this shard since the last masterchain block.
    pub fees_collected: CurrencyCollection,
    /// Amount of funds created in this shard since the last masterchain block.
    pub funds_created: CurrencyCollection,
    /// Copyleft rewards if present.
    pub copyleft_rewards: Dict<CellHash, Tokens>,
    /// Proofs from other workchains.
    pub proof_chain: Option<ProofChain>,
}

impl ShardDescription {
    const TAG_LEN: u16 = 4;

    const TAG_V1: u8 = 0xa;
    const TAG_V2: u8 = 0xb;
    const TAG_V3: u8 = 0xc;
    const TAG_V4: u8 = 0xd;
}

impl Store for ShardDescription {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        let tag = if self.proof_chain.is_some() {
            Self::TAG_V4
        } else if !self.copyleft_rewards.is_empty() {
            Self::TAG_V3
        } else {
            Self::TAG_V1
        };

        let flags = ((self.before_split as u8) << 7)
            | ((self.before_merge as u8) << 6)
            | ((self.want_split as u8) << 5)
            | ((self.want_merge as u8) << 4)
            | ((self.nx_cc_updated as u8) << 3);

        ok!(builder.store_small_uint(tag, Self::TAG_LEN));
        ok!(builder.store_u32(self.seqno));
        ok!(builder.store_u32(self.reg_mc_seqno));
        ok!(builder.store_u64(self.start_lt));
        ok!(builder.store_u64(self.end_lt));
        ok!(builder.store_u256(&self.root_hash));
        ok!(builder.store_u256(&self.file_hash));
        ok!(builder.store_u8(flags));
        ok!(builder.store_u32(self.next_catchain_seqno));
        ok!(builder.store_u64(self.next_validator_shard));
        ok!(builder.store_u32(self.min_ref_mc_seqno));
        ok!(builder.store_u32(self.gen_utime));
        ok!(self.split_merge_at.store_into(builder, finalizer));

        let cell = {
            let mut builder = CellBuilder::new();
            ok!(self.fees_collected.store_into(&mut builder, finalizer));
            ok!(self.funds_created.store_into(&mut builder, finalizer));

            if let Some(proof_chain) = &self.proof_chain {
                ok!(if self.copyleft_rewards.is_empty() {
                    builder.store_bit_zero()
                } else {
                    ok!(builder.store_bit_one());
                    self.copyleft_rewards.store_into(&mut builder, finalizer)
                });
                ok!(proof_chain.store_into(&mut builder, finalizer));
            } else if !self.copyleft_rewards.is_empty() {
                ok!(self.copyleft_rewards.store_into(&mut builder, finalizer));
            }

            ok!(builder.build_ext(finalizer))
        };

        builder.store_reference(cell)
    }
}

impl<'a> Load<'a> for ShardDescription {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let (cont_in_cell, with_copyleft, with_proof_chain) =
            match slice.load_small_uint(Self::TAG_LEN) {
                Ok(Self::TAG_V1) => (true, false, false),
                Ok(Self::TAG_V2) => (false, false, false),
                Ok(Self::TAG_V3) => (true, true, false),
                Ok(Self::TAG_V4) => (true, true, true),
                Ok(_) => return Err(Error::InvalidTag),
                Err(e) => return Err(e),
            };

        let seqno = ok!(slice.load_u32());
        let reg_mc_seqno = ok!(slice.load_u32());
        let start_lt = ok!(slice.load_u64());
        let end_lt = ok!(slice.load_u64());
        let root_hash = ok!(slice.load_u256());
        let file_hash = ok!(slice.load_u256());

        let flags = ok!(slice.load_u8());
        if flags & 0b111 != 0 {
            return Err(Error::InvalidData);
        }

        let next_catchain_seqno = ok!(slice.load_u32());
        let next_validator_shard = ok!(slice.load_u64());
        let min_ref_mc_seqno = ok!(slice.load_u32());
        let gen_utime = ok!(slice.load_u32());
        let split_merge_at = ok!(Option::<FutureSplitMerge>::load_from(slice));

        let mut cont = if cont_in_cell {
            Some(ok!(slice.load_reference()).as_slice())
        } else {
            None
        };

        let slice = match &mut cont {
            Some(cont) => cont,
            None => slice,
        };

        let fees_collected = ok!(CurrencyCollection::load_from(slice));
        let funds_created = ok!(CurrencyCollection::load_from(slice));
        let copyleft_rewards = if with_copyleft && (!with_proof_chain || ok!(slice.load_bit())) {
            ok!(Dict::load_from(slice))
        } else {
            Dict::new()
        };
        let proof_chain = if with_proof_chain {
            Some(ok!(ProofChain::load_from(slice)))
        } else {
            None
        };

        Ok(Self {
            seqno,
            reg_mc_seqno,
            start_lt,
            end_lt,
            root_hash,
            file_hash,
            before_split: flags & 0b10000000 != 0,
            before_merge: flags & 0b01000000 != 0,
            want_split: flags & 0b00100000 != 0,
            want_merge: flags & 0b00010000 != 0,
            nx_cc_updated: flags & 0b00001000 != 0,
            next_catchain_seqno,
            next_validator_shard,
            min_ref_mc_seqno,
            gen_utime,
            split_merge_at,
            fees_collected,
            funds_created,
            copyleft_rewards,
            proof_chain,
        })
    }
}

fn parse_block_id(shard: ShardIdent, mut value: CellSlice) -> Result<BlockId, Error> {
    if !value.try_advance(ShardDescription::TAG_LEN, 0) {
        return Err(Error::CellUnderflow);
    }

    Ok(BlockId {
        shard,
        seqno: ok!(value.load_u32()),
        root_hash: {
            // Skip some fields (reg_mc_seqno: u32, start_lt: u64, end_lt: u64)
            if !value.try_advance(32 + 64 + 64, 0) {
                return Err(Error::CellUnderflow);
            }
            ok!(value.load_u256())
        },
        file_hash: ok!(value.load_u256()),
    })
}

/// Time window for shard split/merge.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum FutureSplitMerge {
    /// Shard split window info.
    Split {
        /// Unix timestamp of the planned start of the split.
        split_utime: u32,
        /// Window duration in seconds.
        interval: u32,
    },
    /// Shard merge window info.
    Merge {
        /// Unix timestamp of the planned start of the merge.
        merge_utime: u32,
        /// Window duration in seconds.
        interval: u32,
    },
}

impl Store for FutureSplitMerge {
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn Finalizer) -> Result<(), Error> {
        match *self {
            Self::Split {
                split_utime,
                interval,
            } => {
                ok!(builder.store_bit_zero());
                ok!(builder.store_u32(split_utime));
                builder.store_u32(interval)
            }
            Self::Merge {
                merge_utime,
                interval,
            } => {
                ok!(builder.store_bit_one());
                ok!(builder.store_u32(merge_utime));
                builder.store_u32(interval)
            }
        }
    }
}

impl<'a> Load<'a> for FutureSplitMerge {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let bit = ok!(slice.load_bit());
        let utime = ok!(slice.load_u32());
        let interval = ok!(slice.load_u32());
        Ok(if bit {
            Self::Merge {
                merge_utime: utime,
                interval,
            }
        } else {
            Self::Split {
                split_utime: utime,
                interval,
            }
        })
    }
}

/// Proofs from other workchains.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ProofChain {
    /// Amount of proofs (`1..=8`)
    len: u8,
    /// Start cell for proofs.
    child: Cell,
}

impl Store for ProofChain {
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn Finalizer) -> Result<(), Error> {
        ok!(builder.store_u8(self.len));
        builder.store_reference(self.child.clone())
    }
}

impl<'a> Load<'a> for ProofChain {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let len = ok!(slice.load_u8());
        if !(1..=8).contains(&len) {
            return Err(Error::InvalidData);
        }
        Ok(Self {
            len,
            child: ok!(slice.load_reference_cloned()),
        })
    }
}
