use crate::cell::*;
use crate::dict::Dict;
use crate::error::Error;
use crate::num::Tokens;
use crate::util::{unlikely, IterStatus};

use crate::models::block::block_id::ShardIdent;
use crate::models::currency::CurrencyCollection;

/// A tree of the most recent descriptions for all currently existing shards
/// for all workchains except the masterchain.
#[derive(Clone, Eq, PartialEq)]
pub struct ShardHashes<C: CellFamily>(Dict<C, i32, CellContainer<C>>);

impl<C: CellFamily> std::fmt::Debug for ShardHashes<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("ShardHashes").field(&self.0).finish()
    }
}

impl<C> ShardHashes<C>
where
    for<'c> C: DefaultFinalizer + 'c,
{
    /// Returns a shards description tree root for the specified workchain.
    pub fn get_workchain_shards(
        &self,
        workchain: i32,
    ) -> Result<Option<WorkchainShardHashes<C>>, Error> {
        let Some(root) = ok!(self.0.get(workchain)) else {
            return Ok(None);
        };

        Ok(Some(WorkchainShardHashes { workchain, root }))
    }
}

impl<C: CellFamily> Store<C> for ShardHashes<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.0.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ShardHashes<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self(Dict::load_from(slice)?))
    }
}

/// A tree of the most recent descriptions for all currently existing shards
/// for a single workchain.
#[derive(Clone, Eq, PartialEq)]
pub struct WorkchainShardHashes<C: CellFamily> {
    workchain: i32,
    root: CellContainer<C>,
}

impl<C: CellFamily> std::fmt::Debug for WorkchainShardHashes<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WorkchainShardHashes")
            .field("workchain", &self.workchain)
            .field("root", &self.root)
            .finish()
    }
}

impl<C: CellFamily> WorkchainShardHashes<C> {
    /// Gets an iterator over the keys of the shard descriptions tree, sorted by key.
    /// The iterator element type is `Result<CellSlice<C>>`.
    ///
    /// If the tree is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn keys(&self) -> WorkchainShardHashesKeysIter<'_, C> {
        WorkchainShardHashesKeysIter::new(self.workchain, self.root.as_ref())
    }

    /// Gets an iterator over the raw entries of the shard descriptions tree, sorted by key.
    /// The iterator element type is `Result<(ShardIdent, CellSlice<C>)>`.
    ///
    /// If the tree is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn raw_iter(&self) -> WorkchainShardHashesRawIter<'_, C> {
        WorkchainShardHashesRawIter::new(self.workchain, self.root.as_ref())
    }

    /// Gets an iterator over the raw values of the shard descriptions tree, sorted by key.
    /// The iterator element type is `Result<CellSlice<C>>`.
    ///
    /// If the tree is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn raw_values(&self) -> WorkchainShardHashesRawValuesIter<'_, C> {
        WorkchainShardHashesRawValuesIter::new(self.workchain, self.root.as_ref())
    }
}

/// An iterator over the entries of a [`WorkchainShardHashes`].
///
/// This struct is created by the [`raw_iter`] method on [`WorkchainShardHashes`].
/// See its documentation for more.
///
/// [`raw_iter`]: WorkchainShardHashes::raw_iter
pub struct WorkchainShardHashesRawIter<'a, C: CellFamily> {
    workchain: i32,
    leaf: Option<CellSlice<'a, C>>,
    segments: Vec<IterSegment<'a, C>>,
    status: IterStatus,
}

impl<C: CellFamily> Clone for WorkchainShardHashesRawIter<'_, C> {
    fn clone(&self) -> Self {
        Self {
            workchain: self.workchain,
            leaf: self.leaf,
            segments: self.segments.clone(),
            status: self.status,
        }
    }
}

impl<'a, C: CellFamily> WorkchainShardHashesRawIter<'a, C> {
    /// Creates an iterator over the entries of a [`WorkchainShardHashes`].
    pub fn new(workchain: i32, root: &'a dyn Cell<C>) -> Self {
        let status = 'error: {
            if root.descriptor().is_pruned_branch() {
                break 'error IterStatus::Pruned;
            }

            let mut slice = root.as_slice();

            let is_fork = match slice.load_bit() {
                Some(bit) => bit,
                None => break 'error IterStatus::Broken,
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

impl<'a, C: CellFamily> Iterator for WorkchainShardHashesRawIter<'a, C> {
    type Item = Result<(ShardIdent, CellSlice<'a, C>), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        fn build_shard_prefix<C: CellFamily>(segments: &[IterSegment<'_, C>]) -> u64 {
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
                let mut slice = match segment.data.reference(segment.is_right as u8) {
                    Some(child) => {
                        // Handle pruned branch access
                        if unlikely(child.descriptor().is_pruned_branch()) {
                            return Some(Err(self.finish(Error::PrunedBranchAccess)));
                        }
                        child.as_slice()
                    }
                    None => return Some(Err(self.finish(Error::CellUnderflow))),
                };

                match slice.load_bit() {
                    // Break on leaf
                    Some(false) => break slice,
                    // Add segment on fork
                    Some(true) if self.segments.len() < ShardIdent::MAX_SPLIT_DEPTH as usize => {
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
            ShardIdent::new_unchecked(self.workchain, build_shard_prefix::<C>(&self.segments))
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

/// An iterator over the keys of a [`WorkchainShardHashes`].
///
/// This struct is created by the [`raw_keys`] method on [`WorkchainShardHashes`].
/// See its documentation for more.
///
/// [`keys`]: WorkchainShardHashes::keys
pub struct WorkchainShardHashesKeysIter<'a, C: CellFamily> {
    inner: WorkchainShardHashesRawIter<'a, C>,
}

impl<C: CellFamily> Clone for WorkchainShardHashesKeysIter<'_, C> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, C: CellFamily> WorkchainShardHashesKeysIter<'a, C> {
    /// Creates an iterator over the keys of a [`WorkchainShardHashes`].
    pub fn new(workchain: i32, root: &'a dyn Cell<C>) -> Self {
        Self {
            inner: WorkchainShardHashesRawIter::new(workchain, root),
        }
    }
}

impl<'a, C: CellFamily> Iterator for WorkchainShardHashesKeysIter<'a, C> {
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
pub struct WorkchainShardHashesRawValuesIter<'a, C: CellFamily> {
    inner: WorkchainShardHashesRawIter<'a, C>,
}

impl<C: CellFamily> Clone for WorkchainShardHashesRawValuesIter<'_, C> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, C: CellFamily> WorkchainShardHashesRawValuesIter<'a, C> {
    /// Creates an iterator over the raw values of a [`WorkchainShardHashes`].
    pub fn new(workchain: i32, root: &'a dyn Cell<C>) -> Self {
        Self {
            inner: WorkchainShardHashesRawIter::new(workchain, root),
        }
    }
}

impl<'a, C: CellFamily> Iterator for WorkchainShardHashesRawValuesIter<'a, C> {
    type Item = Result<CellSlice<'a, C>, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next()? {
            Ok((_, value)) => Some(Ok(value)),
            Err(e) => Some(Err(e)),
        }
    }
}

struct IterSegment<'a, C: CellFamily> {
    data: &'a dyn Cell<C>,
    is_right: bool,
}

impl<C: CellFamily> Copy for IterSegment<'_, C> {}

impl<C: CellFamily> Clone for IterSegment<'_, C> {
    fn clone(&self) -> Self {
        Self {
            data: self.data,
            is_right: self.is_right,
        }
    }
}

/// Description of the most recent state of the shard.
#[derive(Clone, Eq, PartialEq)]
pub struct ShardDescription<C: CellFamily> {
    /// Sequence number of the latest block in the shard.
    pub seqno: u32,
    /// The latest known masterchain block at the time of shard generation.
    pub reg_mc_seqno: u32,
    /// The beginning of the logical time range since the last MC block.
    pub start_lt: u64,
    /// The end of the logical time range since the last MC block.
    pub end_lt: u64,
    /// Representation hash of the root cell of the latest block in the shard.
    pub root_hash: CellHash,
    /// Hash of the BOC encoded root cell of the latest block in the shard.
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
    pub fees_collected: CurrencyCollection<C>,
    /// Amount of funds created in this shard since the last masterchain block.
    pub funds_created: CurrencyCollection<C>,
    /// Copyleft rewards if present.
    pub copyleft_rewards: Dict<C, CellHash, Tokens>,
    /// Proofs from other workchains.
    pub proof_chain: Option<ProofChain<C>>,
}

impl<C: CellFamily> ShardDescription<C> {
    const TAG_V1: u8 = 0xa;
    const TAG_V2: u8 = 0xb;
    const TAG_V3: u8 = 0xc;
    const TAG_V4: u8 = 0xd;
}

impl<C: CellFamily> Store<C> for ShardDescription<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
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

        if !(builder.store_small_uint(tag, 4)
            && builder.store_u32(self.seqno)
            && builder.store_u32(self.reg_mc_seqno)
            && builder.store_u64(self.start_lt)
            && builder.store_u64(self.end_lt)
            && builder.store_u256(&self.root_hash)
            && builder.store_u256(&self.file_hash)
            && builder.store_u8(flags)
            && builder.store_u32(self.next_catchain_seqno)
            && builder.store_u64(self.next_validator_shard)
            && builder.store_u32(self.min_ref_mc_seqno)
            && builder.store_u32(self.gen_utime)
            && self.split_merge_at.store_into(builder, finalizer))
        {
            return false;
        }

        let cell = 'cell: {
            let mut builder = CellBuilder::<C>::new();
            if !(self.fees_collected.store_into(&mut builder, finalizer)
                && self.funds_created.store_into(&mut builder, finalizer))
            {
                return false;
            }

            let stored = if let Some(proof_chain) = &self.proof_chain {
                let stored = if self.copyleft_rewards.is_empty() {
                    builder.store_bit_zero()
                } else {
                    builder.store_bit_one()
                        && self.copyleft_rewards.store_into(&mut builder, finalizer)
                };
                stored && proof_chain.store_into(&mut builder, finalizer)
            } else if !self.copyleft_rewards.is_empty() {
                self.copyleft_rewards.store_into(&mut builder, finalizer)
            } else {
                true
            };

            if stored {
                if let Some(cell) = builder.build_ext(finalizer) {
                    break 'cell cell;
                }
            }
            return false;
        };

        builder.store_reference(cell)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ShardDescription<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let (cont_in_cell, with_copyleft, with_proof_chain) = match slice.load_small_uint(4)? {
            Self::TAG_V1 => (true, false, false),
            Self::TAG_V2 => (false, false, false),
            Self::TAG_V3 => (true, true, false),
            Self::TAG_V4 => (true, true, true),
            _ => return None,
        };

        let seqno = slice.load_u32()?;
        let reg_mc_seqno = slice.load_u32()?;
        let start_lt = slice.load_u64()?;
        let end_lt = slice.load_u64()?;
        let root_hash = slice.load_u256()?;
        let file_hash = slice.load_u256()?;

        let flags = slice.load_u8()?;
        if flags & 0b111 != 0 {
            return None;
        }

        let next_catchain_seqno = slice.load_u32()?;
        let next_validator_shard = slice.load_u64()?;
        let min_ref_mc_seqno = slice.load_u32()?;
        let gen_utime = slice.load_u32()?;
        let split_merge_at = Option::<FutureSplitMerge>::load_from(slice)?;

        let mut cont = if cont_in_cell {
            Some(slice.load_reference()?.as_slice())
        } else {
            None
        };

        let slice = match &mut cont {
            Some(cont) => cont,
            None => slice,
        };

        let fees_collected = CurrencyCollection::load_from(slice)?;
        let funds_created = CurrencyCollection::load_from(slice)?;
        let copyleft_rewards = if with_copyleft && (!with_proof_chain || slice.load_bit()?) {
            Dict::load_from(slice)?
        } else {
            Dict::new()
        };
        let proof_chain = if with_proof_chain {
            Some(ProofChain::load_from(slice)?)
        } else {
            None
        };

        Some(Self {
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

impl<C: CellFamily> Store<C> for FutureSplitMerge {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        match *self {
            Self::Split {
                split_utime,
                interval,
            } => {
                builder.store_bit_zero()
                    && builder.store_u32(split_utime)
                    && builder.store_u32(interval)
            }
            Self::Merge {
                merge_utime,
                interval,
            } => {
                builder.store_bit_one()
                    && builder.store_u32(merge_utime)
                    && builder.store_u32(interval)
            }
        }
    }
}

impl<'a, C: CellFamily> Load<'a, C> for FutureSplitMerge {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let bit = slice.load_bit()?;
        let utime = slice.load_u32()?;
        let interval = slice.load_u32()?;
        Some(if bit {
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
#[derive(Clone, Eq, PartialEq)]
pub struct ProofChain<C: CellFamily> {
    /// Amount of proofs (`1..=8`)
    len: u8,
    /// Start cell for proofs.
    child: CellContainer<C>,
}

impl<C: CellFamily> Store<C> for ProofChain<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        builder.store_u8(self.len) && builder.store_reference(self.child.clone())
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ProofChain<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let len = slice.load_u8()?;
        if !(1..=8).contains(&len) {
            return None;
        }
        Some(Self {
            len,
            child: slice.load_reference_cloned()?,
        })
    }
}

// ///
// /// # TLB-scheme
// ///
// /// ```text
// /// bt_leaf$0 {X:Type} leaf:X = BinTree X;
// /// bt_fork$1 {X:Type} left:^(BinTree X) right:^(BinTree X) = BinTree X;
// /// ```
// pub struct BinTree<'a, C: CellFamily, T> {
//     data: CellSlice<'a, C>,
//     _value: PhantomData<T>,
// }

// impl<'a, C: CellFamily> Load<'a, C> for BinTree<'a, C> {
//     fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
//         let data = *slice;
//         let (data_bits, data_refs) = if slice.load_bit()? {
//             (0, 2)
//         } else {
//             if !T::skip_value(slice) {
//                 return None;
//             }
//             let bits = data.remaining_bits() - slice.remaining_bits();
//             let refs = data.remaining_refs() - slice.remaining_refs();
//             (bits, refs)
//         };

//         Some(Self {
//             data: data.get_prefix(data_bits, data_refs),
//             _value: PhantomData,
//         })
//     }
// }

// fn bin_tree_get<'a, C: CellFamily>(
//     mut data: CellSlice<'a, C>,
//     mut key: CellSlice<'a, C>,
// ) -> Result<Option<CellSlice<'a, C>>, Error> {
//     loop {
//         match data.load_bit() {
//             Some(true) => {}
//             Some(false) => break,
//             None => return Err(Error::CellUnderflow),
//         }
//         if data.remaining_refs() < 2 {
//             return Err(Error::CellUnderflow);
//         }

//         match key.load_bit() {
//             Some(bit) => match data.get_reference(bit as u8) {
//                 Some(child) => {
//                     // Handle pruned branch access
//                     if unlikely(child.descriptor().is_pruned_branch()) {
//                         return Err(Error::PrunedBranchAccess);
//                     }
//                     data = child.as_slice()
//                 }
//                 None => return Err(Error::CellUnderflow),
//             },
//             None => return Ok(None),
//         }
//     }

//     Ok(if key.is_data_empty() {
//         Some(data)
//     } else {
//         None
//     })
// }
