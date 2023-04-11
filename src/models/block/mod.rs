//! Block models.

use crate::cell::*;
use crate::dict::Dict;
use crate::merkle::MerkleUpdate;
use crate::num::*;
use crate::util::*;

use crate::models::currency::CurrencyCollection;
use crate::models::global_version::GlobalVersion;
use crate::models::Lazy;

pub use self::block_extra::*;
pub use self::block_id::*;
pub use self::block_proof::*;
pub use self::shard_hashes::*;

mod block_extra;
mod block_id;
mod block_proof;
mod shard_hashes;

/// Shard block.
#[derive(CustomDebug, CustomClone, CustomEq)]
pub struct Block<C: CellFamily> {
    /// Global network id.
    pub global_id: i32,
    /// Block info.
    pub info: Lazy<C, BlockInfo<C>>,
    /// Tokens flow info.
    pub value_flow: Lazy<C, ValueFlow<C>>,
    /// Merkle update for the shard state.
    pub state_update: Lazy<C, MerkleUpdate<C>>,
    /// Merkle updates for the outgoing messages queue.
    pub out_msg_queue_updates: Option<Dict<C, u32, Lazy<C, MerkleUpdate<C>>>>,
    /// Block content.
    pub extra: Lazy<C, BlockExtra<C>>,
}

impl<C: CellFamily> Block<C> {
    const TAG_V1: u32 = 0x11ef55aa;
    const TAG_V2: u32 = 0x11ef55bb;

    /// Tries to load block info.
    pub fn load_info(&self) -> Option<BlockInfo<C>> {
        self.info.load()
    }

    /// Tries to load tokens flow info.
    pub fn load_value_flow(&self) -> Option<ValueFlow<C>> {
        self.value_flow.load()
    }

    /// Tries to load state update.
    pub fn load_state_update(&self) -> Option<MerkleUpdate<C>> {
        self.state_update.load()
    }

    /// Tries to load block content.
    pub fn load_extra(&self) -> Option<BlockExtra<C>> {
        self.extra.load()
    }
}

impl<C: CellFamily> Store<C> for Block<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        let tag = if self.out_msg_queue_updates.is_none() {
            Self::TAG_V1
        } else {
            Self::TAG_V2
        };

        if !(builder.store_u32(tag)
            && builder.store_u32(self.global_id as u32)
            && builder.store_reference(self.info.cell.clone())
            && builder.store_reference(self.value_flow.cell.clone()))
        {
            return false;
        }

        let part_stored = if let Some(out_msg_queue_updates) = &self.out_msg_queue_updates {
            let cell = 'cell: {
                let mut builder = CellBuilder::<C>::new();
                if self.state_update.store_into(&mut builder, finalizer)
                    && out_msg_queue_updates.store_into(&mut builder, finalizer)
                {
                    if let Some(cell) = builder.build_ext(finalizer) {
                        break 'cell cell;
                    }
                }
                return false;
            };
            builder.store_reference(cell)
        } else {
            self.state_update.store_into(builder, finalizer)
        };

        part_stored && self.extra.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for Block<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let with_out_msg_queue_updates = match slice.load_u32()? {
            Self::TAG_V1 => false,
            Self::TAG_V2 => true,
            _ => return None,
        };

        let global_id = slice.load_u32()? as i32;
        let info = Lazy::load_from(slice)?;
        let value_flow = Lazy::load_from(slice)?;
        let (state_update, out_msg_queue_updates) = if with_out_msg_queue_updates {
            let slice = &mut slice.load_reference()?.as_slice();
            (Lazy::load_from(slice)?, Some(Dict::load_from(slice)?))
        } else {
            (Lazy::load_from(slice)?, None)
        };

        Some(Self {
            global_id,
            info,
            value_flow,
            state_update,
            out_msg_queue_updates,
            extra: <_>::load_from(slice)?, // TODO
        })
    }
}

/// Block info.
#[derive(CustomDebug, CustomClone, CustomEq)]
pub struct BlockInfo<C: CellFamily> {
    /// Block model version.
    pub version: u32,
    /// Whether this block was produced after the shards were merged.
    pub after_merge: bool,
    /// Whether this block was produced before the shards split.
    pub before_split: bool,
    /// Whether this block was produced after the shards split.
    pub after_split: bool,
    /// Hint that the shard with this block should split.
    pub want_split: bool,
    /// Hint that the shard with this block should merge.
    pub want_merge: bool,
    /// Whether this block is a key block.
    pub key_block: bool,

    /// Block flags (currently only bit 1 is used, for [`gen_software`])
    ///
    /// [`gen_software`]: Self::gen_software
    pub flags: u8,
    /// Block sequence number.
    pub seqno: u32,
    /// Block vertical sequence number.
    pub vert_seqno: u32,

    /// Shard id where this block was produced.
    pub shard: ShardIdent,
    /// Unix timestamp when the block was created.
    pub gen_utime: u32,
    /// Logical time range start.
    pub start_lt: u64,
    /// Logical time range end.
    pub end_lt: u64,
    /// Last 4 bytes of the hash of the validator list.
    pub gen_validator_list_hash_short: u32,
    /// Seqno of the catchain session where this block was produced.
    pub gen_catchain_seqno: u32,
    /// Minimal referenced seqno of the masterchain block.
    pub min_ref_mc_seqno: u32,
    /// Previous key block seqno.
    pub prev_key_block_seqno: u32,
    /// The version and capabilities of the software that created this block.
    pub gen_software: GlobalVersion,

    /// Reference to the masterchain block which was used during the creation of this block.
    pub master_ref: Option<Lazy<C, BlockRef>>,
    /// Reference to the previous block (or blocks).
    pub prev_ref: CellContainer<C>,
    /// Optional reference to the previous vertical block.
    pub prev_vert_ref: Option<Lazy<C, BlockRef>>,
}

impl<C: CellFamily> BlockInfo<C> {
    const TAG: u32 = 0x9bc7a987;
    const FLAG_WITH_GEN_SOFTWARE: u8 = 0x1;

    /// Tries to load a reference to the previous block (or blocks).
    pub fn load_prev_ref(&self) -> Option<PrevBlockRef> {
        let mut slice = self.prev_ref.as_ref().as_slice();
        Some(if unlikely(self.after_merge) {
            let left = BlockRef::load_from(&mut slice.load_reference()?.as_slice())?;
            let right = BlockRef::load_from(&mut slice.load_reference()?.as_slice())?;
            PrevBlockRef::AfterMerge { left, right }
        } else {
            PrevBlockRef::Single(BlockRef::load_from(&mut slice)?)
        })
    }
}

impl<C: CellFamily> Store<C> for BlockInfo<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        let packed_flags = ((self.master_ref.is_some() as u8) << 7)
            | ((self.after_merge as u8) << 6)
            | ((self.before_split as u8) << 5)
            | ((self.after_split as u8) << 4)
            | ((self.want_split as u8) << 3)
            | ((self.want_merge as u8) << 2)
            | ((self.key_block as u8) << 1)
            | (self.prev_vert_ref.is_some() as u8);

        if !(builder.store_u32(Self::TAG)
            && builder.store_u32(self.version)
            && builder.store_u8(packed_flags)
            && builder.store_u8(self.flags)
            && builder.store_u32(self.seqno)
            && builder.store_u32(self.vert_seqno)
            && self.shard.store_into(builder, finalizer)
            && builder.store_u32(self.gen_utime)
            && builder.store_u64(self.start_lt)
            && builder.store_u64(self.end_lt)
            && builder.store_u32(self.gen_validator_list_hash_short)
            && builder.store_u32(self.gen_catchain_seqno)
            && builder.store_u32(self.min_ref_mc_seqno)
            && builder.store_u32(self.prev_key_block_seqno))
        {
            return false;
        }

        if self.flags & Self::FLAG_WITH_GEN_SOFTWARE != 0
            && !self.gen_software.store_into(builder, finalizer)
        {
            return false;
        }

        if let Some(master_ref) = &self.master_ref {
            if !builder.store_reference(master_ref.cell.clone()) {
                return false;
            }
        }

        if !builder.store_reference(self.prev_ref.clone()) {
            return false;
        }

        if let Some(prev_vert_ref) = &self.prev_vert_ref {
            if !builder.store_reference(prev_vert_ref.cell.clone()) {
                return false;
            }
        }

        true
    }
}

impl<'a, C: CellFamily> Load<'a, C> for BlockInfo<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if slice.load_u32()? != Self::TAG {
            return None;
        }

        let version = slice.load_u32()?;
        let packed_flags = slice.load_u8()?;
        let flags = slice.load_u8()?;
        let seqno = slice.load_u32()?;
        if seqno == 0 {
            return None;
        }
        let vert_seqno = slice.load_u32()?;
        let shard = ShardIdent::load_from(slice)?;
        let gen_utime = slice.load_u32()?;
        let start_lt = slice.load_u64()?;
        let end_lt = slice.load_u64()?;
        let gen_validator_list_hash_short = slice.load_u32()?;
        let gen_catchain_seqno = slice.load_u32()?;
        let min_ref_mc_seqno = slice.load_u32()?;
        let prev_key_block_seqno = slice.load_u32()?;

        let gen_software = if flags & Self::FLAG_WITH_GEN_SOFTWARE != 0 {
            GlobalVersion::load_from(slice)?
        } else {
            GlobalVersion::default()
        };

        let master_ref = if packed_flags & 0b10000000 != 0 {
            Some(Lazy::<C, BlockRef>::load_from(slice)?)
        } else {
            None
        };

        let prev_ref = slice.load_reference_cloned()?;

        let prev_vert_ref = if packed_flags & 0b00000001 != 0 {
            Some(Lazy::<C, BlockRef>::load_from(slice)?)
        } else {
            None
        };

        if vert_seqno < prev_vert_ref.is_some() as u32 {
            return None;
        }

        Some(Self {
            version,
            after_merge: packed_flags & 0b01000000 != 0,
            before_split: packed_flags & 0b00100000 != 0,
            after_split: packed_flags & 0b00010000 != 0,
            want_split: packed_flags & 0b00001000 != 0,
            want_merge: packed_flags & 0b00000100 != 0,
            key_block: packed_flags & 0b00000010 != 0,
            flags,
            seqno,
            vert_seqno,
            shard,
            gen_utime,
            start_lt,
            end_lt,
            gen_validator_list_hash_short,
            gen_catchain_seqno,
            min_ref_mc_seqno,
            prev_key_block_seqno,
            gen_software,
            master_ref,
            prev_ref,
            prev_vert_ref,
        })
    }
}

/// Reference to the previous block.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum PrevBlockRef {
    /// Reference to the parent block (simple case).
    Single(BlockRef),
    /// Reference to both parent blocks (case after merge).
    AfterMerge {
        /// Block id from the "left" shard.
        ///
        /// See [`is_left_child`].
        ///
        /// [`is_left_child`]: ShardIdent::is_left_child
        left: BlockRef,
        /// Block id from the "right" shard.
        ///
        /// See [`is_right_child`].
        ///
        /// [`is_right_child`]: ShardIdent::is_right_child
        right: BlockRef,
    },
}

/// Reference to the external block.
#[derive(CustomDebug, Clone, Eq, PartialEq, Store, Load)]
pub struct BlockRef {
    /// The end of the logical time of the referenced block.
    pub end_lt: u64,
    /// Sequence number of the referenced block.
    pub seqno: u32,
    /// Representation hash of the root cell of the referenced block.
    #[debug(with = "DisplayHash")]
    pub root_hash: CellHash,
    /// Hash of the BOC encoded root cell of the referenced block.
    #[debug(with = "DisplayHash")]
    pub file_hash: CellHash,
}

/// Tokens flow info.
#[derive(CustomDebug, CustomClone, CustomEq)]
pub struct ValueFlow<C: CellFamily> {
    /// Total amount transferred from the previous block.
    pub from_prev_block: CurrencyCollection<C>,
    /// Total amount transferred to the next block.
    pub to_next_block: CurrencyCollection<C>,
    /// Sum of all imported amounts from messages.
    pub imported: CurrencyCollection<C>,
    /// Sum of all exported amounts of messages.
    pub exported: CurrencyCollection<C>,

    /// Total fees collected in this block.
    pub fees_collected: CurrencyCollection<C>,
    /// Shard fees imported to this block.
    pub fees_imported: CurrencyCollection<C>,
    /// Fee recovery (?)
    pub recovered: CurrencyCollection<C>,
    /// Block creation fees.
    pub created: CurrencyCollection<C>,
    /// Minted extra currencies.
    pub minted: CurrencyCollection<C>,

    /// Optional copyleft rewards.
    pub copyleft_rewards: Dict<C, CellHash, Tokens>,
}

impl<C: CellFamily> ValueFlow<C> {
    const TAG_V1: u32 = 0xb8e48dfb;
    const TAG_V2: u32 = 0xe0864f6d;
}

impl<C: CellFamily> Store<C> for ValueFlow<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        let tag = if self.copyleft_rewards.is_empty() {
            Self::TAG_V1
        } else {
            Self::TAG_V2
        };

        if !builder.store_u32(tag) {
            return false;
        }

        let cell1 = 'cell1: {
            let mut builder = CellBuilder::<C>::new();
            if self.from_prev_block.store_into(&mut builder, finalizer)
                && self.to_next_block.store_into(&mut builder, finalizer)
                && self.imported.store_into(&mut builder, finalizer)
                && self.exported.store_into(&mut builder, finalizer)
            {
                if let Some(cell) = builder.build_ext(finalizer) {
                    break 'cell1 cell;
                }
            }
            return false;
        };

        if !builder.store_reference(cell1) || !self.fees_collected.store_into(builder, finalizer) {
            return false;
        }

        let cell2 = 'cell2: {
            let mut builder = CellBuilder::<C>::new();
            if self.fees_imported.store_into(&mut builder, finalizer)
                && self.recovered.store_into(&mut builder, finalizer)
                && self.created.store_into(&mut builder, finalizer)
                && self.minted.store_into(&mut builder, finalizer)
            {
                if let Some(cell) = builder.build_ext(finalizer) {
                    break 'cell2 cell;
                }
            }
            return false;
        };

        if !builder.store_reference(cell2) {
            return false;
        }

        if !self.copyleft_rewards.is_empty()
            && !self.copyleft_rewards.store_into(builder, finalizer)
        {
            return false;
        }

        true
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ValueFlow<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let with_copyleft_rewards = match slice.load_u32()? {
            Self::TAG_V1 => false,
            Self::TAG_V2 => true,
            _ => return None,
        };

        let fees_collected = CurrencyCollection::load_from(slice)?;
        let slice1 = &mut slice.load_reference()?.as_slice();
        let slice2 = &mut slice.load_reference()?.as_slice();
        let copyleft_rewards = if with_copyleft_rewards {
            Dict::load_from(slice)?
        } else {
            Dict::new()
        };

        Some(Self {
            from_prev_block: CurrencyCollection::load_from(slice1)?,
            to_next_block: CurrencyCollection::load_from(slice1)?,
            imported: CurrencyCollection::load_from(slice1)?,
            exported: CurrencyCollection::load_from(slice1)?,
            fees_collected,
            fees_imported: CurrencyCollection::load_from(slice2)?,
            recovered: CurrencyCollection::load_from(slice2)?,
            created: CurrencyCollection::load_from(slice2)?,
            minted: CurrencyCollection::load_from(slice2)?,
            copyleft_rewards,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prelude::{RcBoc, RcCell, RcCellBuilder, RcCellFamily};

    fn serialize_any<T: Store<RcCellFamily>>(data: T) -> RcCell {
        CellBuilder::build_from(data).unwrap()
    }

    fn check_block(boc_str: &str) -> RcCell {
        let boc = RcBoc::decode_base64(boc_str).unwrap();
        let block = boc.parse::<Block<_>>().unwrap();
        println!("block: {block:#?}");

        let info = block.load_info().unwrap();
        println!("info: {info:#?}");
        let prev_ref = info.load_prev_ref().unwrap();
        println!("prev_ref: {prev_ref:#?}");
        assert_eq!(serialize_any(info).as_ref(), block.info.cell.as_ref());

        let value_flow = block.load_value_flow().unwrap();
        println!("value_flow: {value_flow:#?}");
        assert_eq!(
            serialize_any(value_flow).as_ref(),
            block.value_flow.cell.as_ref()
        );

        let state_update = block.load_state_update().unwrap();
        println!("state_update: {state_update:#?}");
        assert_eq!(
            serialize_any(state_update).as_ref(),
            block.state_update.cell.as_ref()
        );

        let extra = block.load_extra().unwrap();
        println!("extra: {extra:#?}");
        let account_blocks = extra.account_blocks.load().unwrap();
        println!("account_blocks: {account_blocks:#?}");

        for entry in account_blocks.iter() {
            let (account, _, account_block) = entry.unwrap();
            assert_eq!(account, account_block.account);

            for entry in account_block.transactions.iter() {
                let (_lt, _, cell) = entry.unwrap();
                let tx = cell.load().unwrap();
                assert_eq!(account, tx.account);
            }
        }
        assert_eq!(
            serialize_any(account_blocks).as_ref(),
            extra.account_blocks.cell.as_ref()
        );

        let custom = extra.load_custom().unwrap();
        if let Some(custom) = &custom {
            println!("custom: {custom:#?}");

            let shards = custom.shards.get_workchain_shards(0).unwrap().unwrap();
            for entry in shards.raw_iter() {
                let (shard, _value) = entry.unwrap();
                println!("shard: {shard:?}");
            }

            for entry in custom.shards.iter() {
                let (shard, value) = entry.unwrap();
                println!("shard {shard:?}: {value:#?}");
            }

            for item in custom.shards.latest_blocks() {
                let block_id = item.unwrap();
                println!("block_id: {block_id}");
            }

            assert_eq!(
                serialize_any(custom).as_ref(),
                extra.custom.as_ref().unwrap().cell.as_ref()
            )
        }

        assert_eq!(serialize_any(extra).as_ref(), block.extra.cell.as_ref());

        let serialized = serialize_any(block);
        assert_eq!(serialized.as_ref(), boc.as_ref());

        boc
    }

    #[test]
    fn masterchain_block() {
        check_block("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");
    }

    #[test]
    fn masterchain_key_block() {
        check_block("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");
    }

    #[test]
    fn shard_block_empty() {
        check_block("te6ccgECFQEAA8YABBAR71WqAAAAKhIPBAEDiUoz9v1QIt7jANJzQctGcLhUBtlENxxQzrOhCdPHOG3NBnhHCR9gZ82qSA4rpOnxhd+UUvx2cd0qIp/or2qjVIdMEdoGQAMCAgABAgADACAKigR9nGzmP8ejgQmAaeGpILtImgOAypbmVkNQNDfHIrqBLkCBCq7mkZA8O8xyfg/H8b6+jQoQlwzoC/CDJFVYiCvbAhkCGQsFI1uQI6/iAAAAKgAAAAAAAAAAAAAAAAAB5VLiAAAAAGPO8fkAAB+IesjnAQF5N6EgBw0GANkAAAAAAAAAAP//////////gUTkn2uouLbDufYZvQyobpAAAfiHqqYoUBeTeiZvys7wWRmdRaSBABFtSHJLtUebY5JkfR9U8zNwQD6K27XEVqgu0ZfOLbulet2Ob4/4VHUpZOxPl41OygrENjWIAREAAAAAAAAAAFAIAhmvQAAAAAAAAAAAvJvRCgkAUUAAAfiHqqYoT//////////////////////////////////////////4AFFQAAH4h6uaTLFFBvP+w19A8NK2Cs5WDGzSYIQX5KGrGxqaYhT46ydf+CNbkCOv4gAAACoAAAAAAAAAAAAAAAAAAeVS4QAAAABjzvH3AAAfiHq5pM8BeTehIA4NDADZAAAAAAAAAAD//////////4FE5J9rqLi2w7n2GZ8/Q26QAAH4h6myBFAXk3ob8FPCVLkLD6y9lcoO8ynetg214BcScCBrGZo/plhvMgaNy3rMvVg9bFzOccDi6TzYu7vP/1QoXZMgfllXEJhZ6ChIAQEHXjyRaJqq3udYcfkUbeJy9W1X6kfy6ds2nZ+TE6GpVAIYKEgBAezENoQ2GF0kFS+yH3t/bxu8nx3ciCVREQcdb2/MOB8PAAECEbjkjftDuaygBBEQAA0AEO5rKAAIACWBROSfa6i4tsQKJyT7XUXFtgAIAqCbx6mHAAAAAIQBAeVS4gAAAAAAAAAAAAAAAAAAAAAAY87x+QAAH4h6yOcAAAAfiHrI5wFOOzUdAAU9DAF5N6EBeSBTxAAAACIAAAAAAAcXrhQTAJgAAB+IermkzwHlUuG24yvb5jr0/8FaryNIU8kEeLIrgfOXtf8NVff7x0YDD2tM3JxGB5w6r46bZN55+lYCdQkP3cFJXxLeR3ILq+NSAJgAAB+IeqpihQF5N6Jm/KzvBZGZ1FpIEAEW1Icku1R5tjkmR9H1TzM3BAPorbtcRWqC7Rl84tu6V63Y5vj/hUdSlk7E+XjU7KCsQ2NY");
    }

    #[test]
    fn shard_block_with_messages() {
        check_block("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");
    }

    #[test]
    fn parse_block_id() {
        let block_id = BlockId {
            shard: ShardIdent::MASTERCHAIN,
            seqno: 123321,
            root_hash: [123; 32],
            file_hash: [234; 32],
        };

        let s = block_id.to_string();
        println!("S: {s}");
        assert_eq!(s.parse::<BlockId>().unwrap(), block_id);
    }

    #[test]
    fn shard_ident_operations() {
        let shard = ShardIdent::BASECHAIN;
        assert!(shard.is_left_child());
        assert_eq!(shard.prefix_len(), 0);
        assert!(shard.merge().is_none());

        let (left, right) = shard.split().unwrap();
        assert!(left.is_left_child() && !left.is_right_child());
        assert!(right.is_right_child() && !right.is_left_child());

        assert!(!left.is_child_of(&ShardIdent::MASTERCHAIN));
        assert!(!right.is_child_of(&ShardIdent::MASTERCHAIN));

        assert!(left.is_child_of(&shard));
        assert!(!shard.is_child_of(&left));
        assert!(right.is_child_of(&shard));
        assert!(!shard.is_child_of(&right));

        assert!(!left.is_parent_of(&right));
        assert!(!right.is_parent_of(&left));
        assert!(!left.is_ancestor_of(&right));
        assert!(!right.is_ancestor_of(&left));

        assert!(shard.is_parent_of(&left));
        assert!(!left.is_parent_of(&shard));
        assert!(shard.is_parent_of(&right));
        assert!(!right.is_parent_of(&shard));

        assert!(shard.is_ancestor_of(&left));
        assert!(!left.is_ancestor_of(&shard));
        assert!(shard.is_ancestor_of(&right));
        assert!(!right.is_ancestor_of(&shard));

        assert_eq!(left.merge().unwrap(), shard);
        assert_eq!(right.merge().unwrap(), shard);

        let children = {
            let (ll, lr) = left.split().unwrap();
            let (rl, rr) = right.split().unwrap();

            assert!(ll.intersects(&left));
            assert!(left.intersects(&ll));
            assert!(lr.intersects(&left));
            assert!(left.intersects(&lr));

            assert!(rl.intersects(&right));
            assert!(right.intersects(&rl));
            assert!(rr.intersects(&right));
            assert!(right.intersects(&rr));

            assert!(!rl.intersects(&left));
            assert!(!left.intersects(&rl));
            assert!(!rr.intersects(&left));
            assert!(!left.intersects(&rr));

            assert!(!ll.intersects(&right));
            assert!(!right.intersects(&ll));
            assert!(!lr.intersects(&right));
            assert!(!right.intersects(&lr));

            [ll, lr, rl, rr]
        };

        for child in children {
            assert_eq!(child.prefix_len(), 2);
            assert!(child.is_left_child() != child.is_right_child());
            assert!(shard.is_ancestor_of(&child));

            assert!(!child.is_ancestor_of(&shard));
            assert!(!child.is_parent_of(&shard));
            assert!(!shard.is_parent_of(&child));

            assert!(shard.intersects(&child));
            assert!(child.intersects(&shard));

            assert!(!child.intersects(&ShardIdent::MASTERCHAIN));
        }
    }

    #[test]
    fn shard_ident_max_split() {
        let mut shards = vec![];

        let mut shard = ShardIdent::BASECHAIN;
        shards.push(shard);

        for i in 0..ShardIdent::MAX_SPLIT_DEPTH {
            assert_eq!(shard.prefix_len(), i as u16);

            let (left, _) = shard.split().unwrap();
            shard = left;
            shards.push(shard);
        }
        assert!(shard.split().is_none());

        let mut rev_shard = ShardIdent::new(0, 1 << (63 - ShardIdent::MAX_SPLIT_DEPTH)).unwrap();
        while let Some(shard) = shards.pop() {
            assert_eq!(rev_shard, shard);

            if !shards.is_empty() {
                rev_shard = shard.merge().unwrap();
            }
        }
        assert!(rev_shard.merge().is_none());
    }

    #[test]
    fn shard_ident_store_load() {
        fn check_store_load(shard: ShardIdent) {
            let mut builder = RcCellBuilder::new();
            assert!(shard.store_into(&mut builder, &mut RcCellFamily::default_finalizer()));
            let cell = builder.build().unwrap();
            assert_eq!(cell.bit_len(), ShardIdent::BITS);

            let parsed_shard = cell.parse::<ShardIdent>().unwrap();
            assert_eq!(shard, parsed_shard);
        }

        let mut shard = ShardIdent::BASECHAIN;
        for _ in 0..ShardIdent::MAX_SPLIT_DEPTH {
            let (left, right) = shard.split().unwrap();
            check_store_load(left);
            check_store_load(right);
            shard = left;
        }
        assert!(shard.split().is_none());

        // Try loading from invalid cells
        fn check_invalid<F: FnOnce(&mut RcCellBuilder) -> bool>(f: F) {
            let mut builder = RcCellBuilder::new();
            assert!(f(&mut builder));
            let cell = builder.build().unwrap();
            assert!(cell.parse::<ShardIdent>().is_none())
        }

        check_invalid(|b| b.store_bit_one());
        check_invalid(|b| b.store_u8(0));
        check_invalid(|b| {
            b.store_u8(ShardIdent::MAX_SPLIT_DEPTH + 1) && b.store_u32(0) && b.store_u64(0)
        });
    }

    #[test]
    fn proof_for_masterchain_block() {
        let boc = RcBoc::decode_base64("te6ccgECmwEAHl4AAqXDAP////8AAAAAAAAAAADINkw8ILvPHAX2S3uxcpm/gsFm+1SOSeYXqu1Nt0iIygjJGrcq6vD5ygwz1VWTq+YAQy2Q93VP7BNtiVwYGbewtug9wIUBASsRGvRflwADEWMAAABCA+2djTT/LrnAAgICyQYDAgHWBQQAwT0aL6sM4nAThCPc7T7rRFm3/NoqIKAV/Y25iSVwXhhVl52H+DXRh2ouL0GCziLloP0MNW4TfSo/D1yW5hVMrXnuLmktRsOfeqjusOsUHPJMdqEMYuhBKAHVpy6R+YiJwDYAwQxaxnqojICltzeM0U+QItHDyC/nYUGbL7xR2Yedl4fCVR1XaH+FHODBDZZSft2kM1uYIjfg7tH1WlINB2/uPzgvWY9vqp3fA++bS2n5ilhE637ivIOzm8MfaHkRu5GsEBoCASBGBwIBICcIAgEgGAkCASARCgIBIA4LAgEgDQwAwRw1VLIvdsbmu/qrvcMI960aiibqwC1VARMzqNMdJGQTl8sB/Fd3UwZiQwjt68hGNNvmaATsdaiGW4dFr/ebP6vnwIpXAoKekeVBmaMqq5x2U7UvZisdJaBw0muC6Dzq1DoAwSeIfjdB6ubXXkRIFm4nzvO7AV5IaS/h/VybSNriCxE5li1yL/YWSs+16TSAudjy7ehNVBDpjY/4Q1h/Uz478CQsCc/QgsdPAv79bGZlrWfzKRMRnE0Vj9i3uoZIvze5MDYCASAQDwDBMSWtRJ6AiAofoZ24DTq+cl4hGR0q2kUeTFc11zi5vOOWuNJie1TJEUp8r1iJBh0Xc3f3Z53EMmyAJ4uXFcMWo152RBqaydIratPgTccYRLvedMdHa0vaqjbMWjE0VpIQKgDBNsFTrEU5mAZxGH/9j7RYKbKZpKCND61s0JIo8nTs5A+V/+0eIlq2Hi3vMkzcyO4g6mvE1qL/zbSFieATewbym50PnY9PUCC5iVW43R3PgXsfb38PQYMzIBcwomc3k5D4NgIBIBUSAgEgFBMAwSZISlyiv16Vd2HYqyjh8Y/g+X8tX0HG7eGkfC/cFVjdldqmiz5mwM5eZIpPHcNE5WRcdlnVk4QiY5SRDmDyTv+vzlCSSeFYUOZiPlRm3GIbIA2qfkJ+NHmTPWNDoytofC4AwRKLbwU4cEAVV4JVJP7N2XqADEQmKJ75OirZPqLaiSAVVD/0b3/G9J/aE6mtEuAbrkMD5NnFL18CXgGx09XeD1wsQkGbxu+bLPG6Tl7v3V+u3CIIklx8ZeakOWfiA7iLiDoCASAXFgDBBMGxisiFNGZ0CqUiZiRpCUQ41SAvTknfemLQ0W9sOpgXhT8Ca1MY3pz/HIUDKLeeTIVQ7Sxo5PBkHWYjGKqzXKnviLwBiTXraCelfBnRb4vbXD10+rnok1OzaCowfKKQJgDBGAPLdZz1DIt9MVNe8VBXPYcZK8mT3DlQmDbEEkbnc0OV6XM2La+y+zV7oq6jDL4vbJi6RZzv3tK9V4C6fO3XaaeNvsn1P9rj0Hv7LKyGkwbafTevxZamxwGJwKhTKwMkIgIBICAZAgEgHRoCASAcGwDBCqptTO1LzgCz7MEyl76B4KQKylZwPlyY1I/ABUvqysSU3eFS1NHYrjhpCAbGiLfBhcUC1dtxc2pZ8yt5Z5XwOKAcSDM2eY9A8xSY5Rl0avI16x+hDFG5oBx9lY2gQ7hsMgDBFlE/8vkdUKu1rYfBlN50apNeb0GRRm/OH4l/AbAIguPV6qrz/jrVNep3Hwj5Me2Vke88PG0UkbiWd5X36S0CrWr9M5EmdHBmA0HxplGPkceXTBweFPlZS5LuJSO72odwJgIBIB8eAMEW/q1dC+BABeOn+OaV4FIn5zpe4hvVXHdC+mcx5zMzw5QiNOhP7YorKiFkNPLFNwxieYst5xGP2jb2Z3cZFbpCi0SoI8MHQUXs+o50ycFaFohxnlZWIy1Jh8EYciuozDAWAMEGhWEIHwrwP+Fj4oxf58HHyWGK/pZrzhuf3I2+AFtQiJUL3O5mrczenh8lBperwme9kjrNQyIKbBDvK78Kh+PfJJas6/mc8Zvzm1BsHHzqUyKsF0/blHuj3BF/hIbmfygeAgEgJCECASAjIgDBGnOvmPK5POBM9ckpIjeFq90uciAn6Iw4lskyB0Lo1yGX51DjCHOMo/aD7S6OpLQJxNhDk9OUxaegRGVVjtE1JuwUigy8tz0ibUcucIHB/PER4WJwsyXV30ohIxw/jmUUAgDBOC3tZS52Mhpbar1hX+rhWozZvH1UrKRpbTFnCzlmpp+XnhANbSqhGr9d/1ALqwl2GtqLiDt7L7BjvajScVsxOzu/jT1EwIC5h26Ub4nhIRTGEdlXehVqPui3BKX3r1OAOgIBICYlAMEy+CBP8Qad47rP3wzJbfKxr5pLEhgrjMpVQ4XyLBULJpdrVOSp92unja4kN/SJQfcmEUuRo2BFjiQRSQdbCkmO7s0wpWxS50ubq3biGkkLfaGNPXDF/3Sy/PA//IKUQpQiAMEngRd5sZjhac786nnmmZpvIgr6kwml39DCOqOeTRtjPZcyaQ+r3rao3PFYhe0z+qgTeSMqFihBnBHoSPB8Jq2bVVSxwHSwpfozOdX3caG9elDTgK5kPPi7oiI+WhsyaGAiAgEgNygCASAwKQIBIC0qAgEgLCsAwR5weJxx9zVoSv87QP5UtMlZNidg7frWu3vIAiXFQ6Vb1r340vLvEWgMV+q83f5nGCjqSXaIPhAWNahVpDOXtGvRzIL+BYu6rlJ7iorTgGpR3xbrY2FpgkaMdDNK/5EmODIAwTyIGaMj5O8z+AODXontviH936HYEvqdk0XpFc+AuVec1Y3AwQHq8QV06rRB3ENvvxzoI1arJoHeGiA69GgCq3OMZw1CkrxTAnjKnSIPt5BlhxP/Wwi130pi1qpQtzb1rCICASAvLgDBJ2VHk90K0rr8QvUehUiSq11HzChsDZEnhpPjjHv+8zRU+xlXndlw54SfylHEraCnb7Ms9U9Tuf4GGG2K+8zOegx1YheFIXHzASAO/A9gzw3/X2l/KgzbRQNO4iesendEDgDBDnJLusBpTTn60YmuTSkl1J98xsYKmJdVp5swlnrwWPJXM9ZuZE5Mfaocj0jrcvmximpjnd3hbwzypm8l48/KfJ8B3oqS9F5LYE486OpwYtRFQ43blzP1+5ZFhkpPLuiIGgIBIDQxAgEgMzIAwT2NpKG3FZzf3f4hH9urOcyXJK66gNeewnGcfAe3NAmrlLVT2E2D8/iIuFwlpE5pOqXKBTabEza8ick6Ch74fxwVBF28hZca6VBivtiWQzlzmDG4CjjfR1eRXAtm/AXU7BYAwQX4FVaU3Wod2eJYFXeeLzL/FvUttH5qZ77FBHvB7XYaFFCUB87zI0y1LcCzUX/3YlHyJNO2dMp8sR5f1iUqAYV+NYmFprcw9Vkt95SDZt/3+rQOHv3R65sxXK0mIXB1tBICASA2NQDBHbxmgEyPd0qh4sR8HC+3hfcQJEIvvUXGDZd8+2zjC3SWuOGCvf6x5ccDcwgAO4vP1mLZb0Kef33olk9MQnuDAJnc0mKfAXcB9wv3nv1zcpDyXs3TnnHnU7P+XtwlB6JQHgDBE9nU3xYxQIteUuAtx2HAsJjh4QLlVi4iJUHuikvg+IVXOB5gmQV4nGB2sz5JMocI2/MoOxbOE1zYqHldxDMCe7TpVPJy/vNE5MVk09fCFNZSV7apJFYefINSK2zNuaVEHgIBID84AgEgPDkCASA7OgDBOEGOsFA5yiZZ6Utu/jP+Ivbe5tVw1ZHunf4LSII42vnUuFzhXwkCtdkfUX7zCzopSmM2v2Qio9NTBJNxHsw+o0z9k9fM+uEcdfU5R+HdPlklL25yBE9x7NPAIFQlImzoMgDBAc0255SeSJNiIlwCtMa17P7O4er7PLhukZNgSiEKbcIWLrr1F3sEgLLpdDs118IrVDUlqhjDdZYcLAtvMxtb1jHzi9hxrvo9FCXfsoDTYODGdIQeubwBrCJkJ/sb7nb0AgIBID49AMECabJgxwZDDBGKYDenoxeiffcfiFgsSo+r8pg36pWmMVR2JTPXGKzg0QmKCwMd/w8Nz+YCXzrX3h9whLkk7xE4p1OSv9bujV7AhysKjyE13edy+7XFIxM3K3UKyEdc3SwKAMEv9PpAYmkwRChYfKbGoEzt0FBTQALotATGfXtFGInl95SSyZNkAAaNnkhNJyXjAtlmG+JyKB2AzbWvu5jLFxOqdGjw/ukYBT333y4aQ7lUo+UAhefFBtaRPrlPkmWGYuQCAgEgQ0ACASBCQQDBBZqXJFLT8RAYe5KOrMcSNeGHo0JvuaShrEzQL1H6LOEXE9qQNPv4DS5vxR1ToBmv7QpntgbV9u6IG/eTBKHWnR9LSCNrKIqKG7U81VSthRKvgN8RoWD+PQyHWzwGPGt8AgDBESozwOiDGM/zxjSd78MaNsZkhSRib91xsdTGQhEg8JMVcDYnRi2EKU8vhsil/13p8yzLIi/c8OnypHGt6S+0yDUdXSThrBnPtBpBZxSpyWoHXedmU0JwOG7qMI2XyQfUEgIBIEVEAMEf/ioe2/ge6ImhNlS8PnlYd5YfaTy5tdlnztTb41RsylUYTc1iwQaWZWLuBTxJA8Qm8XWLmW4YJ+XSJw1HfMm073XP++g+4bvOOhaocGKnYUOP6jFGzjMP90TPTgf8gBAiAMEHnW9ymWX0/b6j4ydZ5iyZpfsnlF7DR8rivP5mUi2a4JYmYoCzb9l9rTZpSQm7ONRRmjzXrqa/iNtDegG2EXaz68y6qveD9w//cVTa75Nqw0P4lvl9cwWun8FUy8/EpUwaAgEgZkcCASBXSAIBIFBJAgEgTUoCASBMSwDBA39DnZ8OPrkpt5vfFcRw/J7Zrv1ujXQ0AVV/GEbw5LUUQyWbKgSW4gLWFt6HHax3XuZ5DXPkMz+hg6W1BglobqYpsBIfNWwHHlqEuNDwZBpcaKDXb+j7B4iIG6svrSZYNgDBNJeyVoeauAumL9b730+Q24phhL6QcY5NR9HlcRy7L5nVRqrRIpqFPSu70Y5Zdehy+HrURBr0A26TZ2IKAhaacZ4rdwbdM6mxD1vB6wDBf3J26LUVqN+fD4ojrCbHaWF0AgIBIE9OAMECLGnIxorxIaxw4jxCNy1/bBlLFo0VHv/ShNxuXZvV/df8NaNklIKiNxS3zS6oFhTVSLEIU3l4Yli3VEDE/sVPI3HIhuHwHLw94F4npGLaOZAai0POs+q1CSMqn4h2aNwqAMEhfWge9Zzn4jJk0v5V7pdglyuhZu8OCagS5ZD3Wl0ra5Rsat/WHeoLdsYy+aCRBgxVHRzZP2TQkoqN6DayJSEySaCnxBEEGgPXpmNTxp/2W/T4qLOSQtYj7Q6rhQUgprAaAgEgVFECASBTUgDBMXepR3RZmF+4YSeKMapqddt3DofSSqYOL+ZhTAerpkGVY77eYwMg5n2iHj4xDTHe0kdWCB/pw46iZyLxBq/BHLAIY3W8Qv8v/kOwmK+ayiHUUCB8iIUKSI1Odv/QT4kkIgDBI/pExccgRNpNOIWvE/9m2+K3o3xGLiyhR/08i+HArIuUpPiMV8gQEX6nzm7lX6lpbleXr0PUCDYpLr68DI9x6u75syi+oPpo72C35GD8dE1HFS6iVtuAmfCykNMErb8UOgIBIFZVAMEqMoD/1Q5Qz7EcYjxLOKDJtOsR8sMGXGTH+2NNe+jnDhdale2sj0iy4b1ghPWYriy3BPgkXf9DOQOzdYB662fmq+uWB3UiHeVAlnB6EqE5QMKSlPcRGChbWjcv0AwOZvAqAMESG98IjnLXi05+V514eY7yCVSTgVbDPSOUz17j0E52uFQX2rnOP8JF/t38DaW667aCeR2jcya9HZwcZ7VI7+MPR/ZLUBVgwdrfVMlGzGx9fGrvHVWy80/I77t/FqMx7vwuAgEgX1gCASBcWQIBIFtaAMEZ7SVInNWrDQO4rnE/3UHZR18lvtJ+jkNCCJp3d6enuRRy5oxOi4Mlxt5IS0VGjXHgYkCRVq7o+CMG29qLpgr7WofK+EXllFLhLRfMAKkei4HaBI50ZpzUwzCYsxiPpygqAMESR9aDhwg+zKvA8rp+PlwEXSF6Yp2YX9JlbwcOg5R+3NaWpRpkpm/n2PUqGNaxPjxjtO0U2qY6vASbLw99lFCPK8IuQ4j+3FZHu33bQe34HLpmxBetytPIRTQqNlbbPMwKAgEgXl0AwRja7nRFvfBFJTZimrpy4OuVpzEyBxvDooV6SM0DrTIlVGCMEw01K2l34I/8CeAx4NnLLEOnruypmcEaebAQwRAvvmdj/3YGyEACG89CW20ykR1tyBgI9QQsKfLlXKiGtDoAwTRuZjYkPWC29qJnNMuaIQeJmymuzfgDqZ7k63FuEAF41ke/9263wIAHs6YS6UevaT0cdXRz6wPlw5CD725bfeurRT6beZuriDe0LbEV/W4CKalbuTPguFXueHF99pL4zCICASBjYAIBIGJhAME2Zgb28bLAG+HpHzjivESw4MrDXOVxBye+Ne2xjwUq4BdSh86KZVIuFPFgGZmKD+b2DQL20TeClfjVaBlWOTSiZTnVM2Au0FIE6oNkS1GLfJvr5KuF73HqJKwV2xG2jMgSAMEgzvDtHMK7UaLUKrsXmnjGkbQyn0UHy1L+7Jd6pb7Z9VU+yQbRSVVo8+NfABhIZy2NMm0mlfIuyKXYo1o4JoTuhCyB7XYxPP1k7WuLnOV7tcBYrpAuYYZOESo06expc4QuAgEgZWQAwQUpWX0KGF5VOEWv7TdcrwsFfPKoawJGRhaZsMabDMRfVL8YX0Gza0EYcHH0fnLDh1aZsE6TDgX2j1At8n2k/Y6UPx1oFRNAzYpxq2PnSxe3p42vEub8IV8LXcTqXm6V/BIAwTHjZiIpkXZ1sKq1P7MZfJR58CmQw79TNV0GanqFBWYy1PbjIm8p0hzKwE1Sb74THBRzDn+OXI0RSfqnpacnvfcAyGu7q7SSIokdTUO7EaVvk+BsBX4dD8bXfcxlSrWJUD4CASB2ZwIBIG9oAgEgbGkCASBragDBPUBYhIiEwKY61adQaWF4uo3wGmVDG3aJcFmDknfjX/wWdqLbdU4p8Pd64g1gLn7DiW2J6+jE2pxEiy5OwZxxSn38q4YO1z9QQj56ekQuIu5r+uIDDRzicAJ8TRbcLpbkLgDBA8BlhPxa8NQykMr12WZYzZlkuVBSMAzK4E4uB81BHjbWxVFFtMM6Zw7RtpeDiogBIYmx3UzTrDu+EYbRXxNDJ2Vnh8m4WHSah+FaD3Rc9WrlLPwz0RGpyROi2/fC9hS8JgIBIG5tAMEs6K/tYahosyu3oMJ3bExb7+JAXEqS0dN7SfE3HvZxvdRIYdz1HRUB0nGi9l1YuEXjyq/a+IrppJUdToZfZT+BHPuz665nx4QPfsawg7AkBnBXvyFk1ygOg9r8JMRAUVAeAMEYr3Fkt5n92el3OHvMl1Bxg2xBIxEzoOTZYjY2T4HD/9UOFeCLmkYAxFO8aQ9iNaz4h0xl1KfelB14gkTQ3ByxvSrBKsOfwPnNxNl1yd6cYON7BJWS0uon22/J5AiBzgQ2AgEgc3ACASBycQDBDR2F/giMdoO2BVOEALZLikTubeu/PPLeFTYLDTQtYpcVAuHQiJ4ssvF9Xk0wyfMHLBoqoOpc2+BxXMU1PU9J4AL+DtB0WotVA63vasbhiD2fpCigNG4pmA3QDaOPjuPMCgDBK4lj1DZpoNuQhN0HYX+ZB7tcs6Xfhkqb5GGd2UWPMGUV9EhSKKaWASFEe0/Wly105QG/fNRyLb+PS2Dw3j62F6eF95miGHUWLx2xVPfeKGjkGuKCIOnKOgo+1HTFUyuIJgIBIHV0AMEZi+GCUZow8ldsJPZ6SwcZJOALxVFpJBLSViLfMqe7KNaQj1Qz2UeraBtHBQg+Xn7Z52SINVyaq8/9R9nlfjfC8b1wWxYs8OMB6mIyHuItFEG39uN2G+XkI/2JUVHSHqAeAMEpGxf/VG8od02jS+v0uhEVfeQsoqmrDhThAcbZCEeaFVWGoZWkA/zCK7PN5bx9HnFwlTk4AS7c6PKYK56N5Z+XcCgm5nFLOuC//tBTXSCWi1pcqaRcpXeGtfxXymkXFgQqAgEgfncCASB7eAIBIHp5AMEOHPHQwnls9oNYbd0jiMx2M/9B34oztyYhwrlj8jKzUNQS1eEK6Y6BKoeBIXIrIv+OcUDxiczYG9NLNx9QSPe8A8mthAe3ayvkJNV/k0DcnlfbAiXMFq/+RZ7C5qR67SACAMEOrPECaulWlALU2un9H2SZFZzCm4poido58Qfb/HKrFFcXFJO+GA9xxih2nOgjnDRk5DFu/JDy3J8GA5cxYM2loFqx1ZDf3IESPZqA7yK6Ly1qzbHv93yef91Kss4CP6g6AgEgfXwAwQCH9OOKu2E6f6bf5Nv6Q9yJOtOdCnMqTtLuGw8DAcINlKHwmvAHLCDgpUvPR88EzSSBs9kGEfQ4RQZfzZ8nx4H4Onlbmce5Uf7eQVESShHS4AeCcgtnOp3LAI3VlVyVhDIAwT51dufWrgVCtOn1OlXlenuyPpXFaiKE3E3pvpOlvPS0l/o1ximKWuMYjpUPbDcWQBD06vHeFu1DAWm/vgVcQHoyo9leC1lOxOSgLskq5SoqoR+Eg+JxKaGbhm/N57l2VCoCASCCfwIBIIGAAME2693H8ivEIX5/0VNUbR8C76RjWYpOGI5mouAFMMWNtdUPsyD5N8ZBVB+8fqHDHvQzt99GWBMxzDm5A+XvKLbaIgoS66BbpIphFk7L3NuvJ0eEDIoDiyiFCORcN0llQXgCAMEljGlWcwTMlxxTM6DMewCtXGAWqWNyuJBGbAvBd3HL2ZfAsa+keVzPAYn+U5DCfDOD7ahXagsdrXrB9XLZ+xWla8i4clyaJbFnFmAhX1x93+G8M8ECUNiZrywMNXfuAewiAgEghIMAwRH5lXKsbyasl3VavQtG82o6QuoAStdzVvS0pOZeCUZFFTO2GZRLBOHK2qR1vxP/WFVYNUUNyR67frsInThMA/nD07YwyB3PrJ952DJ99+KTvYVJmzerR0E80iTxfU+DyA4AwQrLeFq2hr4UqOLSFcd6L5YHv7IwuSaU714Jsj/7nQT+lgh00X9IM3midmsTgjl5LWgh12X4vrfDMVBAiKGHxeD+tTmx8Mg9v9KxWX35o7h6lpLO+G4YGn72OJDsqaOC9CIJRgM8ILvPHAX2S3uxcpm/gsFm+1SOSeYXqu1Nt0iIygjJGgAUhiQQEe9VqgAAACqZk5CHJIlKM/b9tBy6SCQ0oVaaYv+RWPnaGHChExyMZkbtHaR3ELhDWkeP5SvVGRFRxvov2BtO2Tzqtv8gzKUq0momBJafdntzT8CPjo2IIxfMpWjPybcORKgXyASMi4khAVCKKEgBATyNm/LTpUnnjS2/Ee7BjlvgkGSX1d3RU3PSgaAFCSdBAAMoSAEBel59KEePqzHT4qrxGeZ2qJPnDRo+Kx8IM6Db8VNlJ7gABChIAQH9IRNmp1RRbW929Naozo3WQUaG2vSrz589zdZzk69bZgAGKEgBAamxUJXw2x8pF0GjtOxlM811RHP9PFfCkCWQbdwvQ2wIAAcAAQIoSAEBxdvjVpavFw2pD3ziiEcpytJfBJAuDi29kriuFpgjWdYABCqKBN/Xvy7VEQb38uJWJd1786QZbxOI5SBNK/6+WVnvd1URFPabniG1YcHYBj3Q4HKSieFCfftBFM//iGVntc5dJuIAtgC2kpFojAEDFPabniG1YcHYBj3Q4HKSieFCfftBFM//iGVntc5dJuKYS1M0NRoNEtyZce3zab7TLvRBVfva1NnVNlUnbKKZDQC2ABJojAED39e/LtURBvfy4lYl3XvzpBlvE4jlIE0r/r5ZWe93VRGNsffnoDVbP/DwPj3C0i9Rq8pm+ekG0zUjEXgWCz4niQC2ABICEbjkjftM04zIdJWUAB1Gfk24cmacZkORlU/EAAgCJYPWLe26f4fdvB6xb246mKUxQAiWlgIBIJiXABW/////vL0alKIAEAAVvgAAA7yzZw3BVVABoJvHqYcAAAAABAEAyDZMAAAAAAD/////AAAAAAAAAABhtSHHAAATn/tPNUAAABOf+081RBr0X5cAAxFjAMg2SADIA7XEAAAABwAAAAAAAAAumgCYAAATn/s/8wUAyDZLu6FUXxwS5CsRZc+yCn2mE+EacrJ5Akq5mddxgwuVcopQTyilJcUerPdpsV2x7M7lkS5XzIZ/R0kEduNV2Nu+9g==").unwrap();
        let proof = boc.parse::<BlockProof<_>>().unwrap();

        assert_eq!(proof.proof_for.shard, ShardIdent::MASTERCHAIN);
        assert_eq!(proof.proof_for.seqno, 13121100);
        assert!(proof.signatures.is_some());

        assert_eq!(serialize_any(proof).as_ref(), boc.as_ref());
    }

    #[test]
    fn proof_for_shardchain_block() {
        let boc = RcBoc::decode_base64("te6ccgECDwEAAs8AAaXDBAAAAADwAAAAAAAAAAEndRPGh13esYv1+IiNBF8d0E4W9nAxxWox0/9dfbYfzbMNf7BAsJFC3f6OXhNcq+C1Z/dy9rq/xPVHxMsxSz9swGhTQAEJRgPGh13esYv1+IiNBF8d0E4W9nAxxWox0/9dfbYfzbMNfwAEAiQQEe9VqgAAACoDBAUGAqCbx6mHAAAAAIQBASd1EwAAAAAEAAAAAPAAAAAAAAAAYbUjQwAAE6ADeamAAAAToAN5qYHbMdUdAAMRZADINqwAyAO1xAAAAAcAAAAAAAAALgcIAhG45I37QDuaygQJCiqKBATDffPjKveSZSYvtkZDpIzT+6RfYUrlPaItUrZS8V7HQaP1v/aOVl4LiMM8qu+JUek2p0uQuIHV4AaCN5mrVOwAewB7CwwDiUoz9v0ZQGFiq3f3DnYsuIgizbBpIte2d8WchEzwPiE3cn+PRhRnl9e52rlFK8AWPE59DDMfnMn3HEPFdaM6B7NN0/8dQA0ODgCYAAAToANbJQQAyDasn3vQI1cAvX7TsH6cpLNG/Gcli4REHLB9gYLvAY1RwRThGBO5s7HGv5it3cNwmlhKe7UHYRvZ3j852Y8MYel2RwCYAAAToANqZ0EBJ3USM2ZQuOyJ2K6GEos4at5g1bubtGURZk8RVDYd+S8wz4JIJyFKVPraOO4qeN3eYmJwv1rg2zn+GEDcpFrl66En0AAlgEruBB2JoVR0AldwIOxNCqOACAANABAO5rKACGiMAQMEw33z4yr3kmUmL7ZGQ6SM0/ukX2FK5T2iLVK2UvFex1tvG3oZaJke0Zq49+C17SaNZRZFg/fTM2Liga2R2p8fAHsAAmiMAQNBo/W/9o5WXguIwzyq74lR6TanS5C4gdXgBoI3matU7NxzJDjVef2kcydRvYGpPaaQxMZu1+tYTs5aS6nT9+8bAHsAAgADACAAAQI=").unwrap();
        let proof = boc.parse::<BlockProof<_>>().unwrap();

        assert_eq!(
            proof.proof_for.shard,
            ShardIdent::new(0, 0xf800000000000000).unwrap()
        );
        assert_eq!(proof.proof_for.seqno, 19363091);
        assert!(proof.signatures.is_none());

        assert_eq!(serialize_any(proof).as_ref(), boc.as_ref());
    }
}
