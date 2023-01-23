//! Block models.

use std::str::FromStr;

use crate::cell::*;
use crate::error::ParseBlockIdError;
use crate::util::DisplayHash;
use crate::CellHash;

/// Full block id.
#[derive(Default, Clone, Copy, Eq, Hash, PartialEq, Ord, PartialOrd)]
pub struct BlockId {
    /// Block shard ident.
    pub shard: ShardIdent,
    /// Block number in shard.
    pub seqno: u32,
    /// Representation hash of the root cell of the block.
    pub root_hash: CellHash,
    /// Hash of the BOC encoded root cell of the block.
    pub file_hash: CellHash,
}

impl BlockId {
    /// The number of data bits that this struct occupies.
    pub const BITS: u16 = ShardIdent::BITS + 32 + 256 + 256;

    /// Returns short block id.
    pub const fn as_short_id(&self) -> BlockIdShort {
        BlockIdShort {
            shard: self.shard,
            seqno: self.seqno,
        }
    }
}

impl FromStr for BlockId {
    type Err = ParseBlockIdError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.is_empty() {
            return Err(ParseBlockIdError::Empty);
        }

        let mut parts = s.split(':');
        let workchain = match parts.next() {
            Some(wc) => match wc.parse::<i32>() {
                Ok(wc) => wc,
                Err(_) => return Err(ParseBlockIdError::InvalidShardIdent),
            },
            None => return Err(ParseBlockIdError::Empty),
        };

        let shard = 'shard: {
            if let Some(prefix) = parts.next() {
                if let Ok(prefix) = u64::from_str_radix(prefix, 16) {
                    if let Some(shard) = ShardIdent::new(workchain, prefix) {
                        break 'shard shard;
                    }
                }
            }
            return Err(ParseBlockIdError::InvalidShardIdent);
        };

        let seqno = 'seqno: {
            if let Some(seqno) = parts.next() {
                if let Ok(seqno) = seqno.parse::<u32>() {
                    break 'seqno seqno;
                }
            }
            return Err(ParseBlockIdError::InvalidSeqno);
        };

        let mut result = Self {
            shard,
            seqno,
            ..Default::default()
        };

        'hash: {
            if let Some(hash) = parts.next() {
                if hex::decode_to_slice(hash, &mut result.root_hash).is_ok() {
                    break 'hash;
                }
            }
            return Err(ParseBlockIdError::InvalidRootHash);
        }

        'hash: {
            if let Some(hash) = parts.next() {
                if hex::decode_to_slice(hash, &mut result.file_hash).is_ok() {
                    break 'hash;
                }
            }
            return Err(ParseBlockIdError::InvalidFileHash);
        }

        if parts.next().is_none() {
            Ok(result)
        } else {
            Err(ParseBlockIdError::UnexpectedPart)
        }
    }
}

impl std::fmt::Display for BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "{}:{}:{}:{}",
            self.shard,
            self.seqno,
            DisplayHash(&self.root_hash),
            DisplayHash(&self.file_hash)
        ))
    }
}

impl std::fmt::Debug for BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BlockId")
            .field("shard", &self.shard)
            .field("seqno", &self.seqno)
            .field("root_hash", &DisplayHash(&self.root_hash))
            .field("file_hash", &DisplayHash(&self.file_hash))
            .finish()
    }
}

impl<C: CellFamily> Store<C> for BlockId {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.shard.store_into(builder, finalizer)
            && builder.store_u32(self.seqno)
            && builder.store_u256(&self.root_hash)
            && builder.store_u256(&self.file_hash)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for BlockId {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            shard: ShardIdent::load_from(slice)?,
            seqno: slice.load_u32()?,
            root_hash: slice.load_u256()?,
            file_hash: slice.load_u256()?,
        })
    }
}

/// Short block id.
#[derive(Debug, Default, Clone, Copy, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct BlockIdShort {
    /// Block shard ident.
    pub shard: ShardIdent,
    /// Block number in shard.
    pub seqno: u32,
}

impl std::fmt::Display for BlockIdShort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}:{}", self.shard, self.seqno))
    }
}

/// Shard ident.
#[derive(Clone, Copy, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct ShardIdent {
    workchain: i32,
    prefix: u64,
}

impl Default for ShardIdent {
    #[inline]
    fn default() -> Self {
        ShardIdent::MASTERCHAIN
    }
}

impl std::fmt::Display for ShardIdent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}:{:016x}", self.workchain, self.prefix))
    }
}

impl std::fmt::Debug for ShardIdent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

impl ShardIdent {
    /// The prefix for the full shard.
    pub const PREFIX_FULL: u64 = 0x8000000000000000;

    /// Max possible shard split depth.
    pub const MAX_SPLIT_DEPTH: u8 = 60;

    /// The number of data bits that this struct occupies.
    pub const BITS: u16 = 8 + 32 + 64;

    const UNUSED_BITS_MASK: u64 = !0 >> (Self::MAX_SPLIT_DEPTH + 1);

    /// Masterchain shard ident.
    pub const MASTERCHAIN: Self = Self::new_full(-1);
    /// Base workchain shard ident.
    pub const BASECHAIN: Self = Self::new_full(0);

    /// Tries to create a new shard ident from parts.
    pub const fn new(workchain: i32, prefix: u64) -> Option<Self> {
        if prefix == 0
            || prefix & Self::UNUSED_BITS_MASK != 0
            || workchain == -1 && prefix != Self::PREFIX_FULL
        {
            return None;
        }
        Some(Self { workchain, prefix })
    }

    /// Creates a new full shard ident for the specified workchain.
    pub const fn new_full(workchain: i32) -> Self {
        Self {
            workchain,
            prefix: Self::PREFIX_FULL,
        }
    }

    /// Creates a new shard ident from parts.
    ///
    /// # Safety
    ///
    /// The following must be true:
    /// - prefix must not be zero.
    /// - low bits must not be used (see [`MAX_SPLIT_DEPTH`]).
    ///
    /// [`MAX_SPLIT_DEPTH`]: Self::MAX_SPLIT_DEPTH
    pub const unsafe fn new_unchecked(workchain: i32, prefix: u64) -> Self {
        Self { workchain, prefix }
    }

    /// Returns the shard workchain.
    #[inline]
    pub const fn workchain(&self) -> i32 {
        self.workchain
    }

    /// Returns the shard prefix.
    #[inline]
    pub const fn prefix(&self) -> u64 {
        self.prefix
    }

    /// Returns `true` if this shard could not be merged further.
    ///
    /// See [`PREFIX_FULL`]
    ///
    /// [`PREFIX_FULL`]: Self::PREFIX_FULL
    #[inline]
    pub const fn is_full(&self) -> bool {
        self.prefix == Self::PREFIX_FULL
    }

    /// Returns `true` if this shard is the left child of the parent shard.
    ///
    /// NOTE: Full shard is left.
    pub const fn is_left_child(&self) -> bool {
        !self.is_right_child()
    }

    /// Returns `true` if this shard is the right child of the parent shard.
    ///
    /// NOTE: Full shard is left.
    pub const fn is_right_child(&self) -> bool {
        (self.prefix & (self.prefix_tag() << 1)) != 0
    }

    /// Returns `true` if the current shard is somewhere in the parents
    /// hierarchy of the specified shard.
    pub const fn is_ancestor_of(&self, shard: &Self) -> bool {
        if self.workchain != shard.workchain {
            return false;
        }

        let ancestor_tag = self.prefix_tag();
        let shard_tag = shard.prefix_tag();
        ancestor_tag >= shard_tag
            && ((self.prefix ^ shard.prefix) & (self.prefix_tag_mask() << 1)) == 0
    }

    /// Returns `true` if the current shard is the direct parent of the specified shard.
    pub const fn is_parent_of(&self, child: &Self) -> bool {
        if self.workchain != child.workchain || child.is_full() {
            return false;
        }

        let tag = child.prefix_tag();
        let child_parent_prefix = (child.prefix - tag) | (tag << 1);
        child_parent_prefix == self.prefix
    }

    /// Returns `true` if the current shard is the direct child of the specified shard.
    pub const fn is_child_of(&self, parent: &Self) -> bool {
        parent.is_parent_of(self)
    }

    /// Returns `true` if one shard fully includes another.
    pub const fn intersects(&self, other: &Self) -> bool {
        if self.workchain != other.workchain {
            return false;
        }

        let self_tag_mask = self.prefix_tag();
        let other_tag_mask = other.prefix_tag();

        let longest_prefix_tag = if other_tag_mask > self_tag_mask {
            other_tag_mask
        } else {
            self_tag_mask
        };

        let longest_bits = (!longest_prefix_tag + 1) << 1;
        let equal_bits = self.prefix ^ other.prefix;
        equal_bits & longest_bits == 0
    }

    /// Returns the parent shard of the current shard.
    ///
    /// Returns `None` for the full shard.
    pub const fn merge(&self) -> Option<Self> {
        if self.is_full() {
            None
        } else {
            let tag = self.prefix_tag();
            Some(Self {
                workchain: self.workchain,
                prefix: (self.prefix - tag) | (tag << 1),
            })
        }
    }

    /// Splits the current shard into two children.
    ///
    /// Returns `None` for the shard with `depth > MAX_SPLIT_DEPTH`.
    pub const fn split(&self) -> Option<(Self, Self)> {
        if self.prefix & ((Self::UNUSED_BITS_MASK << 1) + 1) != 0 {
            None
        } else {
            let tag = self.prefix_tag() >> 1;
            let left = Self {
                workchain: self.workchain,
                prefix: self.prefix - tag,
            };
            let right = Self {
                workchain: self.workchain,
                prefix: self.prefix + tag,
            };
            Some((left, right))
        }
    }

    /// Returns shard prefix len in bits.
    pub const fn prefix_len(&self) -> u16 {
        match self.prefix {
            0 => 64,
            _ => 63 - self.prefix.trailing_zeros() as u16,
        }
    }

    /// Returns `true` if the specified account could be stored in the current shard.
    pub const fn contains_account(&self, account: &CellHash) -> bool {
        let mut bits = self.prefix_len();

        let mut byte = 0;
        let prefix = self.prefix.to_be_bytes();
        while bits > 0 && byte < 8 {
            // Get next bytes
            let prefix_byte = prefix[byte];
            let account_byte = account[byte];

            if bits >= 8 {
                // Early exit if they are not equal
                if prefix_byte != account_byte {
                    return false;
                }

                // Move to the next byte
                bits -= 8;
                byte += 1;
            } else {
                // Check if the remaining amount of bits are equal
                let mask = 0xff << (8 - bits);
                return (prefix_byte ^ account_byte) & mask == 0;
            }
        }

        // All bits were checked without exit => contains account
        true
    }

    #[inline]
    const fn prefix_tag(&self) -> u64 {
        self.prefix & self.prefix_tag_mask()
    }

    #[inline]
    const fn prefix_tag_mask(&self) -> u64 {
        !(self.prefix) + 1
    }
}

impl<C: CellFamily> Store<C> for ShardIdent {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        let prefix_len = self.prefix_len() as u8;
        let prefix_without_tag = self.prefix - self.prefix_tag();
        builder.store_u8(prefix_len)
            && builder.store_u32(self.workchain as u32)
            && builder.store_u64(prefix_without_tag)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ShardIdent {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let prefix_len = slice.load_u8()?;
        if prefix_len > Self::MAX_SPLIT_DEPTH {
            return None;
        }

        let workchain = slice.load_u32()? as i32;
        let prefix_without_tag = slice.load_u64()?;

        let tag = 1u64 << (63 - prefix_len);
        let prefix = (prefix_without_tag & (!tag + 1)) | tag;

        Some(Self { workchain, prefix })
    }
}

#[cfg(test)]
mod tests {
    use crate::{RcCellBuilder, RcCellFamily};

    use super::*;

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

            let parsed_shard = ShardIdent::load_from(&mut cell.as_slice()).unwrap();
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
            assert!(ShardIdent::load_from(&mut cell.as_slice()).is_none())
        }

        check_invalid(|b| b.store_bit_one());
        check_invalid(|b| b.store_u8(0));
        check_invalid(|b| {
            b.store_u8(ShardIdent::MAX_SPLIT_DEPTH + 1) && b.store_u32(0) && b.store_u64(0)
        });
    }
}
