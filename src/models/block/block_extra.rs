use crate::cell::*;
use crate::dict::{AugDict, AugDictSkipValue, Dict};
use crate::error::Error;
use crate::num::Uint15;

use crate::models::config::{BlockchainConfig, ValidatorDescription};
use crate::models::currency::CurrencyCollection;
use crate::models::in_message::ImportFees;
use crate::models::in_message::InMsg;
use crate::models::out_message::OutMsg;
use crate::models::transaction::{HashUpdate, Transaction};
use crate::models::Lazy;

#[cfg(feature = "venom")]
use super::ShardBlockRefs;
use super::ShardHashes;

/// Block info builder.
#[derive(Debug, Clone)]
pub struct BlockExtraBuilder<T> {
    inner: BlockExtra,
    phantom_data: std::marker::PhantomData<T>,
}

impl BlockExtraBuilder<()> {
    #[cfg(not(feature = "venom"))]
    /// Creates a new block info builder.
    pub fn new(account_blocks: Lazy<AugDict<HashBytes, CurrencyCollection, AccountBlock>>) -> Self {
        Self {
            inner: BlockExtra {
                in_msg_description: Default::default(),
                out_msg_description: Default::default(),
                account_blocks,
                rand_seed: HashBytes::ZERO,
                created_by: HashBytes::ZERO,
                custom: None,
            },
            phantom_data: std::marker::PhantomData,
        }
    }
    #[cfg(feature = "venom")]
    /// Creates a new block info builder.
    pub fn new(
        account_blocks: Lazy<AugDict<HashBytes, CurrencyCollection, AccountBlock>>,
        shard_block_refs: ShardBlockRefs,
    ) -> Self {
        Self {
            inner: BlockExtra {
                in_msg_description: Default::default(),
                out_msg_description: Default::default(),
                account_blocks,
                rand_seed: HashBytes::ZERO,
                created_by: HashBytes::ZERO,
                custom: None,
                shard_block_refs,
            },
            phantom_data: std::marker::PhantomData,
        }
    }

    #[cfg(feature = "tycho")]
    /// Set incoming and outgoing message description.
    pub fn set_msg_descriptions(
        mut self,
        in_msg_description: InMsgDescr,
        out_msg_description: OutMsgDescr,
    ) -> BlockExtraBuilder<BlockExtra> {
        self.inner.in_msg_description = CellBuilder::build_from(in_msg_description).unwrap();
        self.inner.out_msg_description = CellBuilder::build_from(out_msg_description).unwrap();
        BlockExtraBuilder {
            inner: self.inner,
            phantom_data: std::marker::PhantomData,
        }
    }
}

impl BlockExtraBuilder<BlockExtra> {
    /// Builds the block info.
    pub fn build(self) -> BlockExtra {
        self.inner
    }
}

pub(super) type InMsgDescr = AugDict<HashBytes, ImportFees, InMsg>;
pub(super) type OutMsgDescr = AugDict<HashBytes, CurrencyCollection, OutMsg>;

/// Block content.
#[derive(Debug, Clone)]
pub struct BlockExtra {
    /// Incoming message description.
    pub in_msg_description: Cell,
    /// Outgoing message description.
    pub out_msg_description: Cell,
    /// Block transactions info.
    pub account_blocks: Lazy<AugDict<HashBytes, CurrencyCollection, AccountBlock>>,
    /// Random generator seed.
    pub rand_seed: HashBytes,
    /// Public key of the collator who produced this block.
    pub created_by: HashBytes,
    /// Additional block content.
    pub custom: Option<Lazy<McBlockExtra>>,
    /// References to the latest known blocks from all shards.
    #[cfg(feature = "venom")]
    pub shard_block_refs: ShardBlockRefs,
}

impl BlockExtra {
    const TAG_V1: u32 = 0x4a33f6fd;
    #[cfg(feature = "venom")]
    const TAG_V2: u32 = 0x4a33f6fc;
}

impl Store for BlockExtra {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        #[cfg(not(feature = "venom"))]
        ok!(builder.store_u32(Self::TAG_V1));
        #[cfg(feature = "venom")]
        ok!(builder.store_u32(Self::TAG_V2));

        ok!(builder.store_reference(self.in_msg_description.clone()));
        ok!(builder.store_reference(self.out_msg_description.clone()));
        ok!(builder.store_reference(self.account_blocks.cell.clone()));
        ok!(builder.store_u256(&self.rand_seed));
        ok!(builder.store_u256(&self.created_by));

        #[cfg(not(feature = "venom"))]
        ok!(self.custom.store_into(builder, context));

        #[cfg(feature = "venom")]
        ok!(builder.store_reference({
            let mut builder = CellBuilder::new();

            ok!(self.custom.store_into(&mut builder, context));
            ok!(self.shard_block_refs.store_into(&mut builder, context));

            ok!(builder.build_ext(context))
        }));

        Ok(())
    }
}

impl<'a> Load<'a> for BlockExtra {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let tag = ok!(slice.load_u32());
        #[cfg(not(feature = "venom"))]
        if tag != Self::TAG_V1 {
            return Err(Error::InvalidTag);
        }
        #[cfg(feature = "venom")]
        if tag != Self::TAG_V1 && tag != Self::TAG_V2 {
            return Err(Error::InvalidTag);
        }

        let in_msg_description = ok!(slice.load_reference_cloned());
        let out_msg_description = ok!(slice.load_reference_cloned());
        let account_blocks = ok!(Lazy::load_from(slice));
        let rand_seed = ok!(slice.load_u256());
        let created_by = ok!(slice.load_u256());

        #[cfg(not(feature = "venom"))]
        let custom = ok!(Option::<Lazy<_>>::load_from(slice));

        #[cfg(feature = "venom")]
        let (custom, shard_block_refs) = {
            let slice = &mut ok!(slice.load_reference_as_slice());
            let custom = ok!(Option::<Lazy<_>>::load_from(slice));
            let shard_block_refs = ok!(ShardBlockRefs::load_from(slice));
            (custom, shard_block_refs)
        };

        Ok(Self {
            in_msg_description,
            out_msg_description,
            account_blocks,
            rand_seed,
            created_by,
            custom,
            #[cfg(feature = "venom")]
            shard_block_refs,
        })
    }
}

impl BlockExtra {
    /// Tries to load additional block content.
    pub fn load_custom(&self) -> Result<Option<McBlockExtra>, Error> {
        match &self.custom {
            Some(custom) => match custom.load() {
                Ok(custom) => Ok(Some(custom)),
                Err(e) => Err(e),
            },
            None => Ok(None),
        }
    }

    #[cfg(feature = "tycho")]
    /// Tries to load Incoming message description.
    pub fn load_in_msg_description(&self) -> Result<InMsgDescr, Error> {
        self.in_msg_description.as_ref().parse()
    }

    #[cfg(feature = "tycho")]
    /// Tries to load Outgoing message description.
    pub fn load_out_msg_description(&self) -> Result<OutMsgDescr, Error> {
        self.out_msg_description.as_ref().parse()
    }
}

/// A group of account transactions.
#[derive(Debug, Clone)]
pub struct AccountBlock {
    /// Account id.
    pub account: HashBytes,
    /// Dictionary with fees and account transactions.
    pub transactions: AugDict<u64, CurrencyCollection, Lazy<Transaction>>,
    /// Account state hashes before and after this block.
    pub state_update: Lazy<HashUpdate>,
}

impl AccountBlock {
    const TAG: u8 = 5;
}

impl Store for AccountBlock {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        let transactions_root = match self.transactions.dict().root() {
            Some(root) => ok!(root.as_ref().as_slice()),
            None => return Err(Error::InvalidData),
        };

        ok!(builder.store_small_uint(Self::TAG, 4));
        ok!(builder.store_u256(&self.account));
        ok!(builder.store_slice(transactions_root));
        self.state_update.store_into(builder, context)
    }
}

impl<'a> Load<'a> for AccountBlock {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        match slice.load_small_uint(4) {
            Ok(Self::TAG) => {}
            Ok(_) => return Err(Error::InvalidTag),
            Err(e) => return Err(e),
        }

        Ok(Self {
            account: ok!(slice.load_u256()),
            transactions: ok!(AugDict::load_from_root(slice, &mut Cell::empty_context())),
            state_update: ok!(Lazy::load_from(slice)),
        })
    }
}

impl<'a> AugDictSkipValue<'a> for Lazy<Transaction> {
    fn skip_value(slice: &mut CellSlice<'a>) -> bool {
        slice.try_advance(0, 1)
    }
}

/// Additional content for masterchain blocks.
#[derive(Debug, Clone)]
pub struct McBlockExtra {
    /// A tree of the most recent descriptions for all currently existing shards
    /// for all workchains except the masterchain.
    pub shards: ShardHashes,
    /// Collected/created shard fees.
    pub fees: ShardFees,
    /// Signatures for previous blocks (TODO)
    pub prev_block_signatures: Dict<u16, BlockSignature>,
    /// TODO
    pub recover_create_msg: Option<Cell>,
    /// TODO
    pub mint_msg: Option<Cell>,
    /// Copyleft messages if present.
    pub copyleft_msgs: Dict<Uint15, Cell>,
    /// Blockchain config (if the block is a key block).
    pub config: Option<BlockchainConfig>,
}

impl McBlockExtra {
    const TAG_V1: u16 = 0xcca5;
    const TAG_V2: u16 = 0xdc75;

    // #[cfg(feature = "tycho")]
    // /// Tries to load recover create message
    // pub fn load_recover_create_msg(&self) -> Option<Result<InMsg, Error>> {
    //     self.recover_create_msg
    //         .clone()
    //         .map(|msg| msg.as_ref().parse())
    // }
    //
    // #[cfg(feature = "tycho")]
    // /// Tries to load mint message
    // pub fn load_mint_msg(&self) -> Option<Result<InMsg, Error>> {
    //     self.mint_msg.clone().map(|msg| msg.as_ref().parse())
    // }

    #[cfg(feature = "tycho")]
    /// Set recover create message
    pub fn set_recover_create_msg(mut self, recover_create_msg: InMsg) {
        self.recover_create_msg = Some(CellBuilder::build_from(recover_create_msg).unwrap());
    }

    #[cfg(feature = "tycho")]
    /// Set mint message
    pub fn set_mint_msg(mut self, mint_msg: InMsg) {
        self.mint_msg = Some(CellBuilder::build_from(mint_msg).unwrap());
    }
}

impl Store for McBlockExtra {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        let tag = if self.copyleft_msgs.is_empty() {
            Self::TAG_V1
        } else {
            Self::TAG_V2
        };

        let cell = {
            let mut builder = CellBuilder::new();
            ok!(self.prev_block_signatures.store_into(&mut builder, context));
            ok!(self.recover_create_msg.store_into(&mut builder, context));
            ok!(self.mint_msg.store_into(&mut builder, context));

            if !self.copyleft_msgs.is_empty() {
                ok!(self.copyleft_msgs.store_into(&mut builder, context));
            }

            ok!(builder.build_ext(context))
        };

        ok!(builder.store_u16(tag));
        ok!(builder.store_bit(self.config.is_some()));
        ok!(self.shards.store_into(builder, context));
        ok!(self.fees.store_into(builder, context));
        ok!(builder.store_reference(cell));

        if let Some(config) = &self.config {
            config.store_into(builder, context)
        } else {
            Ok(())
        }
    }
}

impl<'a> Load<'a> for McBlockExtra {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let with_copyleft = match slice.load_u16() {
            Ok(Self::TAG_V1) => false,
            Ok(Self::TAG_V2) => true,
            Ok(_) => return Err(Error::InvalidTag),
            Err(e) => return Err(e),
        };

        let with_config = ok!(slice.load_bit());
        let shards = ok!(ShardHashes::load_from(slice));
        let fees = ok!(ShardFees::load_from(slice));

        let mut cont = ok!(slice.load_reference_as_slice());

        let config = if with_config {
            Some(ok!(BlockchainConfig::load_from(slice)))
        } else {
            None
        };

        let slice = &mut cont;

        Ok(Self {
            shards,
            fees,
            prev_block_signatures: ok!(Dict::load_from(slice)),
            recover_create_msg: ok!(Option::<Cell>::load_from(slice)),
            mint_msg: ok!(Option::<Cell>::load_from(slice)),
            copyleft_msgs: if with_copyleft {
                ok!(Dict::load_from(slice))
            } else {
                Dict::new()
            },
            config,
        })
    }
}

/// TEMP shard fees mapping sub.
#[derive(Debug, Clone, Store, Load)]
pub struct ShardFees {
    /// Dictionary root.
    pub root: Option<Cell>,
    /// `AugDict` root extra part.
    pub fees: CurrencyCollection,
    /// `AugDict` root extra part.
    pub create: CurrencyCollection,
}

impl ShardFees {
    #[cfg(feature = "tycho")]
    /// Tries to load Incoming message description.
    pub fn load_root(&self) -> Option<Result<ShardIdentifier, Error>> {
        self.root.as_ref().map(|root| root.parse())
    }
    #[cfg(feature = "tycho")]
    /// Set root description.
    pub fn set_root(&mut self, root: ShardIdentifier) {
        self.root = Some(CellBuilder::build_from(root).unwrap());
    }
}

#[cfg(feature = "tycho")]
/// Shard identifier with full prefix.
#[derive(Clone, Debug, Default, Store, Load)]
pub struct ShardIdentifier {
    /// Workchain id.
    pub workchain: i8,
    /// Shard prefix.
    pub prefix: u64,
}

/// Block signature pair.
#[derive(Debug, Clone, Store, Load)]
pub struct BlockSignature {
    /// Signer node short id.
    pub node_id_short: HashBytes,
    /// Signature data.
    pub signature: Signature,
}

/// Signature verification utils.
pub trait BlockSignatureExt {
    /// Verifies signatures for the specified data and the provided list of nodes.
    fn check_signatures(&self, list: &[ValidatorDescription], data: &[u8]) -> Result<u64, Error>;
}

impl BlockSignatureExt for Dict<u16, BlockSignature> {
    fn check_signatures(&self, list: &[ValidatorDescription], data: &[u8]) -> Result<u64, Error> {
        // Collect nodes by short id
        let mut unique_nodes =
            ahash::HashMap::<[u8; 32], &ValidatorDescription>::with_capacity_and_hasher(
                list.len(),
                Default::default(),
            );

        for node in list {
            let node_id_short = tl_proto::hash(everscale_crypto::tl::PublicKey::Ed25519 {
                key: node.public_key.as_ref(),
            });
            unique_nodes.insert(node_id_short, node);
        }

        let mut weight = 0;
        for value in self.values() {
            let value = ok!(value);
            if let Some(node) = unique_nodes.get(&value.node_id_short) {
                if !node.verify_signature(data, &value.signature) {
                    return Err(Error::InvalidSignature);
                }
                weight += node.weight;
            }
        }

        Ok(weight)
    }
}

/// Ed25519 signature.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Signature(pub [u8; 64]);

impl Signature {
    const TAG_LEN: u16 = 4;

    const TAG: u8 = 0x5;
}

impl Default for Signature {
    #[inline]
    fn default() -> Self {
        Self([0; 64])
    }
}

impl AsRef<[u8; 64]> for Signature {
    #[inline]
    fn as_ref(&self) -> &[u8; 64] {
        &self.0
    }
}

impl Store for Signature {
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn CellContext) -> Result<(), Error> {
        ok!(builder.store_small_uint(Self::TAG, Self::TAG_LEN));
        builder.store_raw(&self.0, 512)
    }
}

impl<'a> Load<'a> for Signature {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        match slice.load_small_uint(Self::TAG_LEN) {
            Ok(Self::TAG) => {}
            Ok(_) => return Err(Error::InvalidTag),
            Err(e) => return Err(e),
        }

        let mut result = Self::default();
        match slice.load_raw(&mut result.0, 512) {
            Ok(_) => Ok(result),
            Err(e) => Err(e),
        }
    }
}
