#[cfg(feature = "sync")]
use std::sync::OnceLock;

use crate::cell::*;
use crate::dict::{AugDict, AugDictExtra, Dict, DictKey};
use crate::error::Error;
use crate::num::Uint15;

use crate::models::config::{BlockchainConfig, ValidatorDescription};
use crate::models::currency::CurrencyCollection;
use crate::models::message::{ImportFees, InMsg, OutMsg};
use crate::models::transaction::{HashUpdate, Transaction};
use crate::models::{Lazy, ShardHashes, ShardIdent};

#[cfg(feature = "venom")]
use super::ShardBlockRefs;

/// Block content.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct BlockExtra {
    /// Inbound message description.
    pub in_msg_description: Lazy<InMsgDescr>,
    /// Outbound message description.
    pub out_msg_description: Lazy<OutMsgDescr>,
    /// Block transactions info.
    pub account_blocks: Lazy<AccountBlocks>,
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

#[cfg(feature = "sync")]
impl Default for BlockExtra {
    fn default() -> Self {
        Self {
            in_msg_description: Self::empty_in_msg_descr().clone(),
            out_msg_description: Self::empty_out_msg_descr().clone(),
            account_blocks: Self::empty_account_blocks().clone(),
            rand_seed: HashBytes::default(),
            created_by: HashBytes::default(),
            custom: None,
            #[cfg(feature = "venom")]
            shard_block_refs: ShardBlockRefs::default(),
        }
    }
}

impl BlockExtra {
    const TAG_V1: u32 = 0x4a33f6fd;
    #[cfg(any(feature = "venom", feature = "tycho"))]
    const TAG_V2: u32 = 0x4a33f6fc;

    /// Returns a static reference to an empty inbound message description.
    #[cfg(feature = "sync")]
    pub fn empty_in_msg_descr() -> &'static Lazy<InMsgDescr> {
        static IN_MSG_DESCR: OnceLock<Lazy<InMsgDescr>> = OnceLock::new();
        IN_MSG_DESCR.get_or_init(|| Lazy::new(&AugDict::new()).unwrap())
    }

    /// Returns a static reference to an empty outbound message description.
    #[cfg(feature = "sync")]
    pub fn empty_out_msg_descr() -> &'static Lazy<OutMsgDescr> {
        static OUT_MSG_DESCR: OnceLock<Lazy<OutMsgDescr>> = OnceLock::new();
        OUT_MSG_DESCR.get_or_init(|| Lazy::new(&AugDict::new()).unwrap())
    }

    /// Returns a static reference to an empty account blocks.
    #[cfg(feature = "sync")]
    pub fn empty_account_blocks() -> &'static Lazy<AccountBlocks> {
        static ACCOUNT_BLOCKS: OnceLock<Lazy<AccountBlocks>> = OnceLock::new();
        ACCOUNT_BLOCKS.get_or_init(|| Lazy::new(&AugDict::new()).unwrap())
    }
}

impl Store for BlockExtra {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        #[cfg(not(any(feature = "venom", feature = "tycho")))]
        ok!(builder.store_u32(Self::TAG_V1));
        #[cfg(any(feature = "venom", feature = "tycho"))]
        ok!(builder.store_u32(Self::TAG_V2));

        ok!(builder.store_reference(self.in_msg_description.cell.clone()));
        ok!(builder.store_reference(self.out_msg_description.cell.clone()));
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
        #[cfg(not(any(feature = "venom", feature = "tycho")))]
        if tag != Self::TAG_V1 {
            return Err(Error::InvalidTag);
        }
        #[cfg(any(feature = "venom", feature = "tycho"))]
        if tag != Self::TAG_V1 && tag != Self::TAG_V2 {
            return Err(Error::InvalidTag);
        }

        let in_msg_description = ok!(Lazy::load_from(slice));
        let out_msg_description = ok!(Lazy::load_from(slice));
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

    /// Tries to load inbound message description.
    pub fn load_in_msg_description(&self) -> Result<InMsgDescr, Error> {
        self.in_msg_description.load()
    }

    /// Tries to load outbound message description.
    pub fn load_out_msg_description(&self) -> Result<OutMsgDescr, Error> {
        self.out_msg_description.load()
    }
}

/// Account blocks grouped by account id with a total fees as an extra data.
pub type AccountBlocks = AugDict<HashBytes, CurrencyCollection, AccountBlock>;

/// A group of account transactions.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
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

/// A list of inbound messages.
pub type InMsgDescr = AugDict<HashBytes, ImportFees, InMsg>;

/// A list of outbound messages.
pub type OutMsgDescr = AugDict<HashBytes, CurrencyCollection, OutMsg>;

/// Additional content for masterchain blocks.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct McBlockExtra {
    /// A tree of the most recent descriptions for all currently existing shards
    /// for all workchains except the masterchain.
    pub shards: ShardHashes,
    /// Collected/created shard fees.
    pub fees: ShardFees,
    /// Signatures for previous blocks.
    pub prev_block_signatures: Dict<u16, BlockSignature>,
    /// An optional message with funds recover.
    pub recover_create_msg: Option<Lazy<InMsg>>,
    /// An optional message with minting.
    pub mint_msg: Option<Lazy<InMsg>>,
    /// Copyleft messages if present.
    #[cfg_attr(feature = "serde", serde(skip))]
    pub copyleft_msgs: Dict<Uint15, Cell>,
    /// Blockchain config (if the block is a key block).
    pub config: Option<BlockchainConfig>,
}

impl Default for McBlockExtra {
    fn default() -> Self {
        Self {
            shards: ShardHashes::default(),
            fees: ShardFees::new(),
            prev_block_signatures: Dict::new(),
            recover_create_msg: None,
            mint_msg: None,
            copyleft_msgs: Dict::new(),
            config: None,
        }
    }
}

impl McBlockExtra {
    const TAG_V1: u16 = 0xcca5;
    const TAG_V2: u16 = 0xdc75;

    /// Tries to load recover/create message.
    pub fn load_recover_create_msg(&self) -> Result<Option<InMsg>, Error> {
        match &self.recover_create_msg {
            Some(msg) => msg.load().map(Some),
            None => Ok(None),
        }
    }

    /// Tries to load mint message.
    pub fn load_mint_msg(&self) -> Result<Option<InMsg>, Error> {
        match &self.mint_msg {
            Some(msg) => msg.load().map(Some),
            None => Ok(None),
        }
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
            recover_create_msg: ok!(Option::<Lazy<_>>::load_from(slice)),
            mint_msg: ok!(Option::<Lazy<_>>::load_from(slice)),
            copyleft_msgs: if with_copyleft {
                ok!(Dict::load_from(slice))
            } else {
                Dict::new()
            },
            config,
        })
    }
}

/// A dictionary with collected/created shard fees.
pub type ShardFees = AugDict<ShardIdentFull, ShardFeeCreated, ShardFeeCreated>;

/// [`ShardIdent`] that is stored with terminatino bit.
#[derive(Clone, Debug, Default, Store, Load)]
pub struct ShardIdentFull {
    /// Workchain id.
    pub workchain: i32,
    /// Shard prefix with terminatino bit.
    pub prefix: u64,
}

impl DictKey for ShardIdentFull {
    const BITS: u16 = 96;

    fn from_raw_data(raw_data: &[u8; 128]) -> Option<Self> {
        let workchain = i32::from_be_bytes(raw_data[0..4].try_into().unwrap());
        let prefix = u64::from_be_bytes(raw_data[4..12].try_into().unwrap());
        Some(Self { workchain, prefix })
    }
}

impl TryFrom<ShardIdentFull> for ShardIdent {
    type Error = Error;

    #[inline]
    fn try_from(ident: ShardIdentFull) -> Result<Self, Self::Error> {
        ShardIdent::new(ident.workchain, ident.prefix).ok_or(Error::InvalidData)
    }
}

impl From<ShardIdent> for ShardIdentFull {
    #[inline]
    fn from(ident: ShardIdent) -> Self {
        Self {
            workchain: ident.workchain(),
            prefix: ident.prefix(),
        }
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for ShardIdentFull {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if serializer.is_human_readable() {
            serializer.collect_str(&format_args!("{}:{:08x}", self.workchain, self.prefix))
        } else {
            (self.workchain, self.prefix).serialize(serializer)
        }
    }
}

/// Collected fees/created funds.
#[derive(Debug, Clone, Default, Eq, PartialEq, Store, Load)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct ShardFeeCreated {
    /// Collected fees.
    pub fees: CurrencyCollection,
    /// Created funds.
    pub create: CurrencyCollection,
}

impl AugDictExtra for ShardFeeCreated {
    fn comp_add(
        left: &mut CellSlice,
        right: &mut CellSlice,
        b: &mut CellBuilder,
        cx: &mut dyn CellContext,
    ) -> Result<(), Error> {
        let left = ok!(Self::load_from(left));
        let right = ok!(Self::load_from(right));
        Self {
            fees: ok!(left.fees.checked_add(&right.fees)),
            create: ok!(left.create.checked_add(&right.create)),
        }
        .store_into(b, cx)
    }
}

/// Block signature pair.
#[derive(Debug, Clone, Store, Load)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
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

#[cfg(feature = "serde")]
impl serde::Serialize for Signature {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use base64::prelude::{Engine as _, BASE64_STANDARD};

        const fn encoded_len(len: usize) -> usize {
            (len * 4 / 3 + 3) & !3
        }

        if serializer.is_human_readable() {
            const BUFFER_SIZE: usize = encoded_len(64);

            let mut buffer = [0; { BUFFER_SIZE }];
            let n = BASE64_STANDARD
                .encode_slice(self.0.as_slice(), &mut buffer)
                .unwrap();
            debug_assert_eq!(n, BUFFER_SIZE);

            // SAFETY: `BASE64_STANDARD` always returns a valid UTF-8 string.
            serializer.serialize_str(unsafe { std::str::from_utf8_unchecked(&buffer) })
        } else {
            self.0.serialize(serializer)
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "serde")]
    #[test]
    fn serde_signature() {
        let res = super::Signature([123; 64]);
        serde_json::to_string(&res).unwrap();
    }
}
