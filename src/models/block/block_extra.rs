use crate::cell::*;
use crate::dict::{AugDict, AugDictSkipValue, Dict};
use crate::error::Error;
use crate::num::Uint15;
use crate::util::{CustomDebug, DisplayHash};

use crate::models::config::BlockchainConfig;
use crate::models::currency::CurrencyCollection;
use crate::models::transaction::{HashUpdate, Transaction};
use crate::models::Lazy;

use super::ShardHashes;

/// Block content.
#[derive(CustomDebug, Clone, Store, Load)]
#[tlb(tag = "#4a33f6fd")]
pub struct BlockExtra {
    /// Incoming message description.
    pub in_msg_description: Cell,
    /// Outgoing message description.
    pub out_msg_description: Cell,
    /// Block transactions info.
    pub account_blocks: Lazy<AugDict<CellHash, CurrencyCollection, AccountBlock>>,
    /// Random generator seed.
    #[debug(with = "DisplayHash")]
    pub rand_seed: CellHash,
    /// Public key of the collator who produced this block.
    #[debug(with = "DisplayHash")]
    pub created_by: CellHash,
    /// Additional block content.
    pub custom: Option<Lazy<McBlockExtra>>,
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
}

/// A group of account transactions.
#[derive(CustomDebug, Clone)]
pub struct AccountBlock {
    /// Account id.
    #[debug(with = "DisplayHash")]
    pub account: CellHash,
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
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        let transactions_root = match self.transactions.dict().root() {
            Some(root) => ok!(root.as_ref().as_slice()),
            None => return Err(Error::InvalidData),
        };

        ok!(builder.store_small_uint(Self::TAG, 4));
        ok!(builder.store_u256(&self.account));
        ok!(builder.store_slice(transactions_root));
        self.state_update.store_into(builder, finalizer)
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
            transactions: ok!(AugDict::load_from_root(
                slice,
                &mut Cell::default_finalizer()
            )),
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
}

impl Store for McBlockExtra {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        let tag = if self.copyleft_msgs.is_empty() {
            Self::TAG_V1
        } else {
            Self::TAG_V2
        };

        let cell = {
            let mut builder = CellBuilder::new();
            ok!(self
                .prev_block_signatures
                .store_into(&mut builder, finalizer));
            ok!(self.recover_create_msg.store_into(&mut builder, finalizer));
            ok!(self.mint_msg.store_into(&mut builder, finalizer));

            if !self.copyleft_msgs.is_empty() {
                ok!(self.copyleft_msgs.store_into(&mut builder, finalizer));
            }

            ok!(builder.build_ext(finalizer))
        };

        ok!(builder.store_u16(tag));
        ok!(builder.store_bit(self.config.is_some()));
        ok!(self.shards.store_into(builder, finalizer));
        ok!(self.fees.store_into(builder, finalizer));
        ok!(builder.store_reference(cell));

        if let Some(config) = &self.config {
            config.store_into(builder, finalizer)
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
#[derive(CustomDebug, Clone, Store, Load)]
pub struct ShardFees {
    /// Dictionary root.
    pub root: Option<Cell>,
    /// `AugDict` root extra part.
    pub fees: CurrencyCollection,
    /// `AugDict` root extra part.
    pub create: CurrencyCollection,
}

/// Block signature pair.
#[derive(CustomDebug, Clone, Store, Load)]
pub struct BlockSignature {
    /// Signer node short id.
    #[debug(with = "DisplayHash")]
    pub node_id_short: CellHash,
    /// Signature data.
    pub signature: Signature,
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

impl Store for Signature {
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn Finalizer) -> Result<(), Error> {
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
