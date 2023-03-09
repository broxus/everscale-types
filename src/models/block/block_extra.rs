use crate::cell::*;
use crate::dict::{AugDict, AugDictSkipValue, Dict};
use crate::error::Error;
use crate::num::Uint15;
use crate::util::{CustomClone, CustomDebug, DisplayHash};

use crate::models::config::BlockchainConfig;
use crate::models::currency::CurrencyCollection;
use crate::models::transaction::{HashUpdate, Transaction};
use crate::models::Lazy;

use super::ShardHashes;

/// Block content.
#[derive(CustomDebug, CustomClone, Store, Load)]
#[tlb(tag = "#4a33f6fd")]
pub struct BlockExtra<C: CellFamily> {
    /// Incoming message description.
    pub in_msg_description: CellContainer<C>,
    /// Outgoing message description.
    pub out_msg_description: CellContainer<C>,
    /// Block transactions info.
    pub account_blocks: Lazy<C, AugDict<C, CellHash, CurrencyCollection<C>, AccountBlock<C>>>,
    /// Random generator seed.
    #[debug(with = "DisplayHash")]
    pub rand_seed: CellHash,
    /// Public key of the collator who produced this block.
    #[debug(with = "DisplayHash")]
    pub created_by: CellHash,
    /// Additional block content.
    pub custom: Option<Lazy<C, McBlockExtra<C>>>,
}

impl<C: CellFamily> BlockExtra<C> {
    /// Tries to load additional block content.
    pub fn load_custom(&self) -> Result<Option<McBlockExtra<C>>, Error> {
        match &self.custom {
            Some(custom) => match custom.load() {
                Some(custom) => Ok(Some(custom)),
                None => Err(Error::CellUnderflow),
            },
            None => Ok(None),
        }
    }
}

/// A group of account transactions.
#[derive(CustomDebug, CustomClone)]
pub struct AccountBlock<C: CellFamily> {
    /// Account id.
    #[debug(with = "DisplayHash")]
    pub account: CellHash,
    /// Dictionary with fees and account transactions.
    pub transactions: AugDict<C, u64, CurrencyCollection<C>, Lazy<C, Transaction<C>>>,
    /// Account state hashes before and after this block.
    pub state_update: Lazy<C, HashUpdate>,
}

impl<C: CellFamily> AccountBlock<C> {
    const TAG: u8 = 5;
}

impl<C: CellFamily> Store<C> for AccountBlock<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        let transactions_root = match self.transactions.dict().root() {
            Some(root) => root.as_ref().as_slice(),
            None => return false,
        };

        builder.store_small_uint(Self::TAG, 4)
            && builder.store_u256(&self.account)
            && builder.store_slice(transactions_root)
            && self.state_update.store_into(builder, finalizer)
    }
}

impl<'a, C> Load<'a, C> for AccountBlock<C>
where
    for<'c> C: DefaultFinalizer + 'c,
{
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if slice.load_small_uint(4)? != Self::TAG {
            return None;
        }

        Some(Self {
            account: slice.load_u256()?,
            transactions: AugDict::load_from_root(slice, &mut C::default_finalizer())?,
            state_update: Lazy::load_from(slice)?,
        })
    }
}

impl<'a, C: CellFamily> AugDictSkipValue<'a, C> for Lazy<C, Transaction<C>> {
    fn skip_value(slice: &mut CellSlice<'a, C>) -> bool {
        slice.try_advance(0, 1)
    }
}

/// Additional content for masterchain blocks.
#[derive(CustomDebug, CustomClone)]
pub struct McBlockExtra<C: CellFamily> {
    /// A tree of the most recent descriptions for all currently existing shards
    /// for all workchains except the masterchain.
    pub shards: ShardHashes<C>,
    /// Collected/created shard fees.
    pub fees: ShardFees<C>,
    /// Signatures for previous blocks (TODO)
    pub prev_block_signatures: Dict<C, u16, BlockSignature>,
    /// TODO
    pub recover_create_msg: Option<CellContainer<C>>,
    /// TODO
    pub mint_msg: Option<CellContainer<C>>,
    /// Copyleft messages if present.
    pub copyleft_msgs: Dict<C, Uint15, CellContainer<C>>,
    /// Blockchain config (if the block is a key block).
    pub config: Option<BlockchainConfig<C>>,
}

impl<C: CellFamily> McBlockExtra<C> {
    const TAG_V1: u16 = 0xcca5;
    const TAG_V2: u16 = 0xdc75;
}

impl<C: CellFamily> Store<C> for McBlockExtra<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        let tag = if self.copyleft_msgs.is_empty() {
            Self::TAG_V1
        } else {
            Self::TAG_V2
        };

        let cell = {
            let mut builder = CellBuilder::<C>::new();
            if !(self
                .prev_block_signatures
                .store_into(&mut builder, finalizer)
                && self.recover_create_msg.store_into(&mut builder, finalizer)
                && self.mint_msg.store_into(&mut builder, finalizer))
            {
                return false;
            }

            if !self.copyleft_msgs.is_empty()
                && !self.copyleft_msgs.store_into(&mut builder, finalizer)
            {
                return false;
            }

            if let Some(cell) = builder.build_ext(finalizer) {
                cell
            } else {
                return false;
            }
        };

        if !(builder.store_u16(tag)
            && builder.store_bit(self.config.is_some())
            && self.shards.store_into(builder, finalizer)
            && self.fees.store_into(builder, finalizer)
            && builder.store_reference(cell))
        {
            return false;
        }

        if let Some(config) = &self.config {
            if !config.store_into(builder, finalizer) {
                return false;
            }
        }

        true
    }
}

impl<'a, C: CellFamily> Load<'a, C> for McBlockExtra<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let with_copyleft = match slice.load_u16()? {
            Self::TAG_V1 => false,
            Self::TAG_V2 => true,
            _ => return None,
        };

        let with_config = slice.load_bit()?;
        let shards = ShardHashes::load_from(slice)?;
        let fees = ShardFees::load_from(slice)?;

        let cont = slice.load_reference()?;

        let config = if with_config {
            Some(BlockchainConfig::load_from(slice)?)
        } else {
            None
        };

        let slice = &mut cont.as_slice();
        Some(Self {
            shards,
            fees,
            prev_block_signatures: Dict::load_from(slice)?,
            recover_create_msg: Option::<CellContainer<C>>::load_from(slice)?,
            mint_msg: Option::<CellContainer<C>>::load_from(slice)?,
            copyleft_msgs: if with_copyleft {
                Dict::load_from(slice)?
            } else {
                Dict::new()
            },
            config,
        })
    }
}

/// TEMP shard fees mapping sub.
#[derive(CustomDebug, CustomClone, Store, Load)]
pub struct ShardFees<C: CellFamily> {
    /// Dictionary root.
    pub root: Option<CellContainer<C>>,
    /// `AugDict` root extra part.
    pub fees: CurrencyCollection<C>,
    /// `AugDict` root extra part.
    pub create: CurrencyCollection<C>,
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
    const TAG: u8 = 0x5;
}

impl Default for Signature {
    #[inline]
    fn default() -> Self {
        Self([0; 64])
    }
}

impl<C: CellFamily> Store<C> for Signature {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        builder.store_small_uint(Self::TAG, 5) && builder.store_raw(&self.0, 512)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for Signature {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if slice.load_small_uint(4)? != Self::TAG {
            return None;
        }
        let mut result = Self::default();
        slice.load_raw(&mut result.0, 512)?;
        Some(result)
    }
}
