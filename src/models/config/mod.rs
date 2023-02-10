//! Blockchain config and params.

use crate::cell::*;
use crate::dict::{Dict, DictKey};
use crate::error::Error;
use crate::num::Tokens;
use crate::util::DisplayHash;

use crate::models::block::GlobalVersion;
use crate::models::currency::ExtraCurrencyCollection;

pub use self::params::*;

mod params;

/// Blockchain config.
#[derive(Clone, Eq, PartialEq)]
pub struct BlockchainConfig<C: CellFamily> {
    /// Configuration contract address.
    pub address: CellHash,
    /// Configuration parameters.
    pub params: Dict<C, u32, CellContainer<C>>,
}

impl<C: CellFamily> std::fmt::Debug for BlockchainConfig<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BlockchainConfig")
            .field("address", &DisplayHash(&self.address))
            .field("params", &self.params)
            .finish()
    }
}

impl<C: CellFamily> Store<C> for BlockchainConfig<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        let params_root = match self.params.root() {
            Some(root) => root.clone(),
            None => return false,
        };
        builder.store_u256(&self.address) && builder.store_reference(params_root)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for BlockchainConfig<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            address: slice.load_u256()?,
            params: Dict::from(Some(slice.load_reference_cloned()?)),
        })
    }
}

impl<C> BlockchainConfig<C>
where
    for<'c> C: DefaultFinalizer + 'c,
{
    /// Returns the elector account address (in masterchain).
    ///
    /// Uses [`ConfigParam1`].
    pub fn get_elector_address(&self) -> Result<CellHash, Error> {
        ok!(self.get::<ConfigParam1>()).ok_or(Error::CellUnderflow)
    }

    /// Returns the minter account address (in masterchain).
    ///
    /// Uses [`ConfigParam2`] with a fallback to [`ConfigParam0`] (config).
    pub fn get_minter_address(&self) -> Result<CellHash, Error> {
        match ok!(self.get::<ConfigParam2>()) {
            Some(address) => Ok(address),
            None => ok!(self.get::<ConfigParam0>()).ok_or(Error::CellUnderflow),
        }
    }

    /// Returns the fee collector account address (in masterchain).
    ///
    /// Uses [`ConfigParam3`] with a fallback to [`ConfigParam1`] (elector).
    pub fn get_fee_collector_address(&self) -> Result<CellHash, Error> {
        match ok!(self.get::<ConfigParam3>()) {
            Some(address) => Ok(address),
            None => ok!(self.get::<ConfigParam1>()).ok_or(Error::CellUnderflow),
        }
    }

    /// Returns the lowest supported block version and required capabilities.
    ///
    /// Uses [`ConfigParam8`].
    pub fn get_global_version(&self) -> Result<GlobalVersion, Error> {
        ok!(self.get::<ConfigParam8>()).ok_or(Error::CellUnderflow)
    }

    /// Returns a list of params that must be present in config.
    ///
    /// Uses [`ConfigParam9`].
    pub fn get_mandatory_params(&self) -> Result<Dict<C, u32, ()>, Error> {
        ok!(self.get::<ConfigParam9>()).ok_or(Error::CellUnderflow)
    }

    /// Returns a list of params that have a different set of update requirements.
    ///
    /// Uses [`ConfigParam10`].
    pub fn get_critical_params(&self) -> Result<Dict<C, u32, ()>, Error> {
        ok!(self.get::<ConfigParam10>()).ok_or(Error::CellUnderflow)
    }

    /// Returns a dictionary with workchain descriptions.
    ///
    /// Uses [`ConfigParam12`].
    pub fn get_workchains(&self) -> Result<Dict<C, i32, WorkchainDescription>, Error> {
        ok!(self.get::<ConfigParam12>()).ok_or(Error::CellUnderflow)
    }

    /// Returns a block creation reward in tokens.
    ///
    /// Uses [`ConfigParam14`].
    pub fn get_block_creation_reward(&self, masterchain: bool) -> Result<Tokens, Error> {
        let Some(rewards) = ok!(self.get::<ConfigParam14>()) else { return Err(Error::CellUnderflow); };
        Ok(if masterchain {
            rewards.masterchain_block_fee
        } else {
            rewards.basechain_block_fee
        })
    }

    /// Returns election timings.
    ///
    /// Uses [`ConfigParam15`].
    pub fn get_election_timings(&self) -> Result<ElectionTimings, Error> {
        ok!(self.get::<ConfigParam15>()).ok_or(Error::CellUnderflow)
    }

    /// Returns possible validator count.
    ///
    /// Uses [`ConfigParam16`].
    pub fn get_validator_count_params(&self) -> Result<ValidatorCountParams, Error> {
        ok!(self.get::<ConfigParam16>()).ok_or(Error::CellUnderflow)
    }

    /// Returns validator stake range and factor.
    ///
    /// Uses [`ConfigParam17`].
    pub fn get_validator_stake_params(&self) -> Result<ValidatorStakeParams, Error> {
        ok!(self.get::<ConfigParam17>()).ok_or(Error::CellUnderflow)
    }

    /// Returns a list with a history of all storage prices.
    ///
    /// Uses [`ConfigParam18`].
    pub fn get_storage_prices(&self) -> Result<Dict<C, u32, StoragePrices>, Error> {
        ok!(self.get::<ConfigParam18>()).ok_or(Error::CellUnderflow)
    }

    /// Returns gas limits and prices.
    ///
    /// Uses [`ConfigParam20`] (for masterchain) or [`ConfigParam21`] (for other workchains).
    pub fn get_gas_prices(&self, masterchain: bool) -> Result<GasLimitsPrices, Error> {
        ok!(if masterchain {
            self.get::<ConfigParam20>()
        } else {
            self.get::<ConfigParam21>()
        })
        .ok_or(Error::CellUnderflow)
    }

    /// Returns block limits.
    ///
    /// Uses [`ConfigParam22`] (for masterchain) or [`ConfigParam23`] (for other workchains).
    pub fn get_block_limits(&self, masterchain: bool) -> Result<BlockLimits, Error> {
        ok!(if masterchain {
            self.get::<ConfigParam22>()
        } else {
            self.get::<ConfigParam23>()
        })
        .ok_or(Error::CellUnderflow)
    }

    /// Returns message forwarding prices.
    ///
    /// Uses [`ConfigParam24`] (for masterchain) or [`ConfigParam25`] (for other workchains).
    pub fn get_msg_forward_prices(&self, masterchain: bool) -> Result<MsgForwardPrices, Error> {
        ok!(if masterchain {
            self.get::<ConfigParam24>()
        } else {
            self.get::<ConfigParam25>()
        })
        .ok_or(Error::CellUnderflow)
    }

    /// Returns a catchain config.
    ///
    /// Uses [`ConfigParam28`].
    pub fn get_catchain_config(&self) -> Result<CatchainConfig, Error> {
        ok!(self.get::<ConfigParam28>()).ok_or(Error::CellUnderflow)
    }

    /// Returns a consensus config.
    ///
    /// Uses [`ConfigParam29`].
    pub fn get_consensus_config(&self) -> Result<ConsensusConfig, Error> {
        ok!(self.get::<ConfigParam29>()).ok_or(Error::CellUnderflow)
    }

    /// Returns a list of fundamental account addresses (in masterchain).
    ///
    /// Uses [`ConfigParam31`].
    pub fn get_fundamental_addresses(&self) -> Result<Dict<C, CellHash, ()>, Error> {
        ok!(self.get::<ConfigParam31>()).ok_or(Error::CellUnderflow)
    }

    /// Returns `true` if the config contains info about the previous validator set.
    ///
    /// Uses [`ConfigParam32`] or [`ConfigParam33`].
    pub fn contains_prev_validator_set(&self) -> Result<bool, Error> {
        Ok(ok!(self.contains::<ConfigParam32>()) || ok!(self.contains::<ConfigParam33>()))
    }

    /// Returns `true` if the config contains info about the next validator set.
    ///
    /// Uses [`ConfigParam36`] or [`ConfigParam37`].
    pub fn contains_next_validator_set(&self) -> Result<bool, Error> {
        Ok(ok!(self.contains::<ConfigParam36>()) || ok!(self.contains::<ConfigParam37>()))
    }

    /// Returns the current validator set.
    ///
    /// Uses [`ConfigParam35`] (temp validators) or [`ConfigParam34`] (current validators).
    pub fn get_current_validator_set(&self) -> Result<ValidatorSet, Error> {
        match ok!(self.get::<ConfigParam35>()) {
            Some(set) => Ok(set),
            None => ok!(self.get::<ConfigParam34>()).ok_or(Error::CellUnderflow),
        }
    }

    /// Returns `true` if the config contains a param for the specified id.
    pub fn contains<'a, T: KnownConfigParam<'a, C>>(&'a self) -> Result<bool, Error> {
        self.params.contains_key(T::ID)
    }

    /// Returns `true` if the config contains a param for the specified id.
    pub fn contains_raw(&self, id: u32) -> Result<bool, Error> {
        self.params.contains_key(id)
    }

    /// Tries to get a parameter from the blockchain config.
    pub fn get<'a, T: KnownConfigParam<'a, C>>(&'a self) -> Result<Option<T::Value>, Error> {
        let Some(mut slice) = ok!(self.get_raw(T::ID)) else { return Ok(None); };
        match <T::Wrapper as Load<'a, C>>::load_from(&mut slice) {
            Some(wrapped) => Ok(Some(wrapped.into_inner())),
            None => Err(Error::CellUnderflow),
        }
    }

    /// Tries to get a raw parameter from the blockchain config.
    pub fn get_raw(&self, id: u32) -> Result<Option<CellSlice<'_, C>>, Error> {
        match ok!(self.params.get_raw(id)) {
            Some(slice) => match slice.get_reference(0) {
                Some(cell) => Ok(Some(cell.as_slice())),
                None => Err(Error::CellUnderflow),
            },
            None => Ok(None),
        }
    }
}

/// Marker trait which is implemented for known config params.
pub trait KnownConfigParam<'a, C: CellFamily> {
    /// Parameter index in a configuration dictionary.
    const ID: u32;

    /// Associated value type.
    type Value;

    /// Value wrapper.
    type Wrapper: ConfigParamWrapper<Self::Value> + Load<'a, C>;
}

/// Trait to customize config param representation.
pub trait ConfigParamWrapper<T> {
    /// Converts this wrapper into an underlying type.
    fn into_inner(self) -> T;
}

/// Identity wrapper for [`ConfigParamWrapper`].
#[repr(transparent)]
pub struct ParamIdentity<T>(T);

impl<T> ConfigParamWrapper<T> for ParamIdentity<T> {
    #[inline]
    fn into_inner(self) -> T {
        self.0
    }
}

impl<'a, C: CellFamily, T: Load<'a, C>> Load<'a, C> for ParamIdentity<T> {
    #[inline]
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self(T::load_from(slice)?))
    }
}

/// Dict wrapper for [`ConfigParamWrapper`] for parsing non-empty dictionaries.
#[repr(transparent)]
pub struct NonEmptyDict<T>(T);

impl<T> ConfigParamWrapper<T> for NonEmptyDict<T> {
    fn into_inner(self) -> T {
        self.0
    }
}

impl<'a, C, K, V> Load<'a, C> for NonEmptyDict<Dict<C, K, V>>
where
    for<'c> C: DefaultFinalizer + 'c,
    K: DictKey,
{
    #[inline]
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self(Dict::load_from_root_ext(
            slice,
            &mut C::default_finalizer(),
        )?))
    }
}

macro_rules! define_config_params {
    ($($(#[doc = $doc:expr])* $id:literal => $ident:ident($($ty:tt)*)),*$(,)?) => {$(
        $(#[doc = $doc])*
        pub struct $ident;

        impl<'a, C> KnownConfigParam<'a, C> for $ident
        where
            for<'c> C: DefaultFinalizer + 'c
        {
            const ID: u32 = $id;

            define_config_params!(@wrapper $($ty)*);
        }
    )*};

    (@wrapper $wrapper:ident => $($ty:tt)*) => {
        type Value = $($ty)*;
        type Wrapper = $wrapper<Self::Value>;
    };
    (@wrapper $($ty:tt)*) => {
        type Value = $($ty)*;
        type Wrapper = ParamIdentity<Self::Value>;
    };
}

define_config_params! {
    /// Configuration account address (in masterchain).
    0 => ConfigParam0(CellHash),
    /// Elector account address (in masterchain).
    1 => ConfigParam1(CellHash),
    /// Minter account address (in masterchain).
    2 => ConfigParam2(CellHash),
    /// Fee collector account address (in masterchain).
    3 => ConfigParam3(CellHash),
    /// DNS root account address (in masterchain).
    4 => ConfigParam4(CellHash),

    /// Mint new price and mint add price (unused).
    6 => ConfigParam6(CellSlice<'a, C>),

    /// Target amount of minted extra currencies.
    7 => ConfigParam7(ExtraCurrencyCollection<C>),

    /// The lowest supported block version and required capabilities.
    ///
    /// Contains a [`GlobalVersion`].
    8 => ConfigParam8(GlobalVersion),

    /// Params that must be present in config.
    9 => ConfigParam9(NonEmptyDict => Dict<C, u32, ()>),
    /// Params that have a different set of update requirements.
    10 => ConfigParam10(NonEmptyDict => Dict<C, u32, ()>),

    /// Config voting setup params.
    ///
    /// Contains a [`ConfigVotingSetup`].
    11 => ConfigParam11(ConfigVotingSetup<C>),

    /// Known workchain descriptions.
    ///
    /// Contains a dictionary with workchain id as key and [`WorkchainDescription`] as value.
    12 => ConfigParam12(Dict<C, i32, WorkchainDescription>),

    /// Complaint pricing.
    13 => ConfigParam13(CellSlice<'a, C>),

    /// Block creation reward for masterchain and basechain.
    ///
    /// Contains a [`BlockCreationReward`].
    14 => ConfigParam14(BlockCreationReward),
    /// Validators election timings.
    ///
    /// Contains [`ElectionTimings`].
    15 => ConfigParam15(ElectionTimings),
    /// Range of number of validators.
    ///
    /// Contains a [`ValidatorCountParams`].
    16 => ConfigParam16(ValidatorCountParams),
    /// Validator stake range and factor.
    ///
    /// Contains [`ValidatorStakeParams`]
    17 => ConfigParam17(ValidatorStakeParams),
    /// Storage prices for different intervals of time.
    ///
    /// Contains a dictionary with a history of all [`StoragePrices`].
    18 => ConfigParam18(NonEmptyDict => Dict<C, u32, StoragePrices>),

    /// Masterchain gas limits and prices.
    ///
    /// Contains [`GasLimitsPrices`].
    20 => ConfigParam20(GasLimitsPrices),
    /// Base workchain gas limits and prices.
    ///
    /// Contains [`GasLimitsPrices`].
    21 => ConfigParam21(GasLimitsPrices),

    /// Masterchain block limits.
    ///
    /// Contains [`BlockLimits`].
    22 => ConfigParam22(BlockLimits),
    /// Base workchain block limits.
    ///
    /// Contains [`BlockLimits`].
    23 => ConfigParam23(BlockLimits),

    /// Message forwarding prices for masterchain.
    ///
    /// Contains [`MsgForwardPrices`].
    24 => ConfigParam24(MsgForwardPrices),
    /// Message forwarding prices for base workchain.
    ///
    /// Contains [`MsgForwardPrices`].
    25 => ConfigParam25(MsgForwardPrices),

    /// Catchain configuration params.
    ///
    /// Contains a [`CatchainConfig`].
    28 => ConfigParam28(CatchainConfig),
    /// Consensus configuration params.
    ///
    /// Contains a [`ConsensusConfig`].
    29 => ConfigParam29(ConsensusConfig),
    /// Delector configuration params.
    30 => ConfigParam30(CellSlice<'a, C>),
    /// Fundamental smartcontract addresses.
    ///
    /// Contains a dictionary with addresses (in masterchain) of fundamental contracts as keys.
    31 => ConfigParam31(Dict<C, CellHash, ()>),

    /// Previous validator set.
    ///
    /// Contains a [`ValidatorSet`].
    32 => ConfigParam32(ValidatorSet),
    /// Previous temporary validator set.
    ///
    /// Contains a [`ValidatorSet`].
    33 => ConfigParam33(ValidatorSet),
    /// Current validator set.
    ///
    /// Contains a [`ValidatorSet`].
    34 => ConfigParam34(ValidatorSet),
    /// Current temporary validator set.
    ///
    /// Contains a [`ValidatorSet`].
    35 => ConfigParam35(ValidatorSet),
    /// Next validator set.
    ///
    /// Contains a [`ValidatorSet`].
    36 => ConfigParam36(ValidatorSet),
    /// Next temporary validator set.
    ///
    /// Contains a [`ValidatorSet`].
    37 => ConfigParam37(ValidatorSet),
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroU32;

    use super::*;
    use crate::RcBoc;

    #[test]
    fn simple_config() {
        let data = RcBoc::decode_base64("te6ccgECigEACEcAAUBVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVQECA81AJwIBA6igAwErEmPiYqZj4mKmABIAEgAAAAAAAAEywAQCAssIBQIBzgcGAFsU46BJ4pS4JJ40y9+tMdJ+2UZSrWUYdAMGECTAPA6JCxkhzRDlgAAAAAAAAARgAFsU46BJ4qSwPeRXXsxbNR+ZG7acHCeQGDIdHXwheeUnrv+uWnnLwAAAAAAAAARgAgEgGAkCASARCgIBIA4LAgEgDQwAWxTjoEnivOLxRUsh4pqwwYDC5CbuUQzrlTlJWmx4WBsm73403yvAAAAAAAAABGAAWxTjoEnipEVVIGFXb2h5kaGj2+bKiY1Wtr/FuQeBNBMvRzSfxhoAAAAAAAAABGACASAQDwBbFOOgSeKopXdt+fCds5ntUhIOsNXkYbj5UIkmFyhFQ4V2eX5kcEAAAAAAAAAEYABbFOOgSeK7bF/tR9yQrsDwRYocvKqVQLgeDnCeipEFJKwgnui9lIAAAAAAAAAEYAIBIBUSAgEgFBMAWxTjoEnilXlgl2Jiiq6BCJ3GcSOA4xOysg/BWm/m26L7iYdqEP5AAAAAAAAABGAAWxTjoEnigt6MIP1qpth6VscY2x4U8Yw9Rmn57fSVpyCdARyX43VAAAAAAAAABGACASAXFgBbFOOgSeKVabQ2kXWQF5rQ/Rl1169o4fzyg2LJkTLG+dThWLxJ24AAAAAAAAAEYABbFOOgSeKCrBvt4bbyM115q64GJlTo0A/dS9A3ceKv56pbmZr+PAAAAAAAAAAEYAIBICAZAgEgHRoCASAcGwBbFOOgSeKv6qrO94YQCazGRAE1gzwmlUhOnbLEPtOQ8D74ZGtAeMAAAAAAAAAEYABbFOOgSeKqppP4XmzrZu1Za6ySbxpGSKRXLFGsk9iTkrN0wo7i9IAAAAAAAAAEYAIBIB8eAFsU46BJ4quHqig7MHynGHSf+WUQJIBOspNXVgaYAz84j6fm3ohwgAAAAAAAAARgAFsU46BJ4qnoJiJhdpbHvpPV9wIegPu1RQoihpxYke7vl7ei5pWmgAAAAAAAAARgAgEgJCECASAjIgBbFOOgSeKuSoXlzPuGb0EsSFmY9BULRTWePsppZPn/KbLfbpNGV0AAAAAAAAAEYABbFOOgSeKe2Eau86GX6XsWzLQDJsb8zoYpq7g7I4wkwSSXksXQVEAAAAAAAAAEYAIBICYlAFsU46BJ4pebUOgp0bJVLwzeXikEYPvFLw9IzcRflezT8T4PaADBAAAAAAAAAARgAFsU46BJ4rywnl7s1R2vaNf9ekUNmjKGN+10IqCq6jC4AmJq3SwIQAAAAAAAAARgAgEgTigCASA8KQIBIDcqAgEgMisBAVgsAQHALQIBSC8uAEK/t3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3cCASAxMABBv2ZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZnAAPfsAIBIDUzAQEgNAA+1wEDAAAH0AAAPoAAAAADAAAACAAAAAQAIAAAACAAAAEBIDYAJMIBAAAA+gAAAPoAAAPoAAAACwIBSDo4AQEgOQBC6gAAAAAAAYagAAAAAABkAAAAAAAAJxAAAAABgABVVVVVAQEgOwBC6gAAAAAAmJaAAAAAACcQAAAAAAAPQkAAAAABgABVVVVVAgEgRj0CASBBPgIBID8/AQEgQABQXcMAAgAAAAgAAAAQAADDAA27oAAST4AAHoSAwwAAA+gAABOIAAAnEAIBIERCAQEgQwCU0QAAAAAAAAPoAAAAAAAPQkDeAAAAAABkAAAAAAAAAA9CQAAAAAAF9eEAAAAAAAAAJxAAAAAAAJiWgAAAAAAF9eEAAAAAADuaygABASBFAJTRAAAAAAAAA+gAAAAAAJiWgN4AAAAAJxAAAAAAAAAAD0JAAAAAAAX14QAAAAAAAAAnEAAAAAAAmJaAAAAAAAX14QAAAAAAO5rKAAIBIElHAQFISABN0GYAAAAAAAAAAAAAAACAAAAAAAAA+gAAAAAAAAH0AAAAAAAD0JBAAgEgTEoBASBLADFgkYTnKgAHI4byb8EAAGWvMQekAAAAMAAIAQEgTQAMA+gAZAANAgEgf08CASBZUAIBIFZRAgEgVFIBASBTACAAAAOEAAABwgAAADIAAAHCAQEgVQAEawABAUhXAQHAWAC30FMx8TFTAAAEcABgqjzoUjr8GguE9ZXTyr3sJMV5oZEkTzCdboG9KrVxcxf0sVbdfJgWj8viBjNa/O8exdRvyYXpnis11WJ+U2/QgAAAAA/////4AAAAAAAAAAQCASBoWgIBIF9bAQEgXAICkV5dACo2BAcEAgBMS0ABMS0AAAAAAgAAA+gAKjYCAwICAA9CQACYloAAAAABAAAB9AEBIGACASBjYQIJt///8GBiewAB/AIC2WZkAgFiZW8CASB5eQIBIHRnAgHOfHwCASB9aQEBIGoCA81AbGsAA6igAgEgdG0CASBxbgIBIHBvAAHUAgFIfHwCASBzcgIBIHd3AgEgd3kCASB7dQIBIHh2AgEgeXcCASB8fAIBIHp5AAFIAAFYAgHUfHwAASABASB+ABrEAAAAIwAAAAAABxeuAgEggoABAfSBAAFAAgEghYMBAUiEAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIBIIiGAQEghwBAMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMBASCJAEBVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVQ==").unwrap();
        let blockchain_config = BlockchainConfig::load_from(&mut data.as_slice()).unwrap();

        assert_eq!(
            blockchain_config.get::<ConfigParam0>().unwrap(),
            Some([0x55; 32])
        );
        assert_eq!(
            blockchain_config.get::<ConfigParam1>().unwrap(),
            Some([0x33; 32])
        );
        assert_eq!(
            blockchain_config.get::<ConfigParam2>().unwrap(),
            Some([0x00; 32])
        );
        assert_eq!(blockchain_config.get::<ConfigParam3>().unwrap(), None);
        assert_eq!(blockchain_config.get::<ConfigParam4>().unwrap(), None);

        assert!(blockchain_config.get::<ConfigParam6>().unwrap().is_none());

        assert!(blockchain_config.get::<ConfigParam7>().unwrap().is_some());

        assert_eq!(
            blockchain_config.get::<ConfigParam8>().unwrap(),
            Some(GlobalVersion {
                version: 35,
                capabilities: 0x717ae,
            })
        );

        let mandatory_params = blockchain_config.get::<ConfigParam9>().unwrap().unwrap();
        for param in mandatory_params.keys() {
            param.unwrap();
        }

        let critical_params = blockchain_config.get::<ConfigParam10>().unwrap().unwrap();
        for param in critical_params.keys() {
            param.unwrap();
        }

        blockchain_config.get::<ConfigParam11>().unwrap().unwrap();

        let workchains = blockchain_config.get::<ConfigParam12>().unwrap().unwrap();
        for entry in workchains.iter() {
            let (id, descr) = entry.unwrap();
            println!("{id}: {descr:#?}");
        }

        assert!(blockchain_config.get::<ConfigParam13>().unwrap().is_none());

        let reward = blockchain_config.get::<ConfigParam14>().unwrap().unwrap();
        println!("{reward:#?}");

        let timings = blockchain_config.get::<ConfigParam15>().unwrap().unwrap();
        assert_eq!(
            timings,
            ElectionTimings {
                validators_elected_for: 900,
                elections_start_before: 450,
                elections_end_before: 50,
                stake_held_for: 450,
            }
        );

        let validator_count = blockchain_config.get::<ConfigParam16>().unwrap().unwrap();
        assert_eq!(
            validator_count,
            ValidatorCountParams {
                max_validators: 1000,
                max_main_validators: 100,
                min_validators: 13,
            }
        );

        let validator_stakes = blockchain_config.get::<ConfigParam17>().unwrap().unwrap();
        assert_eq!(
            validator_stakes,
            ValidatorStakeParams {
                min_stake: Tokens::new(10000000000000),
                max_stake: Tokens::new(10000000000000000),
                min_total_stake: Tokens::new(100000000000000),
                max_stake_factor: 3 << 16,
            }
        );

        let storage_prices = blockchain_config.get::<ConfigParam18>().unwrap().unwrap();
        for entry in storage_prices.iter() {
            let (i, entry) = entry.unwrap();
            println!("{i}: {entry:#?}");
        }

        let mc_prices = blockchain_config.get::<ConfigParam20>().unwrap().unwrap();
        assert_eq!(
            mc_prices,
            GasLimitsPrices {
                gas_price: 655360000,
                gas_limit: 1000000,
                special_gas_limit: 100000000,
                gas_credit: 10000,
                block_gas_limit: 10000000,
                freeze_due_limit: 100000000,
                delete_due_limit: 1000000000,
                flat_gas_limit: 1000,
                flat_gas_price: 10000000,
            }
        );

        let sc_prices = blockchain_config.get::<ConfigParam21>().unwrap().unwrap();
        assert_eq!(
            sc_prices,
            GasLimitsPrices {
                gas_price: 6553600,
                gas_limit: 1000000,
                special_gas_limit: 100000000,
                gas_credit: 10000,
                block_gas_limit: 10000000,
                freeze_due_limit: 100000000,
                delete_due_limit: 1000000000,
                flat_gas_limit: 1000,
                flat_gas_price: 1000000,
            }
        );

        let mc_limits = blockchain_config.get::<ConfigParam22>().unwrap().unwrap();
        assert_eq!(
            mc_limits,
            BlockLimits {
                bytes: BlockParamLimits {
                    underload: 131072,
                    soft_limit: 524288,
                    hard_limit: 1048576,
                },
                gas: BlockParamLimits {
                    underload: 900000,
                    soft_limit: 1200000,
                    hard_limit: 2000000,
                },
                lt_delta: BlockParamLimits {
                    underload: 1000,
                    soft_limit: 5000,
                    hard_limit: 10000,
                },
            }
        );

        let sc_limits = blockchain_config.get::<ConfigParam23>().unwrap().unwrap();
        assert_eq!(sc_limits, mc_limits);

        let mc_msg_fwd_prices = blockchain_config.get::<ConfigParam24>().unwrap().unwrap();
        assert_eq!(
            mc_msg_fwd_prices,
            MsgForwardPrices {
                lump_price: 10000000,
                bit_price: 655360000,
                cell_price: 65536000000,
                ihr_price_factor: 98304,
                first_frac: 21845,
                next_frac: 21845,
            }
        );

        let sc_msg_fwd_prices = blockchain_config.get::<ConfigParam25>().unwrap().unwrap();
        assert_eq!(
            sc_msg_fwd_prices,
            MsgForwardPrices {
                lump_price: 100000,
                bit_price: 6553600,
                cell_price: 655360000,
                ihr_price_factor: 98304,
                first_frac: 21845,
                next_frac: 21845,
            }
        );

        let catchain_config = blockchain_config.get::<ConfigParam28>().unwrap().unwrap();
        assert_eq!(
            catchain_config,
            CatchainConfig {
                isolate_mc_validators: false,
                shuffle_mc_validators: true,
                mc_catchain_lifetime: 250,
                shard_catchain_lifetime: 250,
                shard_validators_lifetime: 1000,
                shard_validators_num: 11,
            }
        );

        let consensus_config = blockchain_config.get::<ConfigParam29>().unwrap().unwrap();
        assert_eq!(
            consensus_config,
            ConsensusConfig {
                new_catchain_ids: false,
                round_candidates: NonZeroU32::new(3).unwrap(),
                next_candidate_delay_ms: 2000,
                consensus_timeout_ms: 16000,
                fast_attempts: 3,
                attempt_duration: 8,
                catchain_max_deps: 4,
                max_block_bytes: 2097152,
                max_collated_bytes: 2097152,
            }
        );

        assert!(blockchain_config.get::<ConfigParam30>().unwrap().is_none());

        let fundamental_smc = blockchain_config.get::<ConfigParam31>().unwrap().unwrap();
        for entry in fundamental_smc.keys() {
            let address = entry.unwrap();
            println!("{}", DisplayHash(&address));
        }

        assert!(blockchain_config.get::<ConfigParam32>().unwrap().is_none());
        assert!(blockchain_config.get::<ConfigParam33>().unwrap().is_none());

        let current_validator_set = blockchain_config.get::<ConfigParam34>().unwrap().unwrap();
        println!("current_vset: {current_validator_set:#?}");

        assert!(blockchain_config.get::<ConfigParam35>().unwrap().is_none());
        assert!(blockchain_config.get::<ConfigParam36>().unwrap().is_none());
        assert!(blockchain_config.get::<ConfigParam37>().unwrap().is_none());
    }
}
