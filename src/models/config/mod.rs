//! Blockchain config and params.

use crate::cell::*;
use crate::dict::{Dict, DictKey};
use crate::error::Error;
use crate::num::Tokens;

use crate::models::currency::ExtraCurrencyCollection;
use crate::models::global_version::GlobalVersion;

pub use self::params::*;

mod params;

#[cfg(test)]
mod tests;

/// Blockchain config.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct BlockchainConfig {
    /// Configuration contract address.
    pub address: HashBytes,
    /// Configuration parameters.
    pub params: Dict<u32, Cell>,
}

impl Store for BlockchainConfig {
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn Finalizer) -> Result<(), Error> {
        let params_root = match self.params.root() {
            Some(root) => root.clone(),
            None => return Err(Error::InvalidData),
        };
        ok!(builder.store_u256(&self.address));
        builder.store_reference(params_root)
    }
}

impl<'a> Load<'a> for BlockchainConfig {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        Ok(Self {
            address: ok!(slice.load_u256()),
            params: Dict::from(Some(ok!(slice.load_reference_cloned()))),
        })
    }
}

impl BlockchainConfig {
    /// Returns the elector account address (in masterchain).
    ///
    /// Uses [`ConfigParam1`].
    pub fn get_elector_address(&self) -> Result<HashBytes, Error> {
        ok!(self.get::<ConfigParam1>()).ok_or(Error::CellUnderflow)
    }

    /// Returns the minter account address (in masterchain).
    ///
    /// Uses [`ConfigParam2`] with a fallback to [`ConfigParam0`] (config).
    pub fn get_minter_address(&self) -> Result<HashBytes, Error> {
        match ok!(self.get::<ConfigParam2>()) {
            Some(address) => Ok(address),
            None => ok!(self.get::<ConfigParam0>()).ok_or(Error::CellUnderflow),
        }
    }

    /// Returns the fee collector account address (in masterchain).
    ///
    /// Uses [`ConfigParam3`] with a fallback to [`ConfigParam1`] (elector).
    pub fn get_fee_collector_address(&self) -> Result<HashBytes, Error> {
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
    pub fn get_mandatory_params(&self) -> Result<Dict<u32, ()>, Error> {
        ok!(self.get::<ConfigParam9>()).ok_or(Error::CellUnderflow)
    }

    /// Returns a list of params that have a different set of update requirements.
    ///
    /// Uses [`ConfigParam10`].
    pub fn get_critical_params(&self) -> Result<Dict<u32, ()>, Error> {
        ok!(self.get::<ConfigParam10>()).ok_or(Error::CellUnderflow)
    }

    /// Returns a dictionary with workchain descriptions.
    ///
    /// Uses [`ConfigParam12`].
    pub fn get_workchains(&self) -> Result<Dict<i32, WorkchainDescription>, Error> {
        ok!(self.get::<ConfigParam12>()).ok_or(Error::CellUnderflow)
    }

    /// Returns a block creation reward for the specified workchain in tokens.
    ///
    /// Uses [`ConfigParam14`].
    pub fn get_block_creation_reward(&self, masterchain: bool) -> Result<Tokens, Error> {
        let rewards = ok!(self.get_block_creation_rewards());
        Ok(if masterchain {
            rewards.masterchain_block_fee
        } else {
            rewards.basechain_block_fee
        })
    }

    /// Returns a block creation rewards in tokens.
    ///
    /// Uses [`ConfigParam14`].
    pub fn get_block_creation_rewards(&self) -> Result<BlockCreationRewards, Error> {
        ok!(self.get::<ConfigParam14>()).ok_or(Error::CellUnderflow)
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
    pub fn get_storage_prices(&self) -> Result<Dict<u32, StoragePrices>, Error> {
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
    pub fn get_fundamental_addresses(&self) -> Result<Dict<HashBytes, ()>, Error> {
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
    pub fn contains<'a, T: KnownConfigParam<'a>>(&'a self) -> Result<bool, Error> {
        self.params.contains_key(T::ID)
    }

    /// Returns `true` if the config contains a param for the specified id.
    pub fn contains_raw(&self, id: u32) -> Result<bool, Error> {
        self.params.contains_key(id)
    }

    /// Tries to get a parameter from the blockchain config.
    pub fn get<'a, T: KnownConfigParam<'a>>(&'a self) -> Result<Option<T::Value>, Error> {
        let Some(mut slice) = ok!(self.get_raw(T::ID)) else {
            return Ok(None);
        };
        match <T::Wrapper as Load<'a>>::load_from(&mut slice) {
            Ok(wrapped) => Ok(Some(wrapped.into_inner())),
            Err(e) => Err(e),
        }
    }

    /// Tries to get a raw parameter from the blockchain config.
    pub fn get_raw(&self, id: u32) -> Result<Option<CellSlice<'_>>, Error> {
        match ok!(self.params.get_raw(id)) {
            Some(slice) => match slice.get_reference_as_slice(0) {
                Ok(slice) => Ok(Some(slice)),
                Err(e) => Err(e),
            },
            None => Ok(None),
        }
    }
}

/// Marker trait which is implemented for known config params.
pub trait KnownConfigParam<'a> {
    /// Parameter index in a configuration dictionary.
    const ID: u32;

    /// Associated value type.
    type Value;

    /// Value wrapper.
    type Wrapper: ConfigParamWrapper<Self::Value> + Load<'a>;
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

impl<'a, T: Load<'a>> Load<'a> for ParamIdentity<T> {
    #[inline]
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        match T::load_from(slice) {
            Ok(value) => Ok(Self(value)),
            Err(e) => Err(e),
        }
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

impl<'a, K, V> Load<'a> for NonEmptyDict<Dict<K, V>>
where
    K: DictKey,
{
    #[inline]
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        match Dict::load_from_root_ext(slice, &mut Cell::default_finalizer()) {
            Ok(value) => Ok(Self(value)),
            Err(e) => Err(e),
        }
    }
}

macro_rules! define_config_params {
    ($($(#[doc = $doc:expr])* $id:literal => $ident:ident($($ty:tt)*)),*$(,)?) => {$(
        $(#[doc = $doc])*
        pub struct $ident;

        impl<'a> KnownConfigParam<'a> for $ident {
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
    0 => ConfigParam0(HashBytes),
    /// Elector account address (in masterchain).
    1 => ConfigParam1(HashBytes),
    /// Minter account address (in masterchain).
    2 => ConfigParam2(HashBytes),
    /// Fee collector account address (in masterchain).
    3 => ConfigParam3(HashBytes),
    /// DNS root account address (in masterchain).
    4 => ConfigParam4(HashBytes),

    /// Mint new price and mint add price (unused).
    6 => ConfigParam6(CellSlice<'a>),

    /// Target amount of minted extra currencies.
    7 => ConfigParam7(ExtraCurrencyCollection),

    /// The lowest supported block version and required capabilities.
    ///
    /// Contains a [`GlobalVersion`].
    8 => ConfigParam8(GlobalVersion),

    /// Params that must be present in config.
    9 => ConfigParam9(NonEmptyDict => Dict<u32, ()>),
    /// Params that have a different set of update requirements.
    10 => ConfigParam10(NonEmptyDict => Dict<u32, ()>),

    /// Config voting setup params.
    ///
    /// Contains a [`ConfigVotingSetup`].
    11 => ConfigParam11(ConfigVotingSetup),

    /// Known workchain descriptions.
    ///
    /// Contains a dictionary with workchain id as key and [`WorkchainDescription`] as value.
    12 => ConfigParam12(Dict<i32, WorkchainDescription>),

    /// Complaint pricing.
    13 => ConfigParam13(CellSlice<'a>),

    /// Block creation reward for masterchain and basechain.
    ///
    /// Contains a [`BlockCreationRewards`].
    14 => ConfigParam14(BlockCreationRewards),
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
    18 => ConfigParam18(NonEmptyDict => Dict<u32, StoragePrices>),

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
    30 => ConfigParam30(CellSlice<'a>),
    /// Fundamental smartcontract addresses.
    ///
    /// Contains a dictionary with addresses (in masterchain) of fundamental contracts as keys.
    31 => ConfigParam31(Dict<HashBytes, ()>),

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
