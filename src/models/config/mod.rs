//! Blockchain config and params.

use crate::cell::*;
use crate::dict::{Dict, DictKey};
use crate::error::Error;
use crate::num::Tokens;
use crate::util::*;

use crate::models::currency::ExtraCurrencyCollection;
use crate::models::global_version::GlobalVersion;

pub use self::params::*;

mod params;

/// Blockchain config.
#[derive(CustomDebug, CustomClone, CustomEq)]
pub struct BlockchainConfig {
    /// Configuration contract address.
    #[debug(with = "DisplayHash")]
    pub address: CellHash,
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
    pub fn get_fundamental_addresses(&self) -> Result<Dict<CellHash, ()>, Error> {
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
        let Some(mut slice) = ok!(self.get_raw(T::ID)) else { return Ok(None); };
        match <T::Wrapper as Load<'a>>::load_from(&mut slice) {
            Ok(wrapped) => Ok(Some(wrapped.into_inner())),
            Err(e) => Err(e),
        }
    }

    /// Tries to get a raw parameter from the blockchain config.
    pub fn get_raw(&self, id: u32) -> Result<Option<CellSlice<'_>>, Error> {
        match ok!(self.params.get_raw(id)) {
            Some(slice) => match slice.get_reference(0) {
                Ok(cell) => Ok(Some(cell.as_slice())),
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
    31 => ConfigParam31(Dict<CellHash, ()>),

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
    use crate::prelude::Boc;

    #[test]
    fn simple_config() {
        let data = Boc::decode_base64("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").unwrap();
        let blockchain_config = data.parse::<BlockchainConfig>().unwrap();

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
                capabilities: 0x717ae.into(),
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

    #[test]
    fn prod_config() {
        fn check_config(data: &str) {
            let data = Boc::decode_base64(data).unwrap();
            let config = data.parse::<BlockchainConfig>().unwrap();

            assert_eq!(config.get_elector_address().unwrap(), [0x33; 32]);
            assert_eq!(config.get_minter_address().unwrap(), [0x00; 32]);
            assert_eq!(config.get_fee_collector_address().unwrap(), [0x33; 32]);
            config.get_global_version().unwrap();

            let mandatory_params = config.get_mandatory_params().unwrap();
            let mandatory_params = mandatory_params
                .keys()
                .collect::<Result<Vec<_>, _>>()
                .unwrap();
            assert_eq!(
                mandatory_params,
                [0, 1, 9, 10, 12, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 28, 34]
            );

            let critical_params = config.get_critical_params().unwrap();
            let critical_params = critical_params
                .keys()
                .collect::<Result<Vec<_>, _>>()
                .unwrap();
            assert_eq!(
                critical_params,
                [0, 1, 9, 10, 12, 14, 15, 16, 17, 32, 34, 36, 4294966295, 4294966296, 4294966297]
            );

            let workchains = config.get_workchains().unwrap();
            for entry in workchains.iter() {
                entry.unwrap();
            }

            config.get_block_creation_rewards().unwrap();
            config.get_election_timings().unwrap();
            config.get_validator_count_params().unwrap();
            config.get_validator_stake_params().unwrap();

            let storage_prices = config.get_storage_prices().unwrap();
            for entry in storage_prices.iter() {
                entry.unwrap();
            }

            config.get_gas_prices(true).unwrap();
            config.get_gas_prices(false).unwrap();
            config.get_block_limits(true).unwrap();
            config.get_block_limits(false).unwrap();
            config.get_msg_forward_prices(true).unwrap();
            config.get_msg_forward_prices(false).unwrap();

            config.get_catchain_config().unwrap();
            config.get_consensus_config().unwrap();

            let fundamental_addresses = config.get_fundamental_addresses().unwrap();
            for entry in fundamental_addresses.keys() {
                entry.unwrap();
            }

            assert!(config.contains_prev_validator_set().unwrap());
            config.contains_next_validator_set().unwrap();

            config.get_current_validator_set().unwrap();
        }

        // Some old config from the network beginning
        check_config("te6ccgICARIAAQAAHdMAAAFAVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVUAARIDslriTVrFHKUwfpRvh/E8hbAS170SfSOdv1M9vT/46WgADs1AAKMAAgIBYgA2AAMRAZUWksSbOq+gkVxTwkaBJEOFYq6V1LZH4O0sGvAW//JYAAfUAAQBKxJetp1fXredXwAZABkP////////9sAABQICywAXAAYCASAACAAHAJvbnHQJPFT/mwMUqtzWJOV0MYd7rdZpQCCEOM3ZO9nvW0T1ECfTCAN1nyKYN1n1KzpenFgD0R1pwOtcCd5QvmuUc63sndFWzToZpOTkgoQCASAAEAAJAgEgAA0ACgIBIAAMAAsAmxzjoEninefr6TK/MJHkCKUDxMG/l39EMdDe8hBHXqf8hafQK+eAG6z5FMG6z7+VMHbObJ7H3B3yz4TADP7EHnksI/2I0ZKBZpwGqZ25YACbHOOgSeKgMVpUJdDJUo3T0sVVaM2OEfQt7fq+lFts4AeL6oBYAwAbrPkUwbrPggBsLDwUgmS1h6XP4smY896/FzqFz/39wA13k7Y9zCPgAgEgAA8ADgCbHOOgSeKnBu3Kp3SUV/FwpQ4gd3HJAlFQGhyCJnz8rj2Mv2d7MoAbrPkUwbrPmdj+/1qMZoxZl1e5f00LITOeZ4Xa8YvytXmuDHkUwEqgAJsc46BJ4oPYs8fX2DaGPZ6BYGrASPm0K+V4OpMQdqFDXF7E7sA1QBus+RTBus+qp/NhUubdtnq0nwgI76IjCf+3/afGA9/ai/X4htYV2SACASAAFAARAgEgABMAEgCbHOOgSeKckZnkLYhAD9La1l9Ket72FMvH/9MJjH6jQpuIw25LuwAbrPkUwbrPhjHsRTQxWtk2f7KqPewL4xCWOaCrX2TrgtPUF5Tqu+UgAJsc46BJ4r2xPoXruZsY/H47NyyAgPH7/bA/cGAiZscaL1DzcuOvQBus+RTBus+2I3FjYzV5cnMtT3shFvozd62JdA1TVAnRwwBTZ3HINeACASAAFgAVAJsc46BJ4olpoEUdDd9igg+niwV3kiA82WCQ9qgoHi2zcFfojGbfABus+RTBus+sMu+KgX22KjVPILn95dwuoUHFG5LP/T6d/vfVRe1z72AAmxzjoEniqOC8PYFPWgndSQU4am/40LWupnfKo0kdxV5KPCwZ61hAG6z5FMG6z4mXujjqh+9BIZCzfA8TKC5qQ8IO93879QTRDbomaGM44AIBIAAnABgCASAAIAAZAgEgAB0AGgIBIAAcABsAmxzjoEniruljJXi3612LFYBQIlKmiA0M6ns+hsdYv3VIxSmjp2RAG6z5FMG6z6EpKPDQxBwQ+DVUPpkmwCRGANMLKFJlBsm8FspbzKWcYACbHOOgSeK+XFX6sqxk0vbtWO7g7Ytm1jkNNZrQDYVgZ9q4gGBfm4AbrPkUwbrPjhyT3GCi9c9oQYXFnXkZb2RTKfw3uN9QMHXANXdVzK3gAgEgAB8AHgCbHOOgSeKyF0Xt8cnzCyCY1NjOY/rzkXVjVzzgc/dDxwudIu7iZIAbrPkUwbrPpKB5d911TZvPPQrQ5sDaaOFTzU0E9nSl5ydaMMs6cDJgAJsc46BJ4o13kKnVM8maaGb8RXWQ7NgbWG2pf1oVJaKdvgrazUAUABus+RTBus+uDN2hN6xxybDfbuhzHZoDfCtEsCMZfsvzOcS5Y4s8hiACASAAJAAhAgEgACMAIgCbHOOgSeKECGt+HsLYW/7L3p6Zd0JOnkndr35D5PUtyKvkFQiQGUA3WfIpg3WfENMgXR86Z3xVH4S3scq5A97tkNzSOv6WFjaWGt+2F8jgAJsc46BJ4oEm7xeZWeEoIHN9E1xGcw4m1ZQkcVVgiU0xdIOUzEKbADdZ8imDdZ8jhTp7dOTnKzCwECctM+JIWI+wPXkrE53Wkh2GspgssuACASAAJgAlAJsc46BJ4qjQBJWUaIRgQzIZDK7u5HL/8V8niFDt/ASxThQqljVxwDdZ8imDdZ84lR4tFuvuS3THt81Mcf4dDxvYK/+g+zK3K6SKRNBlkWAAmxzjoEnig8xPDvX7aDWx5sVZ2pMwE7/1ZozTjfBCQGn5Dy83qSeAN1nyKYN1nysuZQXZfBJxnVmPHL9kMoagovTlr4p+Z8wgqP7GHGSWIAIBIAAvACgCASAALAApAgEgACsAKgCbHOOgSeKnlfCQ0pzDq3oIFuWCAAk5Ml/Pvle2dyn2esG0W4kn4kA3WfIpg3WfHutt6pHdze93MZWj8E5On6HOyPVJ1SuLTo86WF0DwGigAJsc46BJ4rxGYEuHPAMGKrRZkx5q0Wg0KlV808iuJqquCb6jDAIeQDdZ8imDdZ8u0hLeUfcZZQZfEIwoxyLkSMB/lKU2168H13UraJaelGACASAALgAtAJsc46BJ4pblifmi6NyvQ+XKnON76epNzKfb4+QYcbA3AnZc5kwsADdZ8imDdZ8yyHSAwe1TdpLIsOzci+gtvXmys8RJn+ge3R5p7F024uAAmxzjoEniiFrdbTMnQommz9xmZsRcmdayrzvyiQMpCXG1gJlGSTOAN1nyKYN1nwLsV3Gx3YMoqU5cAJ8cCs3S+WUaRv3Slh/iQJIk2zoo4AIBIAAzADACASAAMgAxAJsc46BJ4oAmvHmYX6yqgQECZzMqiqphbn+gY9nS2LDtSGdl3BJWwDdZ8imDdZ8I/rhDFjM7M7VmpvQGaXGY+b3bYMUIIO8halP4SjhE6+AAmxzjoEnitzqG0tbvrqQtupETEdaFLVQBudUgVb9ti6VeNNpqsBiAN1nyKYN1nxasBhpNJrX7m+JLdEChINGppl1f2Udgr+H7buAIk7384AIBIAA1ADQAmxzjoEnigRWcTO1BZynm7A/Z2m/lOTfmmVtBYWXe6PHatTHfEU9AN1nyKYN1nxS270N3SPZv9WY24ukXFqbmAjSCRtIIabG5c85lwOAwYACbHOOgSeKWrRA/LpXdDqAduYrmjdQnyTNpshWKAyYTnhD8h/doYIA3WfIpg3WfNYZrsc7yVh8smk0xF4E+l3YLm/U5Oq2ls3ulVEv89pbgAgEgAGgANxEB0Lkzg+0sXArm25WXxywwL37Ks6fQsPgvjKcmFcsdtOIAB0gAOAErEl61ipdetoqXABgAGA/////////7wAA5AgLLAEkAOgIBSABCADsCASAAPwA8AgEgAD4APQCbHOOgSeKygynewtPqKKZtlYCgegxmmc0HqVsBw6hZvKRg1zQXR0AdF0s8AVjPYiZiVwvedPoqPAOp/cl+pQuPqIkspmeQpIJATrjSSyYgAJsc46BJ4rvHnkS1azYqjPBB4gKnKirs+nmt4LDaQ500eWlNiOFtAB0XSzwBWM9CxBh+DvLKlQn6bHAcAJSGht3/kx5ugwp9OYOGFwxB76ACASAAQQBAAJsc46BJ4rSUcfQUh2Llfc2euAekJzewLYiCC51BzVg8qnFETJbygB0XSzwBWM9vCrBipbBWrR0XdiVrQpA93kcpSPkYFGQwtV6LAlb572AAmxzjoEniiyqF8/Pqjjtwf48ItAPeOct4rusXBjarfvw4jZL6oNLAHRdLPAFYz19r8FPwt4Cy75TtfMlebPhrll0MpkFlQyZFsh/fFRH2oAIBIABGAEMCASAARQBEAJsc46BJ4oT3xrV8E2ujQ2H+39ntDdDvxr9eI7H6WZgsPqc7xx3sgB0XSzwBWM9dcKvri4H/AThE/NPMJTkpl8TozutKscHav4veb0dh4uAAmxzjoEniooH+Xmv87PEcsiXSWRimrDn4eGW7QNU9t7i/I3RmitrAHRdLPAFYz3MQeAfXLxxa5bjotm2VanbhRtvT4VFJ8aPcfLMBxxKXYAIBIABIAEcAmxzjoEniny3as8ujiZP/5POwmM7l1KI4h8YcsCfa8iTWYBCtkm+AHRdLPAFYz2elWxeRBkMBye6eveM9x1njEnUGkHO39kiAdfGu6Mor4ACbHOOgSeKxrcHjmn/H4ZQpQKCoFFMcIkOQoy4nGM9FZQAtBYg3O8AdF0s8AVjPcF+J0c3rIcHx9F08Y6PE2wVVECYimrR/LUMXkcUoeV0gAgEgAFkASgIBIABSAEsCASAATwBMAgEgAE4ATQCbHOOgSeKPmUF1cCDJM21Y24z3oorVMeff6RppksopbXW8yZ1gqMAdF0s8AVjPT/RMAWkSK5YMNJuuHcscPAAgukV3+jU35mqi67Spz3wgAJsc46BJ4rrx3pPGdmgVov31KXz8m5shILvjyNVsRdOEB7FhSdCaAB0XSzwBWM9qyV+FQHIlpAARz5V9OOdHedqcHgxBPIRU4PTB7vxYtOACASAAUQBQAJsc46BJ4oYbIZ+huk2RCiRjYHYHGaTS2FUV8cBHhhqHL7BgOvGfQB0XSzwBWM9VDLPWjVUiLa+P1RtZpw1jhqTCcpb/2tOH/8s4UIcf+GAAmxzjoEnikuG5l8vKjT3ox7qBvZL2XsM/HZu5HUKD02+NSmzwGiTAHRdLPAFYz0dnP6bcV/NJ/nqdywHO0iltvLYZSXnYT9I0a7PttbJC4AIBIABWAFMCASAAVQBUAJsc46BJ4qHFegaHb0kW1pb5gj8UDU2SqYOYorjkByPiTfIZFARKQCLoAgfSNHhydDI3gYelaj3M8jK5WdiblOmvs9SaCQ900heUPzGi9KAAmxzjoEnilcGvxAbV8NUyO+Jm7+lEfNj2DUtINcj+feRVbVfoNXxAOi6WeAKxnqfSsgqN+4GvTQHnDwB1djSA2duBibFPYAHbkXmAezbKIAIBIABYAFcAmxzjoEnirOPg2BnLxa5abMwSANH9NVHYH8VDXmVJIf3mmPnHkdBAOi6WeAKxnpFFahmNdGPLp0NPxSa+7P58iro+n5Sxsz35tMRegbhAIACbHOOgSeKLyT+AL/IOJeO02WBUW9VjSpvi5Oai4NQEDY/sfFHZdMA6LpZ4ArGelDyhfGmmTU6nMaJkvtcM8DECTz2xcgpI48tE5KxUXYngAgEgAGEAWgIBIABeAFsCASAAXQBcAJsc46BJ4pYZT6JDGWWnO2iAaDq6RQymj+/ITGhAo5b5Tj9SwWaiwDoulngCsZ6LI8FVjCt4XRSRbVLtJHv12LeTzMP8u7YlwNh3lekoM2AAmxzjoEnipVHv73YPxT4g8u+A6HgrNiUn3m7ajLbjmJq+exTmfuYAOi6WeAKxnpQ2/i3BQF4sqHwiRaOHnHt0xMAlTc3Qv3gv6l4plKf5oAIBIABgAF8AmxzjoEnit4oQ15InRwqlYxHTwVEho2eQqTg+7dFHon8O8mjhl94AOi6WeAKxnojInU9DLf8KZuRaTyN12nplch0IWtuLB8Pn8C9kj92+oACbHOOgSeKO5FK7hil7ic9SH34MhLcdnRf3n64KteF3qCIaMQ/EDgA6LpZ4ArGephCMYfUVQrsq5hMYL0snqc7vN5homN+WlA973r9hrcbgAgEgAGUAYgIBIABkAGMAmxzjoEnitjcHA9fwI6/Tc1goeZwtDMUpYrROMx69puiyT76izfjAOi6WeAKxnq1PMOuK2eELtJd3O2BXbxo+bhldD1VXzyL0VdcAbs2ZYACbHOOgSeKN4Rt7ha9fy959KW2mi+2EqtgfAftSZPiIgSFpL5pmRkA6LpZ4ArGeoXJSx9eMpVXmzAElph2kenX/VQAr84KPO9URI92Sh6PgAgEgAGcAZgCbHOOgSeKJvlLCB8VSPB5TUCmyRvftn/F06gHXT4YCTsXqSBeORcA6LpZ4ArGeiE8GOUQd0EbTnHXwnVtiaEOpr65XutXnINZqa1/cO28gAJsc46BJ4qRuOFrH4IjLMl209AQyRnPDECHE1l0/mBv9oQdlxKXDADoulngCsZ633XRiOd/A7FoJoSLgoDb4GSezCDjcg2RxT1JOZdgA0SARAUWvvc8LoJZ/tngN2f4DkOqWtaJ2P7Ymay/3s2lF/zbIAAdIAGkBKxJetAP3XrWKlwAdAB0AAAAAAAAB7cAAagICywCEAGsCASAAdQBsAgEgAG4AbQBb0px0CTxVn/FnlyzGyZFmsPvXIhZJjFxeWxwOx4F518E6HnKS9GAAAAAAAAAAjAIBIAByAG8CASAAcQBwAFsU46BJ4rjI2eaml91stlCZdBNZ4qJcZPoV9pmptMZKMHDPJFGJQAAAAAAAAARgAFsU46BJ4ounwtubvFlKPwYTYUn6IrJioESDEUJBExqruDKX3L/zwAAAAAAAAARgAgEgAHQAcwBbFOOgSeKYpusl+d6B9RSaDq+SDwxx55Pjz6mxN+NYnqIe02Q6kcAAAAAAAAAEYABbFOOgSeKutp4jZtg72HP6CUAq8zjoHm0F3fVoGl4J/jgEaOVA0IAAAAAAAAAEYAIBIAB9AHYCASAAegB3AgEgAHkAeABbFOOgSeKNYsuTROffJ9OITkK8q9Izi4vaJplYDD0o0T+/8va/KEAAAAAAAAAEYABbFOOgSeK2mT3MeHJzODw6SF4pH7pmP3WWEND1jCaGtRl3DahvAMAAAAAAAAAEYAIBIAB8AHsAWxTjoEnihhvO5GasqDg9MMruU9obIl2qwhJKuhKWnhJ9kD5xkrFAAAAAAAAABGAAWxTjoEnimYMRyX9A05Jsh96OYBoHaXLqZnyTn+ce9SKuMoebGR3AAAAAAAAABGACASAAgQB+AgEgAIAAfwBbFOOgSeKVtJZFNTJB69BBEwHmzfL3U5B0c+dAdVsV3l9rGB3jnAAAAAAAAAAEYABbFOOgSeKXu5LVYZ4mo6CtuqCKwfGDrX5ovewwyG5UvzvaJuHaBMAAAAAAAAAEYAIBIACDAIIAWxTjoEniliYMsW1ZyavhBdHyrATjsbtXtXllTZbMVB7VqzXoiYbAAAAAAAAABGAAWxTjoEnit+Z7nTFOuUgzknmMKywIGxmZe7KIQD2DjSwSzvNscAyAAAAAAAAABGACASAAlACFAgEgAI0AhgIBIACKAIcCASAAiQCIAFsU46BJ4pMotf2HLEbGa9DLc507LxzYaN0Lx5OFfO6+TP895hFAwAAAAAAAAARgAFsU46BJ4rYhqPnk3SojwHLA6OKq9wmT2MksNBZxxnyBB+EYTXV0QAAAAAAAAARgAgEgAIwAiwBbFOOgSeKi4uvoFtDFrcwHabq1ifrtaVH4Y7oFvq17DW8dmnOcDcAAAAAAAAAEYABbFOOgSeKrYliFbxXDhYAq8RynSbBjNYB2yyILWt7ugRGk4fPT/UAAAAAAAAAEYAIBIACRAI4CASAAkACPAFsU46BJ4pF58x6Eq9zuvb9cQQc6coJdXpt1/dyDraD3eUg3BnpCwAAAAAAAAARgAFsU46BJ4ra0wm6Jz7yZEmpgkoxE24M/LkE4LN/mRI7WtjMYf88ggAAAAAAAAARgAgEgAJMAkgBbFOOgSeKSnZqFmTC6kHPtkUcC/834jWSNE/7Ntk54SxVYAjxUQYAAAAAAAAAEYABbFOOgSeKVVhd7ydKuEeNxZ5jAzAlmHMeRFsbcXmk+sLBDw3zTr0AAAAAAAAAEYAIBIACcAJUCASAAmQCWAgEgAJgAlwBbFOOgSeKv1uhb9t6MG1h2zRBaCybaXBcaC/LeTvb/AOONhmHXgAAAAAAAAAAEYABbFOOgSeKb0wUirkrmDB18M0TH23Rfch4CluKFTJMv/+i2V27eCEAAAAAAAAAEYAIBIACbAJoAWxTjoEniiu5+Cd4aN+wCADq0vvtI5IaM8JpZxf25BxDp40UmEN0AAAAAAAAABGAAWxTjoEnimMekIwjG57wHnFtinFaYk9m+22D2uiXZroPA2v8Ls8dAAAAAAAAABGACASAAoACdAgEgAJ8AngBbFOOgSeK9i1BGOBdX7V7N8F6T8ZBqGXEEzQ3y/o1gSzF0ebbhfEAAAAAAAAAEYABbFOOgSeK4OmL/J6T9L/A1NbDAyG65ikSU5AUvqFYiNwmOOu+knsAAAAAAAAAEYAIBIACiAKEAWxTjoEnik0i8vkgQvGlSf/1CbiwMgW45GAVnvyEVr59QAjxzqs4AAAAAAAAABGAAWxTjoEningZHcgXoBe/hk0oRrgHF8cSHjG1nlMaXEPZXsrHL6mRAAAAAAAAABGACASAA0ACkEgHxVpubtihokSMJ5TT50Bk3um29rOeBkQvar3LVVKO6AgAJIAC+AKUCASAAuQCmAgEgALQApwEBWACoAQHAAKkCASAArQCqAgFiAKwAqwBBvyZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmAEG/IiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiIiICASAArwCuAEK/t3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3cCASAAsQCwAEG/ZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmZmcCAWIAswCyAEG+j2TGr7/z3RDYumcHeQrJZw1UDzepRIsDN7qmpakqysgAA99QAgEgALcAtQEBIAC2AD7XAQMAAAfQAAA+gAAAAAMAAAAIAAAABAAgAAAAIAAAAQEgALgAJMIBAAAA+gAAAPoAAAPoAAAABwIBSAC8ALoBASAAuwBC6gAAAAAAD0JAAAAAAAPoAAAAAAABhqAAAAABgABVVVVVAQEgAL0AQuoAAAAAAJiWgAAAAAAnEAAAAAAAD0JAAAAAAYAAVVVVVQIBIADIAL8CASAAwwDAAgEgAMEAwQEBIADCAFBdwwACAAAACAAAABAAAMMAHoSAAJiWgAExLQDDAAAD6AAAE4gAACcQAgEgAMYAxAEBIADFAJTRAAAAAAAAA+gAAAAAAA9CQN4AAAAAA+gAAAAAAAAAD0JAAAAAAAAPQkAAAAAAAAAnEAAAAAAAmJaAAAAAAAX14QAAAAAAO5rKAAEBIADHAJTRAAAAAAAAA+gAAAAAAJiWgN4AAAAAJxAAAAAAAAAAD0JAAAAAAACYloAAAAAAAAAnEAAAAAAAmJaAAAAAAAX14QAAAAAAO5rKAAIBIADLAMkBAUgAygBN0GYAAAAAAAAAAAAAAACAAAAAAAAA+gAAAAAAAAH0AAAAAAAD0JBAAgEgAM4AzAEBIADNADFgkYTnKgAHI4byb8EAAGWvMQekAAAAMAAIAQEgAM8ADAPoAGQADQIBIAEEANECASAA3gDSAgEgANgA0wIBIADWANQBASAA1QAgAAEAAAAAgAAAACAAAACAAAEBIADXABRrRlU/EAQ7msoAAgEgANsA2QEBIADaABUaUXSHboABASAfSAEBIADcAQHAAN0At9BTL1oB+4ACBHAASvghaN+tzMIGVp1VNMeuvfCezAybJ9fO6h762unhSodL16MBUr/kQntF2jLN1cQ67g+vItT+p91+hk3ghVKDPgAAAAAP////+AAAAAAAAAAEAgEgAO0A3xIB9sL0RxqYIhVr7zhAJOCRd6g7bSupgG7buuEpJkx0JOMACSAA5ADgAQEgAOECApEA4wDiACo2BAcEAgBMS0ABMS0AAAAAAgAAA+gAKjYCAwICAA9CQACYloAAAAABAAAB9AEBIADlAgEgAOgA5gIJt///8GAA5wEAAAH8AgLZAOsA6QIBYgDqAPQCASAA/gD+AgEgAPkA7AIBzgEBAQESAWbx6WmV0yTzjLXhJ1WJTU15KdIbOp2sBFjJklmGAP7pAAggAQIA7gEBIADvAgPNQADxAPAAA6igAgEgAPkA8gIBIAD2APMCASAA9QD0AAHUAgFIAQEBAQIBIAD4APcCASAA/AD8AgEgAPwA/gIBIAEAAPoCASAA/QD7AgEgAP4A/AIBIAEBAQECASAA/wD+AAFIAAFYAgHUAQEBAQABIAEBIAEDABrEAAAAAQAAAAAAAAAuAgEgAQoBBQEB9AEGAQHAAQcCASABCQEIABW/////vL0alKIAEAAVvgAAA7yzZw3BVVACASABDQELAQFIAQwAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgEgARABDgEBIAEPAEAzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMwEBIAERAEBVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVQ==");

        // Current config
        check_config("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");
    }
}
