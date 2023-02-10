//! Blockchain config and params.

use crate::cell::*;
use crate::dict::{Dict, DictKey};
use crate::error::Error;
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
    /// Tries to get a parameter from the blockchain config.
    pub fn get<'a, T: KnownConfigParam<'a, C>>(&'a self) -> Result<Option<T::Value>, Error> {
        let mut slice = match self.params.get_raw(T::ID)? {
            Some(slice) => match slice.get_reference(0) {
                Some(cell) => cell.as_slice(),
                None => return Err(Error::CellUnderflow),
            },
            None => return Ok(None),
        };
        match <T::Wrapper as Load<'a, C>>::load_from(&mut slice) {
            Some(wrapped) => Ok(Some(wrapped.into_inner())),
            None => Err(Error::CellUnderflow),
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
    fn into_inner(self) -> T;
}

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

#[repr(transparent)]
pub struct NotEmptyDict<T>(T);

impl<T> ConfigParamWrapper<T> for NotEmptyDict<T> {
    fn into_inner(self) -> T {
        self.0
    }
}

impl<'a, C, K, V> Load<'a, C> for NotEmptyDict<Dict<C, K, V>>
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
    /// Configuration account address.
    0 => ConfigParam0(CellHash),
    /// Elector account address.
    1 => ConfigParam1(CellHash),
    /// Minter account address.
    2 => ConfigParam2(CellHash),
    /// Fee collector account address.
    3 => ConfigParam3(CellHash),
    /// DNS root account address.
    4 => ConfigParam4(CellHash),

    /// Mint new price and mint add price (unused).
    6 => ConfigParam6(CellSlice<'a, C>),
    /// Target amount of minted extra currencies.
    7 => ConfigParam7(ExtraCurrencyCollection<C>),
    /// The lowest supported block version and required capabilities.
    8 => ConfigParam8(GlobalVersion),
    /// Params that must be present in config.
    9 => ConfigParam9(NotEmptyDict => Dict<C, u32, ()>),
    /// Params that have a different set of update requirements.
    10 => ConfigParam10(NotEmptyDict => Dict<C, u32, ()>),
    /// Config voting setup params.
    11 => ConfigParam11(ConfigVotingSetup<C>),
    /// Known workchain descriptions.
    12 => ConfigParam12(Dict<C, i32, WorkchainDescription>),
    /// Complaint pricing.
    13 => ConfigParam13(CellSlice<'a, C>),
    /// Block creation reward for masterchain and basechain.
    14 => ConfigParam14(BlockCreationReward),
    /// Validators election timings.
    15 => ConfigParam15(ElectionTimings),
    /// Range of number of validators.
    16 => ConfigParam16(ValidatorCount),
    /// Validator stake range and factor.
    17 => ConfigParam17(ValidatorStakeParams),
    /// Storage prices for different intervals of time.
    18 => ConfigParam18(NotEmptyDict => Dict<C, u32, StoragePrices>),

    /// Masterchain gas limits and prices.
    20 => ConfigParam20(GasLimitsPrices),
    /// Base workchain gas limits and prices.
    21 => ConfigParam21(GasLimitsPrices),
    /// Masterchain block limits.
    22 => ConfigParam22(BlockLimits),
    /// Base workchain block limits.
    23 => ConfigParam23(BlockLimits),
    /// Message forwarding prices for masterchain.
    24 => ConfigParam24(MsgForwardPrices),
    /// Message forwarding prices for base workchain.
    25 => ConfigParam25(MsgForwardPrices),

    /// Catchain configuration params.
    28 => ConfigParam28(CatchainConfig),
    /// Consensus configuration params.
    29 => ConfigParam29(ConsensusConfig),
    /// Delector configuration params.
    30 => ConfigParam30(CellSlice<'a, C>),
    /// Fundamental smartcontract addresses.
    31 => ConfigParam31(Dict<C, CellHash, ()>),

    /// Previous validator set.
    32 => ConfigParam32(ValidatorSet),
    /// Previous temporary validator set.
    33 => ConfigParam33(ValidatorSet),
    /// Current validator set.
    34 => ConfigParam34(ValidatorSet),
    /// Current temporary validator set.
    35 => ConfigParam35(ValidatorSet),
    /// Next validator set.
    36 => ConfigParam36(ValidatorSet),
    /// Next temporary validator set.
    37 => ConfigParam37(ValidatorSet),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::num::Tokens;
    use crate::RcBoc;
    use std::num::NonZeroU32;

    #[test]
    fn config_params() {
        let data = RcBoc::decode_base64("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").unwrap();
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
            ValidatorCount {
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
        println!("current_vset: {:#?}", current_validator_set);

        assert!(blockchain_config.get::<ConfigParam35>().unwrap().is_none());
        assert!(blockchain_config.get::<ConfigParam36>().unwrap().is_none());
        assert!(blockchain_config.get::<ConfigParam37>().unwrap().is_none());
    }
}
