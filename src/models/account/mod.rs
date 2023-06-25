//! Account state models.

use crate::cell::*;
use crate::dict::*;
use crate::error::*;
use crate::num::*;

use crate::models::currency::CurrencyCollection;
use crate::models::message::IntAddr;
use crate::models::Lazy;

/// Amount of unique cells and bits for shard states.
#[derive(Debug, Default, Clone, Eq, PartialEq, Store, Load)]
pub struct StorageUsed {
    /// Amount of unique cells.
    pub cells: VarUint56,
    /// The total number of bits in unique cells.
    pub bits: VarUint56,
    /// The number of public libraries in the state.
    pub public_cells: VarUint56,
}

impl StorageUsed {
    /// The additive identity for this type, i.e. `0`.
    pub const ZERO: Self = Self {
        cells: VarUint56::ZERO,
        bits: VarUint56::ZERO,
        public_cells: VarUint56::ZERO,
    };
}

/// Amount of unique cells and bits.
#[derive(Debug, Default, Clone, Copy, Eq, PartialEq, Store, Load)]
pub struct StorageUsedShort {
    /// Amount of unique cells.
    pub cells: VarUint56,
    /// The total number of bits in unique cells.
    pub bits: VarUint56,
}

impl StorageUsedShort {
    /// The additive identity for this type, i.e. `0`.
    pub const ZERO: Self = Self {
        cells: VarUint56::ZERO,
        bits: VarUint56::ZERO,
    };
}

/// Storage profile of an account.
#[derive(Debug, Default, Clone, Eq, PartialEq, Store, Load)]
pub struct StorageInfo {
    /// Amount of unique cells and bits which account state occupies.
    pub used: StorageUsed,
    /// Unix timestamp of the last storage phase.
    pub last_paid: u32,
    /// Account debt for storing its state.
    pub due_payment: Option<Tokens>,
}

/// Brief account status.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum AccountStatus {
    /// Account exists but has not yet been deployed.
    Uninit = 0b00,
    /// Account exists but has been frozen.
    Frozen = 0b01,
    /// Account exists and has been deployed.
    Active = 0b10,
    /// Account does not exist.
    NotExists = 0b11,
}

impl AccountStatus {
    /// The number of data bits that this struct occupies.
    pub const BITS: u16 = 2;
}

impl Store for AccountStatus {
    #[inline]
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn Finalizer) -> Result<(), Error> {
        builder.store_small_uint(*self as u8, 2)
    }
}

impl<'a> Load<'a> for AccountStatus {
    #[inline]
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        match slice.load_small_uint(2) {
            Ok(ty) => Ok(match ty {
                0b00 => Self::Uninit,
                0b01 => Self::Frozen,
                0b10 => Self::Active,
                0b11 => Self::NotExists,
                _ => {
                    debug_assert!(false, "unexpected small uint");
                    // SAFETY: `load_small_uint` must return 2 bits
                    unsafe { std::hint::unreachable_unchecked() }
                }
            }),
            Err(e) => Err(e),
        }
    }
}

/// Shard accounts entry.
#[derive(Debug, Clone, Eq, PartialEq, Store, Load)]
pub struct ShardAccount {
    /// Optional reference to account state.
    pub account: Lazy<OptionalAccount>,
    /// The exact hash of the last transaction.
    pub last_trans_hash: HashBytes,
    /// The exact logical time of the last transaction.
    pub last_trans_lt: u64,
}

impl ShardAccount {
    /// Tries to load account data.
    pub fn load_account(&self) -> Result<Option<Account>, Error> {
        let OptionalAccount(account) = ok!(self.account.load());
        Ok(account)
    }
}

/// A wrapper for `Option<Account>` with customized representation.
#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub struct OptionalAccount(pub Option<Account>);

impl OptionalAccount {
    /// Non-existing account.
    pub const EMPTY: Self = Self(None);
}

impl Store for OptionalAccount {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        match &self.0 {
            None => builder.store_bit_zero(),
            Some(account) => {
                let with_init_code_hash = account.init_code_hash.is_some();
                ok!(if with_init_code_hash {
                    builder.store_small_uint(0b0001, 4)
                } else {
                    builder.store_bit_one()
                });

                ok!(account.address.store_into(builder, finalizer));
                ok!(account.storage_stat.store_into(builder, finalizer));
                ok!(builder.store_u64(account.last_trans_lt));
                ok!(account.balance.store_into(builder, finalizer));
                ok!(account.state.store_into(builder, finalizer));
                if let Some(init_code_hash) = &account.init_code_hash {
                    ok!(builder.store_bit_one());
                    builder.store_u256(init_code_hash)
                } else {
                    Ok(())
                }
            }
        }
    }
}

impl<'a> Load<'a> for OptionalAccount {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let with_init_code_hash = if ok!(slice.load_bit()) {
            false // old version
        } else if slice.is_data_empty() {
            return Ok(Self::EMPTY);
        } else {
            let tag = ok!(slice.load_small_uint(3));
            match tag {
                0 => false, // old version
                1 => true,  // new version
                _ => return Err(Error::InvalidData),
            }
        };

        Ok(Self(Some(Account {
            address: ok!(IntAddr::load_from(slice)),
            storage_stat: ok!(StorageInfo::load_from(slice)),
            last_trans_lt: ok!(slice.load_u64()),
            balance: ok!(CurrencyCollection::load_from(slice)),
            state: ok!(AccountState::load_from(slice)),
            init_code_hash: if with_init_code_hash {
                ok!(Option::<HashBytes>::load_from(slice))
            } else {
                None
            },
        })))
    }
}

/// Existing account data.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Account {
    /// Account address.
    pub address: IntAddr,
    /// Storage statistics.
    pub storage_stat: StorageInfo,
    /// Logical time after the last transaction execution.
    pub last_trans_lt: u64,
    /// Account balance for all currencies.
    pub balance: CurrencyCollection,
    /// Account state.
    pub state: AccountState,
    /// Optional initial code hash.
    pub init_code_hash: Option<HashBytes>,
}

/// State of an existing account.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum AccountState {
    /// Account exists but has not yet been deployed.
    Uninit,
    /// Account exists and has been deployed.
    Active(StateInit),
    /// Account exists but has been frozen. Contains a hash of the last known [`StateInit`].
    Frozen(HashBytes),
}

impl Store for AccountState {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        match self {
            Self::Uninit => builder.store_small_uint(0b00, 2),
            Self::Active(state) => {
                ok!(builder.store_bit_one());
                state.store_into(builder, finalizer)
            }
            Self::Frozen(hash) => {
                ok!(builder.store_small_uint(0b01, 2));
                builder.store_u256(hash)
            }
        }
    }
}

impl<'a> Load<'a> for AccountState {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        Ok(if ok!(slice.load_bit()) {
            match StateInit::load_from(slice) {
                Ok(state) => Self::Active(state),
                Err(e) => return Err(e),
            }
        } else if ok!(slice.load_bit()) {
            match slice.load_u256() {
                Ok(state) => Self::Frozen(state),
                Err(e) => return Err(e),
            }
        } else {
            Self::Uninit
        })
    }
}

/// Deployed account state.
#[derive(Debug, Clone, Eq, PartialEq, Store, Load)]
pub struct StateInit {
    /// Optional split depth for large smart contracts.
    pub split_depth: Option<SplitDepth>,
    /// Optional special contract flags.
    pub special: Option<SpecialFlags>,
    /// Optional contract code.
    pub code: Option<Cell>,
    /// Optional contract data.
    pub data: Option<Cell>,
    /// Libraries used in smart-contract.
    pub libraries: Dict<HashBytes, SimpleLib>,
}

impl Default for StateInit {
    fn default() -> Self {
        Self {
            split_depth: None,
            special: None,
            code: None,
            data: None,
            libraries: Dict::new(),
        }
    }
}

impl StateInit {
    /// Returns the number of data bits that this struct occupies.
    pub const fn bit_len(&self) -> u16 {
        (1 + self.split_depth.is_some() as u16 * SplitDepth::BITS)
            + (1 + self.special.is_some() as u16 * SpecialFlags::BITS)
            + 3
    }

    /// Returns the number of references that this struct occupies.
    pub const fn reference_count(&self) -> u8 {
        self.code.is_some() as u8 + self.data.is_some() as u8 + !self.libraries.is_empty() as u8
    }
}

/// Special transactions execution flags.
#[derive(Debug, Default, Clone, Copy, Eq, PartialEq)]
pub struct SpecialFlags {
    /// Account will be called at the beginning of each block.
    pub tick: bool,
    /// Account will be called at the end of each block.
    pub tock: bool,
}

impl SpecialFlags {
    /// The number of data bits that this struct occupies.
    pub const BITS: u16 = 2;
}

impl Store for SpecialFlags {
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn Finalizer) -> Result<(), Error> {
        builder.store_small_uint(((self.tick as u8) << 1) | self.tock as u8, 2)
    }
}

impl<'a> Load<'a> for SpecialFlags {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        match slice.load_small_uint(2) {
            Ok(data) => Ok(Self {
                tick: data & 0b10 != 0,
                tock: data & 0b01 != 0,
            }),
            Err(e) => Err(e),
        }
    }
}

/// Simple TVM library.
#[derive(Debug, Clone, Eq, PartialEq, Store, Load)]
pub struct SimpleLib {
    /// Whether this library is accessible from other accounts.
    pub public: bool,
    /// Reference to the library cell.
    pub root: Cell,
}
