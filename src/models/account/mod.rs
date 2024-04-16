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

    /// Computes a total storage usage stats.
    ///
    /// `cell_limit` is the maximum number of unique cells to visit.
    /// If the limit is reached, the function will return [`Error::Cancelled`].
    pub fn compute(account: &Account, cell_limit: usize) -> Result<Self, Error> {
        let cell = {
            let cx = &mut Cell::empty_context();
            let mut storage = CellBuilder::new();
            storage.store_u64(account.last_trans_lt)?;
            account.balance.store_into(&mut storage, cx)?;
            account.state.store_into(&mut storage, cx)?;
            if account.init_code_hash.is_some() {
                account.init_code_hash.store_into(&mut storage, cx)?;
            }
            storage.build_ext(cx)?
        };

        let Some(res) = cell.compute_unique_stats(cell_limit) else {
            return Err(Error::Cancelled);
        };

        let res = Self {
            cells: VarUint56::new(res.cell_count),
            bits: VarUint56::new(res.bit_count),
            public_cells: Default::default(),
        };

        if res.cells.is_valid() || !res.bits.is_valid() {
            return Err(Error::IntOverflow);
        }

        Ok(res)
    }
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
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn CellContext) -> Result<(), Error> {
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

    /// Returns an optional account status.
    pub fn status(&self) -> AccountStatus {
        match &self.0 {
            None => AccountStatus::NotExists,
            Some(account) => account.state.status(),
        }
    }

    /// Logical time after the last transaction execution if account exists
    /// or zero otherwise.
    pub fn last_trans_lt(&self) -> u64 {
        match &self.0 {
            None => 0,
            Some(account) => account.last_trans_lt,
        }
    }

    /// Account balance for all currencies.
    #[cfg(feature = "sync")]
    pub fn balance(&self) -> &CurrencyCollection {
        static DEFAULT_VALANCE: CurrencyCollection = CurrencyCollection::ZERO;

        match &self.0 {
            None => &DEFAULT_VALANCE,
            Some(account) => &account.balance,
        }
    }

    /// Returns an account state if it exists.
    pub fn state(&self) -> Option<&AccountState> {
        Some(&self.0.as_ref()?.state)
    }
}

impl AsRef<Option<Account>> for OptionalAccount {
    #[inline]
    fn as_ref(&self) -> &Option<Account> {
        &self.0
    }
}

impl AsMut<Option<Account>> for OptionalAccount {
    #[inline]
    fn as_mut(&mut self) -> &mut Option<Account> {
        &mut self.0
    }
}

impl Store for OptionalAccount {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
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

                ok!(account.address.store_into(builder, context));
                ok!(account.storage_stat.store_into(builder, context));
                ok!(builder.store_u64(account.last_trans_lt));
                ok!(account.balance.store_into(builder, context));
                ok!(account.state.store_into(builder, context));
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

impl AccountState {
    /// Returns an account status.
    pub fn status(&self) -> AccountStatus {
        match self {
            Self::Uninit => AccountStatus::Uninit,
            Self::Active(_) => AccountStatus::Active,
            Self::Frozen(_) => AccountStatus::Frozen,
        }
    }
}

impl Store for AccountState {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        match self {
            Self::Uninit => builder.store_small_uint(0b00, 2),
            Self::Active(state) => {
                ok!(builder.store_bit_one());
                state.store_into(builder, context)
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
    /// Exact size of this value when it is stored in slice.
    pub const fn exact_size_const(&self) -> CellSliceSize {
        CellSliceSize {
            bits: self.bit_len(),
            refs: self.reference_count(),
        }
    }

    /// Returns the number of data bits that this struct occupies.
    const fn bit_len(&self) -> u16 {
        (1 + self.split_depth.is_some() as u16 * SplitDepth::BITS)
            + (1 + self.special.is_some() as u16 * SpecialFlags::BITS)
            + 3
    }

    /// Returns the number of references that this struct occupies.
    const fn reference_count(&self) -> u8 {
        self.code.is_some() as u8 + self.data.is_some() as u8 + !self.libraries.is_empty() as u8
    }
}

impl ExactSize for StateInit {
    #[inline]
    fn exact_size(&self) -> CellSliceSize {
        self.exact_size_const()
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
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn CellContext) -> Result<(), Error> {
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
    /// Library code.
    pub root: Cell,
}
