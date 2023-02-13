//! Account state models.

use everscale_types_proc::{CustomClone, CustomDebug};

use crate::cell::*;
use crate::dict::*;
use crate::num::*;

use crate::models::currency::CurrencyCollection;

/// Amount of unique cells and bits for shard states.
#[derive(Debug, Default, Clone, Eq, PartialEq)]
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

impl<C: CellFamily> Store<C> for StorageUsed {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.cells.store_into(builder, finalizer)
            && self.bits.store_into(builder, finalizer)
            && self.public_cells.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for StorageUsed {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            cells: VarUint56::load_from(slice)?,
            bits: VarUint56::load_from(slice)?,
            public_cells: VarUint56::load_from(slice)?,
        })
    }
}

/// Amount of unique cells and bits.
#[derive(Debug, Default, Clone, Copy, Eq, PartialEq)]
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

impl<C: CellFamily> Store<C> for StorageUsedShort {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.cells.store_into(builder, finalizer) && self.bits.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for StorageUsedShort {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            cells: VarUint56::load_from(slice)?,
            bits: VarUint56::load_from(slice)?,
        })
    }
}

/// Storage profile of an account.
#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct StorageInfo {
    /// Amount of unique cells and bits which account state occupies.
    pub used: StorageUsed,
    /// Unix timestamp of the last storage phase.
    pub last_paid: u32,
    /// Account debt for storing its state.
    pub due_payment: Option<Tokens>,
}

impl<C: CellFamily> Store<C> for StorageInfo {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.used.store_into(builder, finalizer)
            && builder.store_u32(self.last_paid)
            && self.due_payment.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for StorageInfo {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            used: StorageUsed::load_from(slice)?,
            last_paid: slice.load_u32()?,
            due_payment: Option::<Tokens>::load_from(slice)?,
        })
    }
}

/// Brief account status.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
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

impl<C: CellFamily> Store<C> for AccountStatus {
    #[inline]
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        builder.store_small_uint(*self as u8, 2)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for AccountStatus {
    #[inline]
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let ty = slice.load_small_uint(2)?;
        Some(match ty {
            0b00 => Self::Uninit,
            0b01 => Self::Frozen,
            0b10 => Self::Active,
            0b11 => Self::NotExists,
            _ => return None,
        })
    }
}

#[derive(CustomDebug, CustomClone)]
pub struct AccountStorage<C: CellFamily> {
    /// Logical time after the last transaction execution.
    pub last_trans_lt: u64,
    /// Account balance for all currencies.
    pub balance: CurrencyCollection<C>,
}

#[derive(CustomDebug, CustomClone)]
pub enum AccountState<C: CellFamily> {
    Uninit,
    Active(StateInit<C>),
    Frozen(CellHash),
}

impl<C: CellFamily> Store<C> for AccountState<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        match self {
            Self::Uninit => builder.store_small_uint(0b00, 2),
            Self::Active(state) => builder.store_bit_one() && state.store_into(builder, finalizer),
            Self::Frozen(hash) => builder.store_small_uint(0b01, 2) && builder.store_u256(hash),
        }
    }
}

impl<'a, C: CellFamily> Load<'a, C> for AccountState<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(if slice.load_bit()? {
            Self::Active(StateInit::<C>::load_from(slice)?)
        } else if slice.load_bit()? {
            Self::Frozen(slice.load_u256()?)
        } else {
            Self::Uninit
        })
    }
}

/// Deployed account state.
#[derive(CustomDebug, CustomClone)]
pub struct StateInit<C: CellFamily> {
    /// Optional split depth for large smart contracts.
    pub split_depth: Option<SplitDepth>,
    /// Optional special contract flags.
    pub special: Option<SpecialFlags>,
    /// Optional contract code.
    pub code: Option<CellContainer<C>>,
    /// Optional contract data.
    pub data: Option<CellContainer<C>>,
    /// Libraries used in smart-contract.
    pub libraries: Dict<C, CellHash, SimpleLib<C>>,
}

impl<C: CellFamily> Default for StateInit<C> {
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

impl<C: CellFamily> Eq for StateInit<C> {}
impl<C: CellFamily> PartialEq for StateInit<C> {
    #[inline]
    fn eq(&self, other: &StateInit<C>) -> bool {
        self.split_depth == other.split_depth
            && self.special == other.special
            && self.code == other.code
            && self.data == other.data
            && self.libraries == other.libraries
    }
}

impl<C: CellFamily> StateInit<C> {
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

impl<C: CellFamily> Store<C> for StateInit<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.split_depth.store_into(builder, finalizer)
            && self.special.store_into(builder, finalizer)
            && self.code.store_into(builder, finalizer)
            && self.data.store_into(builder, finalizer)
            && self.libraries.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for StateInit<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            split_depth: Option::<SplitDepth>::load_from(slice)?,
            special: Option::<SpecialFlags>::load_from(slice)?,
            code: Option::<CellContainer<C>>::load_from(slice)?,
            data: Option::<CellContainer<C>>::load_from(slice)?,
            libraries: Dict::load_from(slice)?,
        })
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

impl<C: CellFamily> Store<C> for SpecialFlags {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        builder.store_small_uint(((self.tick as u8) << 1) | self.tock as u8, 2)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for SpecialFlags {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let data = slice.load_small_uint(2)?;
        Some(Self {
            tick: data & 0b10 != 0,
            tock: data & 0b01 != 0,
        })
    }
}

/// Simple TVM library.
#[derive(CustomDebug, CustomClone)]
pub struct SimpleLib<C: CellFamily> {
    /// Whether this library is accessible from other accounts.
    pub public: bool,
    /// Reference to the library cell.
    pub root: CellContainer<C>,
}

impl<C: CellFamily> Store<C> for SimpleLib<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        builder.store_bit(self.public) && builder.store_reference(self.root.clone())
    }
}

impl<'a, C: CellFamily> Load<'a, C> for SimpleLib<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            public: slice.load_bit()?,
            root: slice.load_reference_cloned()?,
        })
    }
}
