//! Account state models.

use crate::cell::*;
use crate::dict::*;
use crate::num::*;

/// Amount of unique cells and bits.
#[derive(Debug, Default, Clone, Copy, Eq, PartialEq)]
pub struct StorageUsedShort {
    /// Amount of unique cells.
    pub cells: VarUint56,
    /// The total number of bits in unique cells.
    pub bits: VarUint56,
}

impl StorageUsedShort {
    /// The additive identity for this integer type, i.e. `0`.
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

/// Deployed account state.
#[derive(Debug, Default, Clone, Eq, PartialEq)]
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
    pub libraries: RawDict<C, 256>,
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
            libraries: RawDict::<C, 256>::load_from(slice)?,
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

/// Amounts collection.
#[derive(Default, Clone, Eq, PartialEq)]
pub struct CurrencyCollection<C: CellFamily> {
    /// Amount in native currency.
    pub tokens: Tokens,
    /// Amounts in other currencies.
    pub other: ExtraCurrencyCollection<C>,
}

impl<C: CellFamily> std::fmt::Debug for CurrencyCollection<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CurrencyCollection")
            .field("tokens", &self.tokens)
            .field("other", &self.other)
            .finish()
    }
}

impl<C: CellFamily> CurrencyCollection<C> {
    /// The additive identity for the currency collection
    /// (with empty extra currencies).
    pub const ZERO: Self = Self {
        tokens: Tokens::ZERO,
        other: ExtraCurrencyCollection::new(),
    };

    /// Creates a new currency collection with from the specified tokens amount
    /// and empty extra currency collection.
    pub const fn new(tokens: u128) -> Self {
        Self {
            tokens: Tokens::new(tokens),
            other: ExtraCurrencyCollection::new(),
        }
    }

    /// Returns the number of data bits that this struct occupies.
    pub const fn bit_len(&self) -> u16 {
        self.tokens.unwrap_bit_len() + 1
    }
}

impl<C: CellFamily> Store<C> for CurrencyCollection<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.tokens.store_into(builder, finalizer) && self.other.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for CurrencyCollection<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            tokens: Tokens::load_from(slice)?,
            other: ExtraCurrencyCollection::<C>::load_from(slice)?,
        })
    }
}

/// Dictionary with amounts for multiple currencies.
#[derive(Default, Clone, Eq, PartialEq)]
#[repr(transparent)]
pub struct ExtraCurrencyCollection<C: CellFamily>(RawDict<C, 32>);

impl<C: CellFamily> std::fmt::Debug for ExtraCurrencyCollection<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("ExtraCurrencyCollection")
            .field(&self.0)
            .finish()
    }
}

impl<C: CellFamily> ExtraCurrencyCollection<C> {
    /// Creates an empty extra currency collection.
    pub const fn new() -> Self {
        Self(RawDict::new())
    }

    /// Returns `true` if the dictionary contains no elements.
    pub const fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<C: CellFamily> Store<C> for ExtraCurrencyCollection<C> {
    #[inline]
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.0.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ExtraCurrencyCollection<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self(RawDict::load_from(slice)?))
    }
}
