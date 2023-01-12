//! Account state models.

use crate::cell::*;
use crate::dict::*;
use crate::num::*;

/// Deployed account state.
#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct StateInit<C: CellFamily> {
    /// Optional split depth for large smart contracts.
    pub split_depth: Option<SplitDepth>,
    /// Optional special contract flags.
    pub special: Option<TickTock>,
    /// Optional contract code.
    pub code: Option<CellContainer<C>>,
    /// Optional contract data.
    pub data: Option<CellContainer<C>>,
    /// Libraries used in smart-contract.
    pub libraries: Dict<C, 256>,
}

impl<C: CellFamily> StateInit<C> {
    /// Returns the number of data bits that this struct occupies.
    pub const fn bit_len(&self) -> u16 {
        (1 + self.split_depth.is_some() as u16 * SplitDepth::BITS)
            + (1 + self.special.is_some() as u16 * TickTock::BITS)
            + 3
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
            special: Option::<TickTock>::load_from(slice)?,
            code: Option::<CellContainer<C>>::load_from(slice)?,
            data: Option::<CellContainer<C>>::load_from(slice)?,
            libraries: Dict::<C, 256>::load_from(slice)?,
        })
    }
}

/// Tick-tock transactions execution flags.
#[derive(Debug, Default, Clone, Copy, Eq, PartialEq)]
pub struct TickTock {
    /// Account will be called at the beginning of each block.
    pub tick: bool,
    /// Account will be called at the end of each block.
    pub tock: bool,
}

impl TickTock {
    /// The number of data bits that this struct occupies.
    pub const BITS: u16 = 2;
}

impl<C: CellFamily> Store<C> for TickTock {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        builder.store_small_uint(((self.tick as u8) << 1) | self.tock as u8, 2)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for TickTock {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let data = slice.load_small_uint(2)?;
        Some(Self {
            tick: data & 0b10 != 0,
            tock: data & 0b01 != 0,
        })
    }
}

/// Amounts collection.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct CurrencyCollection<C: CellFamily> {
    /// Amount in native currency.
    pub tokens: Tokens,
    /// Amounts in other currencies.
    pub other: ExtraCurrencyCollection<C>,
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
#[derive(Debug, Default, Clone, Eq, PartialEq)]
#[repr(transparent)]
pub struct ExtraCurrencyCollection<C: CellFamily>(Dict<C, 32>);

impl<C: CellFamily> Store<C> for ExtraCurrencyCollection<C> {
    #[inline]
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.0.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ExtraCurrencyCollection<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self(Dict::load_from(slice)?))
    }
}
