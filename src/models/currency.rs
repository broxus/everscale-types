//! Currency collection stuff.

use everscale_types_proc::*;

use crate::cell::*;
use crate::dict::Dict;
use crate::num::{Tokens, VarUint248};

/// Amounts collection.
#[derive(CustomDebug, CustomClone, CustomEq, Store, Load)]
pub struct CurrencyCollection<C: CellFamily> {
    /// Amount in native currency.
    pub tokens: Tokens,
    /// Amounts in other currencies.
    pub other: ExtraCurrencyCollection<C>,
}

impl<C: CellFamily> Default for CurrencyCollection<C> {
    #[inline]
    fn default() -> Self {
        Self::ZERO
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

/// Dictionary with amounts for multiple currencies.
#[derive(CustomDebug, CustomClone, CustomEq, Store, Load)]
#[repr(transparent)]
pub struct ExtraCurrencyCollection<C: CellFamily>(Dict<C, CellHash, VarUint248>);

impl<C: CellFamily> Default for ExtraCurrencyCollection<C> {
    #[inline]
    fn default() -> Self {
        Self(Dict::new())
    }
}

impl<C: CellFamily> ExtraCurrencyCollection<C> {
    /// Creates an empty extra currency collection.
    pub const fn new() -> Self {
        Self(Dict::new())
    }

    /// Returns `true` if the dictionary contains no elements.
    pub const fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the underlying dictionary.
    pub const fn as_dict(&self) -> &Dict<C, CellHash, VarUint248> {
        &self.0
    }
}