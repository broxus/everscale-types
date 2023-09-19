//! Currency collection stuff.

use crate::cell::*;
use crate::dict::{AugDictSkipValue, Dict};
use crate::num::{Tokens, VarUint248};

/// Amounts collection.
#[derive(Debug, Clone, Eq, PartialEq, Store, Load)]
pub struct CurrencyCollection {
    /// Amount in native currency.
    pub tokens: Tokens,
    /// Amounts in other currencies.
    pub other: ExtraCurrencyCollection,
}

impl Default for CurrencyCollection {
    #[inline]
    fn default() -> Self {
        Self::ZERO
    }
}

impl CurrencyCollection {
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

impl From<Tokens> for CurrencyCollection {
    #[inline]
    fn from(tokens: Tokens) -> Self {
        Self {
            tokens,
            other: ExtraCurrencyCollection::new(),
        }
    }
}

impl<'a> AugDictSkipValue<'a> for CurrencyCollection {
    #[inline]
    fn skip_value(slice: &mut CellSlice<'a>) -> bool {
        Tokens::skip_value(slice) && ExtraCurrencyCollection::skip_value(slice)
    }
}

impl ExactSize for CurrencyCollection {
    #[inline]
    fn exact_size(&self) -> CellSliceSize {
        self.tokens.exact_size() + self.other.exact_size()
    }
}

/// Dictionary with amounts for multiple currencies.
#[derive(Debug, Clone, Eq, PartialEq, Store, Load)]
#[repr(transparent)]
pub struct ExtraCurrencyCollection(Dict<HashBytes, VarUint248>);

impl Default for ExtraCurrencyCollection {
    #[inline]
    fn default() -> Self {
        Self(Dict::new())
    }
}

impl ExtraCurrencyCollection {
    /// Creates an empty extra currency collection.
    pub const fn new() -> Self {
        Self(Dict::new())
    }

    /// Creates a currency collection from a raw cell.
    pub const fn from_raw(dict: Option<Cell>) -> Self {
        Self(Dict::from_raw(dict))
    }

    /// Returns `true` if the dictionary contains no elements.
    pub const fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns a reference to the underlying dictionary.
    pub const fn as_dict(&self) -> &Dict<HashBytes, VarUint248> {
        &self.0
    }

    /// Returns a mutable reference to the underlying dictionary.
    pub fn as_dict_mut(&mut self) -> &mut Dict<HashBytes, VarUint248> {
        &mut self.0
    }
}

impl From<Dict<HashBytes, VarUint248>> for ExtraCurrencyCollection {
    #[inline]
    fn from(value: Dict<HashBytes, VarUint248>) -> Self {
        Self(value)
    }
}

impl<'a> AugDictSkipValue<'a> for ExtraCurrencyCollection {
    #[inline]
    fn skip_value(slice: &mut CellSlice<'a>) -> bool {
        if let Ok(has_extra) = slice.load_bit() {
            !has_extra || slice.try_advance(0, 1)
        } else {
            false
        }
    }
}

impl ExactSize for ExtraCurrencyCollection {
    #[inline]
    fn exact_size(&self) -> CellSliceSize {
        self.0.exact_size()
    }
}
