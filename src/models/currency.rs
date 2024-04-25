//! Currency collection stuff.

use crate::cell::*;
use crate::dict::{AugDictSkipValue, Dict};
use crate::error::Error;
use crate::num::{Tokens, VarUint248};

/// Amounts collection.
#[derive(Debug, Clone, Eq, PartialEq, Store, Load)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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

    /// Checked currency collection addition.
    /// Computes `self + rhs` for each currency, returning `Err`
    /// if overflow occurred or dictionaries had invalid structure.
    pub fn checked_add(&self, other: &Self) -> Result<Self, Error> {
        Ok(Self {
            tokens: match self.tokens.checked_add(other.tokens) {
                Some(value) => value,
                None => return Err(Error::IntOverflow),
            },
            other: self.other.checked_add(&other.other)?,
        })
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
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(transparent)]
pub struct ExtraCurrencyCollection(Dict<u32, VarUint248>);

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
    pub const fn as_dict(&self) -> &Dict<u32, VarUint248> {
        &self.0
    }

    /// Returns a mutable reference to the underlying dictionary.
    pub fn as_dict_mut(&mut self) -> &mut Dict<u32, VarUint248> {
        &mut self.0
    }

    /// Checked extra currency collection addition.
    /// Computes `self + rhs` for each currency, returning `Err`
    /// if overflow occurred or dictionaries had invalid structure.
    pub fn checked_add(&self, other: &Self) -> Result<Self, Error> {
        let mut result = self.clone();
        for entry in other.0.iter() {
            let (currency_id, other) = ok!(entry);

            let existing = ok!(result.as_dict().get(currency_id)).unwrap_or_default();
            match existing.checked_add(&other) {
                Some(value) => ok!(result.0.set(currency_id, &value)),
                None => return Err(Error::IntOverflow),
            };
        }
        Ok(result)
    }
}

impl From<Dict<u32, VarUint248>> for ExtraCurrencyCollection {
    #[inline]
    fn from(value: Dict<u32, VarUint248>) -> Self {
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
