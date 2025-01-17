//! Currency collection stuff.

use crate::cell::*;
use crate::dict::{AugDictExtra, Dict};
use crate::error::Error;
use crate::num::{Tokens, VarUint248};

/// Amounts collection.
#[derive(Debug, Clone, Eq, PartialEq, Store, Load)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[must_use]
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
            other: ok!(self.other.checked_add(&other.other)),
        })
    }

    /// Checked currency collection subtraction.
    /// Computes `self - rhs` for each currency, returning `Err`
    /// if overflow occurred or dictionaries had invalid structure.
    pub fn checked_sub(&self, other: &Self) -> Result<Self, Error> {
        Ok(Self {
            tokens: match self.tokens.checked_sub(other.tokens) {
                Some(value) => value,
                None => return Err(Error::IntOverflow),
            },
            other: ok!(self.other.checked_sub(&other.other)),
        })
    }

    /// Tries to add the specified amount of native tokens to the collection.
    pub fn try_add_assign_tokens(&mut self, other: Tokens) -> Result<(), Error> {
        match self.tokens.checked_add(other) {
            Some(value) => {
                self.tokens = value;
                Ok(())
            }
            None => Err(Error::IntOverflow),
        }
    }

    /// Tries to subtract the specified amount of native tokens from the collection.
    pub fn try_sub_assign_tokens(&mut self, other: Tokens) -> Result<(), Error> {
        match self.tokens.checked_sub(other) {
            Some(value) => {
                self.tokens = value;
                Ok(())
            }
            None => Err(Error::IntOverflow),
        }
    }

    /// Tries to add an other currency collection to the current one.
    pub fn try_add_assign(&mut self, other: &Self) -> Result<(), Error> {
        *self = ok!(self.checked_add(other));
        Ok(())
    }

    /// Tries to subtract an other currency collection from the current one.
    pub fn try_sub_assign(&mut self, other: &Self) -> Result<(), Error> {
        *self = ok!(self.checked_sub(other));
        Ok(())
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

impl ExactSize for CurrencyCollection {
    #[inline]
    fn exact_size(&self) -> Size {
        self.tokens.exact_size() + self.other.exact_size()
    }
}

impl AugDictExtra for CurrencyCollection {
    fn comp_add(
        left: &mut CellSlice,
        right: &mut CellSlice,
        b: &mut CellBuilder,
        cx: &dyn CellContext,
    ) -> Result<(), Error> {
        let left = ok!(Self::load_from(left));
        let right = ok!(Self::load_from(right));
        ok!(left.checked_add(&right)).store_into(b, cx)
    }
}

/// Dictionary with amounts for multiple currencies.
#[derive(Debug, Clone, Eq, PartialEq, Store, Load)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[must_use]
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
                Some(ref value) => ok!(result.0.set(currency_id, value)),
                None => return Err(Error::IntOverflow),
            };
        }
        Ok(result)
    }

    /// Checked extra currency subtraction.
    /// Computes `self - rhs` for each currency, returning `Err`
    /// if overflow occurred or dictionaries had invalid structure.
    pub fn checked_sub(&self, other: &Self) -> Result<Self, Error> {
        let mut result = self.clone();
        for entry in other.0.iter() {
            let (currency_id, other) = ok!(entry);

            let existing = ok!(result.as_dict().get(currency_id)).unwrap_or_default();
            match existing.checked_sub(&other) {
                Some(ref value) => ok!(result.0.set(currency_id, value)),
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

impl ExactSize for ExtraCurrencyCollection {
    #[inline]
    fn exact_size(&self) -> Size {
        self.0.exact_size()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn _cc_must_use() -> anyhow::Result<()> {
        #[expect(unused_must_use)]
        {
            CurrencyCollection::new(10).checked_add(&CurrencyCollection::ZERO)?;
        }

        #[expect(unused_must_use)]
        {
            ExtraCurrencyCollection::new().checked_add(&ExtraCurrencyCollection::new())?;
        }

        Ok(())
    }
}
