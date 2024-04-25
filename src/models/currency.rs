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

/// AddSub trait
pub trait AddSub {
    /// sub
    fn sub(&mut self, other: &Self) -> Result<bool, Error>;
    /// add
    fn add(&mut self, other: &Self) -> Result<bool, Error>;
}

impl AddSub for CurrencyCollection {
    fn sub(&mut self, other: &Self) -> Result<bool, Error> {
        let option = self.tokens.checked_sub(other.tokens);
        match option {
            Some(t) => self.tokens = t,
            None => return Ok(false),
        }
        for other_value in other.other.as_dict().iter() {
            let (hash, other_value) = other_value?;
            if let Some(self_value) = self.other.0.get(hash)? {
                if self_value >= other_value {
                    let (_, self_lo) = self_value.into_words();
                    let (_, other_lo) = other_value.into_words();
                    let new_value = match self_lo.checked_sub(other_lo) {
                        None => return Ok(false),
                        Some(new_value) => new_value,
                    };
                    let new_value = VarUint248::new(new_value);
                    self.other.0.set(hash, new_value)?;
                } else {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }
    fn add(&mut self, other: &Self) -> Result<bool, Error> {
        let option = self.tokens.checked_add(other.tokens);
        match option {
            Some(t) => self.tokens = t,
            None => return Ok(false),
        }
        for other_value in other.other.as_dict().iter() {
            let (hash, other_value) = other_value?;
            if let Some(self_value) = self.other.0.get(hash)? {
                let (_, self_lo) = self_value.into_words();
                let (_, other_lo) = other_value.into_words();
                let new_value = match self_lo.checked_add(other_lo) {
                    None => return Ok(false),
                    Some(new_value) => new_value,
                };
                let new_value = VarUint248::new(new_value);
                self.other.0.set(hash, new_value)?;
            }
        }
        Ok(true)
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
