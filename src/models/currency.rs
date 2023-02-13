//! Currency collection stuff.

use crate::cell::*;
use crate::dict::Dict;
use crate::num::{Tokens, VarUint248};
use crate::util::*;

/// Amounts collection.
pub struct CurrencyCollection<C: CellFamily> {
    /// Amount in native currency.
    pub tokens: Tokens,
    /// Amounts in other currencies.
    pub other: ExtraCurrencyCollection<C>,
}

impl<C: CellFamily> std::fmt::Debug for CurrencyCollection<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        debug_struct_field2_finish(
            f,
            "CurrencyCollection",
            "tokens",
            &self.tokens,
            "other",
            &self.other,
        )
    }
}

impl<C: CellFamily> Default for CurrencyCollection<C> {
    #[inline]
    fn default() -> Self {
        Self::ZERO
    }
}

impl<C: CellFamily> Clone for CurrencyCollection<C> {
    fn clone(&self) -> Self {
        Self {
            tokens: self.tokens,
            other: self.other.clone(),
        }
    }
}

impl<C: CellFamily> Eq for CurrencyCollection<C> {}
impl<C: CellFamily> PartialEq for CurrencyCollection<C> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.tokens == other.tokens && self.other == other.other
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
#[repr(transparent)]
pub struct ExtraCurrencyCollection<C: CellFamily>(Dict<C, CellHash, VarUint248>);

impl<C: CellFamily> std::fmt::Debug for ExtraCurrencyCollection<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        debug_tuple_field1_finish(f, "ExtraCurrencyCollection", &self.0)
    }
}

impl<C: CellFamily> Default for ExtraCurrencyCollection<C> {
    #[inline]
    fn default() -> Self {
        Self(Dict::new())
    }
}

impl<C: CellFamily> Clone for ExtraCurrencyCollection<C> {
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<C: CellFamily> Eq for ExtraCurrencyCollection<C> {}
impl<C: CellFamily> PartialEq for ExtraCurrencyCollection<C> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
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
