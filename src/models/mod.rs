//! Blockchain models.

use crate::cell::{
    Cell, CellBuilder, CellContext, CellSlice, DynCell, EquivalentRepr, Load, Size, Store,
};
use crate::error::Error;
use crate::util::*;
use std::sync::OnceLock;

pub use account::*;
pub use block::*;
pub use config::*;
pub use currency::*;
pub use global_version::*;
pub use message::*;
pub use shard::*;
pub use transaction::*;
pub use vm::*;

pub mod account;
pub mod block;
pub mod config;
pub mod currency;
pub mod global_version;
pub mod message;
pub mod shard;
pub mod transaction;
pub mod vm;

#[cfg(feature = "sync")]
#[doc(hidden)]
mod __checks {
    use super::*;

    assert_impl_all!(Lazy<Message>: Send, Sync);
    assert_impl_all!(Account: Send, Sync);
    assert_impl_all!(Block: Send, Sync);
    assert_impl_all!(Message: Send, Sync);
    assert_impl_all!(Transaction: Send, Sync);
}

/// Lazy-loaded model.
pub struct Lazy<T> {
    cell: Cell,
    cache: OnceLock<Result<T, Error>>,
}

impl<T> crate::cell::ExactSize for Lazy<T> {
    #[inline]
    fn exact_size(&self) -> Size {
        Size { bits: 0, refs: 1 }
    }
}

impl<T> std::fmt::Debug for Lazy<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        debug_tuple_field1_finish(f, "Lazy", &self.cell)
    }
}

impl<T> Eq for Lazy<T> {}
impl<T> PartialEq for Lazy<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.cell.as_ref().eq(other.cell.as_ref())
    }
}

impl<T> Clone for Lazy<T>
where
    T: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            cell: self.cell.clone(),
            cache: self.cache.clone(),
        }
    }
}

impl<T> Lazy<T> {
    /// Wraps the cell in a typed wrapper.
    #[inline]
    pub fn from_raw(cell: Cell) -> Self {
        Self {
            cell,
            cache: OnceLock::new(),
        }
    }

    /// Converts into the underlying cell.
    #[inline]
    pub fn into_inner(self) -> Cell {
        self.cell
    }

    /// Returns the underlying cell.
    #[inline]
    pub fn inner(&self) -> &Cell {
        &self.cell
    }

    /// Converts into a lazy loader for an equivalent type.
    pub fn cast_into<Q>(self) -> Lazy<Q>
    where
        Q: EquivalentRepr<T>,
    {
        Lazy {
            cell: self.cell,
            cache: OnceLock::new(),
        }
    }

    /// Casts itself into a lazy loaded for an equivalent type.
    pub fn cast_ref<Q>(&self) -> &Lazy<Q>
    where
        Q: EquivalentRepr<T>,
    {
        // SAFETY: Lazy is #[repr(transparent)]
        unsafe { &*(self as *const Self as *const Lazy<Q>) }
    }

    /// Serializes only the root hash of the cell.
    #[cfg(feature = "serde")]
    pub fn serialize_repr_hash<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serde::Serialize::serialize(self.cell.repr_hash(), serializer)
    }
}

impl<T> AsRef<DynCell> for Lazy<T> {
    #[inline]
    fn as_ref(&self) -> &DynCell {
        self.cell.as_ref()
    }
}

impl<T: Store> Lazy<T> {
    /// Serializes the provided data and returns the typed wrapper around it.
    pub fn new(data: &T) -> Result<Self, Error> {
        Ok(Self::from_raw(ok!(CellBuilder::build_from(data))))
    }

    /// Updates the content with the provided data.
    pub fn set(&mut self, data: &T) -> Result<(), Error> {
        self.cell = ok!(CellBuilder::build_from(data));
        Ok(())
    }
}

impl<'a, T: Load<'a> + 'a> Lazy<T> {
    /// Loads inner data from cell.
    pub fn load(&'a self) -> Result<T, Error> {
        self.cell.as_ref().parse::<T>()
    }

    /// Parses `T` from the cell or returns the cached result if this method was called before.
    pub fn load_cached(&'a self) -> &Result<T, Error> {
        self.cache.get_or_init(|| self.cell.as_ref().parse::<T>())
    }
}

impl<T> Store for Lazy<T> {
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn CellContext) -> Result<(), Error> {
        builder.store_reference(self.cell.clone())
    }
}

impl<'a, T> Load<'a> for Lazy<T> {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        match slice.load_reference_cloned() {
            Ok(cell) => Ok(Self {
                cell,
                cache: OnceLock::new(),
            }),
            Err(e) => Err(e),
        }
    }
}

#[cfg(feature = "serde")]
impl<T> serde::Serialize for Lazy<T>
where
    for<'a> T: serde::Serialize + Load<'a>,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        if serializer.is_human_readable() {
            let value = match self
                .load_cached()
                .as_ref()
                .map_err(serde::ser::Error::custom)
            {
                Ok(value) => value,
                Err(e) => return Err(e),
            };
            value.serialize(serializer)
        } else {
            crate::boc::Boc::serialize(&self.cell, serializer)
        }
    }
}

#[cfg(feature = "serde")]
impl<'de, T> serde::Deserialize<'de> for Lazy<T>
where
    T: serde::Deserialize<'de> + Store,
{
    fn deserialize<D>(deserializer: D) -> Result<Lazy<T>, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        if deserializer.is_human_readable() {
            let value = T::deserialize(deserializer)?;
            Lazy::new(&value).map_err(serde::de::Error::custom)
        } else {
            crate::boc::Boc::deserialize(deserializer).map(Lazy::from_raw)
        }
    }
}
