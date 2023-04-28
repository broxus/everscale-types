//! Blockchain models.

use std::marker::PhantomData;

use crate::cell::{Cell, CellBuilder, CellSlice, DefaultFinalizer, Finalizer, Load, Store};
use crate::error::Error;
use crate::util::*;

pub use account::*;
pub use block::*;
pub use config::*;
pub use global_version::*;
pub use message::*;
pub use transaction::*;

pub mod account;
pub mod block;
pub mod config;
pub mod currency;
pub mod global_version;
pub mod message;
pub mod shard;
pub mod transaction;

#[cfg(feature = "sync")]
#[doc(hidden)]
mod __checks {
    use super::*;

    assert_impl_all!(Lazy<Message>: Send);
    assert_impl_all!(Account: Send);
    assert_impl_all!(Block: Send);
    assert_impl_all!(Message: Send);
    assert_impl_all!(Transaction: Send);
}

/// Lazy-loaded model.
pub struct Lazy<T> {
    cell: Cell,
    _marker: PhantomData<T>,
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

impl<T> Clone for Lazy<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            cell: self.cell.clone(),
            _marker: PhantomData,
        }
    }
}

impl<T> Lazy<T> {
    /// Wraps the cell in a typed wrapper.
    #[inline]
    pub fn from_raw(cell: Cell) -> Self {
        Self {
            cell,
            _marker: PhantomData,
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
}

impl<T: Store> Lazy<T> {
    /// Serializes the provided data and returns the typed wrapper around it.
    pub fn new(data: &T) -> Result<Self, Error> {
        let mut builder = CellBuilder::new();
        let finalizer = &mut Cell::default_finalizer();
        ok!(data.store_into(&mut builder, finalizer));
        Ok(Self::from_raw(ok!(builder.build_ext(finalizer))))
    }
}

impl<'a, T: Load<'a> + 'a> Lazy<T> {
    /// Loads inner data from cell.
    pub fn load(&'a self) -> Result<T, Error> {
        self.cell.as_ref().parse::<T>()
    }
}

impl<T> Store for Lazy<T> {
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn Finalizer) -> Result<(), Error> {
        builder.store_reference(self.cell.clone())
    }
}

impl<'a, T> Load<'a> for Lazy<T> {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        match slice.load_reference_cloned() {
            Ok(cell) => Ok(Self {
                cell,
                _marker: PhantomData,
            }),
            Err(e) => Err(e),
        }
    }
}
