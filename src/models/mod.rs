//! Blockchain models.

use std::marker::PhantomData;

use crate::cell::{
    CellBuilder, CellContainer, CellFamily, CellSlice, DefaultFinalizer, Finalizer, Load, Store,
};

pub use account::*;
pub use message::*;
pub use transaction::*;

pub mod account;
pub mod message;
pub mod transaction;

/// Lazy-loaded model.
pub struct Lazy<C: CellFamily, T> {
    cell: CellContainer<C>,
    _marker: PhantomData<T>,
}

impl<C: CellFamily, T> std::fmt::Debug for Lazy<C, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Lazy").field(&self.cell).finish()
    }
}

impl<C: CellFamily, T> Eq for Lazy<C, T> {}
impl<C: CellFamily, T> PartialEq for Lazy<C, T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.cell.as_ref().eq(other.cell.as_ref())
    }
}

impl<C: CellFamily, T> Clone for Lazy<C, T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            cell: self.cell.clone(),
            _marker: PhantomData,
        }
    }
}

impl<C: CellFamily, T> Lazy<C, T> {
    /// Wraps the cell in a typed wrapper.
    #[inline]
    pub fn from_raw(cell: CellContainer<C>) -> Self {
        Self {
            cell,
            _marker: PhantomData,
        }
    }

    /// Converts into the underlying cell.
    #[inline]
    pub fn into_inner(self) -> CellContainer<C> {
        self.cell
    }

    /// Returns the underlying cell.
    #[inline]
    pub fn inner(&self) -> &CellContainer<C> {
        &self.cell
    }
}

impl<C: DefaultFinalizer, T: Store<C>> Lazy<C, T> {
    /// Serializes the provided data and returns the typed wrapper around it.
    pub fn new(data: &T) -> Option<Self> {
        let mut builder = CellBuilder::<C>::new();
        let finalizer = &mut C::default_finalizer();
        if !data.store_into(&mut builder, finalizer) {
            return None;
        }
        Some(Self::from_raw(builder.build_ext(finalizer)?))
    }
}

impl<'a, C: CellFamily, T: Load<'a, C> + 'a> Lazy<C, T> {
    /// Loads inner data from cell.
    pub fn load(&'a self) -> Option<T> {
        T::load_from(&mut self.cell.as_ref().as_slice())
    }
}

impl<C: CellFamily, T> Store<C> for Lazy<C, T> {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        builder.store_reference(self.cell.clone())
    }
}

impl<'a, C: CellFamily, T> Load<'a, C> for Lazy<C, T> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            cell: slice.load_reference_cloned()?,
            _marker: PhantomData,
        })
    }
}
