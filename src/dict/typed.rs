use std::borrow::Borrow;
use std::marker::PhantomData;

use crate::cell::*;
use crate::dict::dict_remove_owned;
use crate::error::Error;
use crate::util::*;

use super::{
    dict_find_bound, dict_find_owned, dict_get, dict_insert, dict_load_from_root, DictBound,
    DictKey, SetMode,
};
use super::{dict_remove_bound_owned, raw::*};

/// Typed dictionary with fixed length keys.
#[repr(transparent)]
pub struct Dict<K, V> {
    pub(crate) root: Option<Cell>,
    _key: PhantomData<K>,
    _value: PhantomData<V>,
}

impl<K, V> ExactSize for Dict<K, V> {
    #[inline]
    fn exact_size(&self) -> CellSliceSize {
        CellSliceSize {
            bits: 1,
            refs: self.root.is_some() as u8,
        }
    }
}

impl<'a, K, V> Load<'a> for Dict<K, V> {
    #[inline]
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        Ok(Self {
            root: ok!(<_>::load_from(slice)),
            _key: PhantomData,
            _value: PhantomData,
        })
    }
}

impl<K, V> Store for Dict<K, V> {
    #[inline]
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        self.root.store_into(builder, finalizer)
    }
}

impl<K, V> Default for Dict<K, V> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Clone for Dict<K, V> {
    fn clone(&self) -> Self {
        Self {
            root: self.root.clone(),
            _key: PhantomData,
            _value: PhantomData,
        }
    }
}

impl<K, V> Eq for Dict<K, V> {}

impl<K, V> PartialEq for Dict<K, V> {
    fn eq(&self, other: &Self) -> bool {
        match (&self.root, &other.root) {
            (Some(this), Some(other)) => this.eq(other),
            (None, None) => true,
            _ => false,
        }
    }
}

impl<K, V> From<Option<Cell>> for Dict<K, V> {
    #[inline]
    fn from(dict: Option<Cell>) -> Self {
        Self::from_raw(dict)
    }
}

impl<K, V> std::fmt::Debug for Dict<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        debug_struct_field1_finish(f, "Dict", "root", &self.root)
    }
}

impl<K, V> Dict<K, V> {
    /// Creates an empty dictionary
    pub const fn new() -> Self {
        Self {
            root: None,
            _key: PhantomData,
            _value: PhantomData,
        }
    }

    /// Creates a dictionary from a raw cell.
    pub const fn from_raw(dict: Option<Cell>) -> Self {
        Self {
            root: dict,
            _key: PhantomData,
            _value: PhantomData,
        }
    }

    /// Returns `true` if the dictionary contains no elements.
    pub const fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// Returns the underlying root cell of the dictionary.
    #[inline]
    pub const fn root(&self) -> &Option<Cell> {
        &self.root
    }

    /// Converts into a dictionary with an equivalent value type.
    #[inline]
    pub fn cast_into<Q, T>(self) -> Dict<Q, T>
    where
        Q: EquivalentRepr<K>,
        T: EquivalentRepr<V>,
    {
        Dict {
            root: self.root,
            _key: PhantomData,
            _value: PhantomData,
        }
    }

    /// Casts itself into a lazy loaded for an equivalent type.
    pub fn cast_ref<Q, T>(&self) -> &Dict<Q, T>
    where
        Q: EquivalentRepr<K>,
        T: EquivalentRepr<V>,
    {
        // SAFETY: Dict is #[repr(transparent)]
        unsafe { &*(self as *const Self as *const Dict<Q, T>) }
    }
}

impl<K: DictKey, V> Dict<K, V> {
    /// Loads a non-empty dictionary from a root cell.
    pub fn load_from_root_ext(
        slice: &mut CellSlice<'_>,
        finalizer: &mut dyn Finalizer,
    ) -> Result<Self, Error> {
        match dict_load_from_root(slice, K::BITS, finalizer) {
            Ok(root) => Ok(Self {
                root: Some(root),
                _key: PhantomData,
                _value: PhantomData,
            }),
            Err(e) => Err(e),
        }
    }
}

impl<K, V> Dict<K, V>
where
    K: Store + DictKey,
{
    /// Returns `true` if the dictionary contains a value for the specified key.
    pub fn contains_key<Q>(&self, key: Q) -> Result<bool, Error>
    where
        Q: Borrow<K>,
    {
        fn contains_key_impl<K>(root: &Option<Cell>, key: &K) -> Result<bool, Error>
        where
            K: Store + DictKey,
        {
            let mut builder = CellBuilder::new();
            ok!(key.store_into(&mut builder, &mut Cell::default_finalizer()));
            Ok(ok!(dict_get(
                root.as_ref(),
                K::BITS,
                builder.as_data_slice(),
                &mut Cell::default_cell_context()
            ))
            .is_some())
        }
        contains_key_impl(&self.root, key.borrow())
    }
}

impl<K, V> Dict<K, V>
where
    K: Store + DictKey,
{
    /// Returns the value corresponding to the key.
    pub fn get<'a: 'b, 'b, Q>(&'a self, key: Q) -> Result<Option<V>, Error>
    where
        Q: Borrow<K> + 'b,
        V: Load<'a>,
    {
        pub fn get_impl<'a: 'b, 'b, K, V>(
            root: &'a Option<Cell>,
            key: &'b K,
        ) -> Result<Option<V>, Error>
        where
            K: Store + DictKey,
            V: Load<'a>,
        {
            let Some(mut value) = ({
                let mut builder = CellBuilder::new();
                ok!(key.store_into(&mut builder, &mut Cell::default_finalizer()));
                ok!(dict_get(
                    root.as_ref(),
                    K::BITS,
                    builder.as_data_slice(),
                    &mut Cell::default_cell_context()
                ))
            }) else {
                return Ok(None);
            };

            match V::load_from(&mut value) {
                Ok(value) => Ok(Some(value)),
                Err(e) => Err(e),
            }
        }

        get_impl(&self.root, key.borrow())
    }

    /// Returns the raw value corresponding to the key.
    pub fn get_raw<'a: 'b, 'b, Q>(&'a self, key: Q) -> Result<Option<CellSlice<'a>>, Error>
    where
        Q: Borrow<K> + 'b,
    {
        pub fn get_raw_impl<'a: 'b, 'b, K>(
            root: &'a Option<Cell>,
            key: &'b K,
        ) -> Result<Option<CellSlice<'a>>, Error>
        where
            K: Store + DictKey,
        {
            let mut builder = CellBuilder::new();
            ok!(key.store_into(&mut builder, &mut Cell::default_finalizer()));
            dict_get(
                root.as_ref(),
                K::BITS,
                builder.as_data_slice(),
                &mut Cell::default_cell_context(),
            )
        }

        get_raw_impl(&self.root, key.borrow())
    }

    /// Removes the value associated with key in dictionary.
    /// Returns an optional removed value.
    ///
    /// The dict is rebuilt using the default finalizer.
    pub fn remove<Q>(&mut self, key: Q) -> Result<Option<V>, Error>
    where
        Q: Borrow<K>,
        for<'a> V: Load<'a> + 'static,
    {
        match ok!(self.remove_raw_ext(key, &mut Cell::default_cell_context())) {
            Some((cell, range)) => {
                let mut slice = ok!(range.apply(&cell));
                Ok(Some(ok!(V::load_from(&mut slice))))
            }
            None => Ok(None),
        }
    }

    /// Removes the value associated with key in dictionary.
    /// Returns an optional removed value as cell slice parts.
    ///
    /// The dict is rebuilt using the default finalizer.
    pub fn remove_raw<Q>(&mut self, key: Q) -> Result<Option<CellSliceParts>, Error>
    where
        Q: Borrow<K>,
    {
        self.remove_raw_ext(key, &mut Cell::default_cell_context())
    }

    /// Removes the lowest key from the dict.
    /// Returns an optional removed key and value as cell slice parts.
    ///
    /// Use [`remove_bound_ext`] if you need to use a custom finalizer.
    ///
    /// [`remove_bound_ext`]: RawDict::remove_bound_ext
    pub fn remove_min_raw(&mut self, signed: bool) -> Result<Option<(K, CellSliceParts)>, Error> {
        self.remove_bound_raw_ext(DictBound::Min, signed, &mut Cell::default_cell_context())
    }

    /// Removes the largest key from the dict.
    /// Returns an optional removed key and value as cell slice parts.
    ///
    /// Use [`remove_bound_ext`] if you need to use a custom finalizer.
    ///
    /// [`remove_bound_ext`]: RawDict::remove_bound_ext
    pub fn remove_max_raw(&mut self, signed: bool) -> Result<Option<(K, CellSliceParts)>, Error> {
        self.remove_bound_raw_ext(DictBound::Max, signed, &mut Cell::default_cell_context())
    }

    /// Removes the specified dict bound.
    /// Returns an optional removed key and value as cell slice parts.
    ///
    /// Use [`remove_bound_ext`] if you need to use a custom finalizer.
    ///
    /// [`remove_bound_ext`]: RawDict::remove_bound_ext
    pub fn remove_bound_raw(
        &mut self,
        bound: DictBound,
        signed: bool,
    ) -> Result<Option<(K, CellSliceParts)>, Error> {
        self.remove_bound_raw_ext(bound, signed, &mut Cell::default_cell_context())
    }
}

impl<K, V> Dict<K, V>
where
    K: Store + DictKey,
    V: Store,
{
    /// Sets the value associated with the key in the dictionary.
    ///
    /// Use [`set_ext`] if you need to use a custom finalizer.
    ///
    /// [`set_ext`]: Dict::set_ext
    pub fn set<Q, T>(&mut self, key: Q, value: T) -> Result<bool, Error>
    where
        Q: Borrow<K>,
        T: Borrow<V>,
    {
        self.set_ext(key, value, &mut Cell::default_cell_context())
    }

    /// Sets the value associated with the key in the dictionary
    /// only if the key was already present in it.
    ///
    /// Use [`replace_ext`] if you need to use a custom finalizer.
    ///
    /// [`replace_ext`]: Dict::replace_ext
    pub fn replace<Q, T>(&mut self, key: Q, value: T) -> Result<bool, Error>
    where
        Q: Borrow<K>,
        T: Borrow<V>,
    {
        self.replace_ext(key, value, &mut Cell::default_cell_context())
    }

    /// Sets the value associated with key in dictionary,
    /// but only if it is not already present.
    ///
    /// Use [`add_ext`] if you need to use a custom finalizer.
    ///
    /// [`add_ext`]: Dict::add_ext
    pub fn add<Q, T>(&mut self, key: Q, value: T) -> Result<bool, Error>
    where
        Q: Borrow<K>,
        T: Borrow<V>,
    {
        self.add_ext(key, value, &mut Cell::default_cell_context())
    }
}

impl<K, V> Dict<K, V>
where
    K: Store + DictKey,
{
    /// Gets an iterator over the entries of the dictionary, sorted by key.
    /// The iterator element type is `Result<(K, V)>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    ///
    /// # Performance
    ///
    /// In the current implementation, iterating over dictionary builds a key
    /// for each element. Use [`values`] or [`raw_values`] if you don't need keys from an iterator.
    ///
    /// [`values`]: Dict::values
    /// [`raw_values`]: Dict::raw_values
    pub fn iter<'a>(&'a self) -> Iter<'_, K, V>
    where
        V: Load<'a>,
    {
        Iter::new(&self.root)
    }

    /// Gets an iterator over the keys of the dictionary, in sorted order.
    /// The iterator element type is `Result<K>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    ///
    /// # Performance
    ///
    /// In the current implementation, iterating over dictionary builds a key
    /// for each element. Use [`values`] if you don't need keys from an iterator.
    ///
    /// [`values`]: Dict::values
    pub fn keys(&'_ self) -> Keys<'_, K> {
        Keys::new(&self.root)
    }

    /// Computes the minimal key in dictionary that is lexicographically greater than `key`,
    /// and returns it along with associated value as cell slice parts.
    #[inline]
    pub fn get_next<Q>(&self, key: Q, signed: bool) -> Result<Option<(K, V)>, Error>
    where
        Q: Borrow<K>,
        for<'a> V: Load<'a>,
    {
        self.find_ext(key, DictBound::Max, false, signed)
    }

    /// Computes the maximal key in dictionary that is lexicographically smaller than `key`,
    /// and returns it along with associated value as cell slice parts.
    #[inline]
    pub fn get_prev<Q>(&self, key: Q, signed: bool) -> Result<Option<(K, V)>, Error>
    where
        Q: Borrow<K>,
        for<'a> V: Load<'a>,
    {
        self.find_ext(key, DictBound::Min, false, signed)
    }

    /// Computes the minimal key in dictionary that is lexicographically greater than `key`,
    /// and returns it along with associated value as cell slice parts.
    #[inline]
    pub fn get_or_next<Q>(&self, key: Q, signed: bool) -> Result<Option<(K, V)>, Error>
    where
        Q: Borrow<K>,
        for<'a> V: Load<'a>,
    {
        self.find_ext(key, DictBound::Max, true, signed)
    }

    /// Computes the maximal key in dictionary that is lexicographically smaller than `key`,
    /// and returns it along with associated value as cell slice parts.
    #[inline]
    pub fn get_or_prev<Q>(&self, key: Q, signed: bool) -> Result<Option<(K, V)>, Error>
    where
        Q: Borrow<K>,
        for<'a> V: Load<'a>,
    {
        self.find_ext(key, DictBound::Min, true, signed)
    }

    #[inline]
    fn find_ext<Q>(
        &self,
        key: Q,
        towards: DictBound,
        inclusive: bool,
        signed: bool,
    ) -> Result<Option<(K, V)>, Error>
    where
        Q: Borrow<K>,
        for<'a> V: Load<'a>,
    {
        fn find_impl<K, V>(
            root: &Option<Cell>,
            key: &K,
            towards: DictBound,
            inclusive: bool,
            signed: bool,
        ) -> Result<Option<(K, V)>, Error>
        where
            K: DictKey + Store,
            for<'a> V: Load<'a>,
        {
            let Some((key, (cell, range))) = ({
                let mut builder = CellBuilder::new();
                ok!(key.store_into(&mut builder, &mut Cell::default_finalizer()));
                // TODO: add `dict_find` with non-owned return type
                ok!(dict_find_owned(
                    root.clone(),
                    K::BITS,
                    builder.as_data_slice(),
                    towards,
                    inclusive,
                    signed,
                    &mut Cell::default_cell_context()
                ))
            }) else {
                return Ok(None);
            };
            let value = &mut ok!(range.apply(&cell));

            match K::from_raw_data(key.raw_data()) {
                Some(key) => Ok(Some((key, ok!(V::load_from(value))))),
                None => Err(Error::CellUnderflow),
            }
        }

        find_impl(&self.root, key.borrow(), towards, inclusive, signed)
    }
}

impl<K, V> Dict<K, V>
where
    K: DictKey,
{
    /// Gets an iterator over the values of the dictionary, in order by key.
    /// The iterator element type is `Result<V>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn values<'a>(&'a self) -> Values<'a, V>
    where
        V: Load<'a>,
    {
        Values::new(&self.root, K::BITS)
    }

    /// Returns the lowest key and a value corresponding to the key.
    pub fn get_min<'a>(&'a self, signed: bool) -> Result<Option<(K, V)>, Error>
    where
        V: Load<'a>,
    {
        Ok(match ok!(self.get_bound_raw(DictBound::Min, signed)) {
            Some((key, ref mut value)) => Some((key, ok!(V::load_from(value)))),
            None => None,
        })
    }

    /// Returns the lowest key and a value corresponding to the key.
    pub fn get_max<'a>(&'a self, signed: bool) -> Result<Option<(K, V)>, Error>
    where
        V: Load<'a>,
    {
        Ok(match ok!(self.get_bound_raw(DictBound::Max, signed)) {
            Some((key, ref mut value)) => Some((key, ok!(V::load_from(value)))),
            None => None,
        })
    }

    /// Finds the specified dict bound and returns a key and a raw value corresponding to the key.
    pub fn get_bound_raw(
        &self,
        bound: DictBound,
        signed: bool,
    ) -> Result<Option<(K, CellSlice<'_>)>, Error> {
        let Some((key, value)) = ok!(dict_find_bound(
            self.root.as_ref(),
            K::BITS,
            bound,
            signed,
            &mut Cell::default_cell_context()
        )) else {
            return Ok(None);
        };
        match K::from_raw_data(key.raw_data()) {
            Some(key) => Ok(Some((key, value))),
            None => Err(Error::CellUnderflow),
        }
    }

    /// Removes the specified dict bound.
    /// Returns an optional removed key and value as cell slice parts.
    ///
    /// Key and dict are serialized using the provided finalizer.
    pub fn remove_bound_raw_ext(
        &mut self,
        bound: DictBound,
        signed: bool,
        context: &mut dyn CellContext,
    ) -> Result<Option<(K, CellSliceParts)>, Error> {
        let (dict, removed) = ok!(dict_remove_bound_owned(
            self.root.clone(),
            K::BITS,
            bound,
            signed,
            context
        ));
        self.root = dict;
        Ok(match removed {
            Some((key, value)) => match K::from_raw_data(key.raw_data()) {
                Some(key) => Some((key, value)),
                None => return Err(Error::CellUnderflow),
            },
            None => None,
        })
    }
}

impl<K, V> Dict<K, V>
where
    K: Store + DictKey,
{
    /// Removes the value associated with key in dictionary.
    /// Returns an optional removed value as cell slice parts.
    ///
    /// Dict is rebuild using the provided finalizer.
    pub fn remove_raw_ext<Q>(
        &mut self,
        key: Q,
        context: &mut dyn CellContext,
    ) -> Result<Option<CellSliceParts>, Error>
    where
        Q: Borrow<K>,
    {
        pub fn remove_raw_ext_impl<K>(
            root: &Option<Cell>,
            key: &K,
            context: &mut dyn CellContext,
        ) -> Result<(Option<Cell>, Option<CellSliceParts>), Error>
        where
            K: Store + DictKey,
        {
            let mut builder = CellBuilder::new();
            ok!(key.store_into(&mut builder, &mut Cell::default_finalizer()));
            dict_remove_owned(
                root.as_ref(),
                &mut builder.as_data_slice(),
                K::BITS,
                false,
                context,
            )
        }

        let (dict, removed) = ok!(remove_raw_ext_impl(&self.root, key.borrow(), context));
        self.root = dict;
        Ok(removed)
    }

    /// Gets an iterator over the raw entries of the dictionary, sorted by key.
    /// The iterator element type is `Result<(CellBuilder, CellSlice)>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    ///
    /// # Performance
    ///
    /// In the current implementation, iterating over dictionary builds a key
    /// for each element. Use [`values`] or [`raw_values`] if you don't need keys from an iterator.
    ///
    /// [`values`]: Dict::values
    /// [`raw_values`]: Dict::raw_values
    pub fn raw_iter(&'_ self) -> RawIter<'_> {
        RawIter::new(&self.root, K::BITS)
    }

    /// Gets an iterator over the raw keys of the dictionary, in sorted order.
    /// The iterator element type is `Result<CellBuilder>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    ///
    /// # Performance
    ///
    /// In the current implementation, iterating over dictionary builds a key
    /// for each element. Use [`values`] or [`raw_values`] if you don't need keys from an iterator.
    ///
    /// [`values`]: Dict::values
    /// [`raw_values`]: Dict::raw_values
    pub fn raw_keys(&'_ self) -> RawKeys<'_> {
        RawKeys::new(&self.root, K::BITS)
    }
}

impl<K, V> Dict<K, V>
where
    K: DictKey,
{
    /// Gets an iterator over the raw values of the dictionary, in order by key.
    /// The iterator element type is `Result<CellSlice>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn raw_values(&'_ self) -> RawValues<'_> {
        RawValues::new(&self.root, K::BITS)
    }
}

impl<K, V> Dict<K, V>
where
    K: Store + DictKey,
    V: Store,
{
    /// Sets the value associated with the key in the dictionary.
    pub fn set_ext<Q, T>(
        &mut self,
        key: Q,
        value: T,
        context: &mut dyn CellContext,
    ) -> Result<bool, Error>
    where
        Q: Borrow<K>,
        T: Borrow<V>,
    {
        self.insert_impl(key.borrow(), value.borrow(), SetMode::Set, context)
    }

    /// Sets the value associated with the key in the dictionary
    /// only if the key was already present in it.
    pub fn replace_ext<Q, T>(
        &mut self,
        key: Q,
        value: T,
        context: &mut dyn CellContext,
    ) -> Result<bool, Error>
    where
        Q: Borrow<K>,
        T: Borrow<V>,
    {
        self.insert_impl(key.borrow(), value.borrow(), SetMode::Replace, context)
    }

    /// Sets the value associated with key in dictionary,
    /// but only if it is not already present.
    pub fn add_ext<Q, T>(
        &mut self,
        key: Q,
        value: T,
        context: &mut dyn CellContext,
    ) -> Result<bool, Error>
    where
        Q: Borrow<K>,
        T: Borrow<V>,
    {
        self.insert_impl(key.borrow(), value.borrow(), SetMode::Add, context)
    }

    fn insert_impl(
        &mut self,
        key: &K,
        value: &V,
        mode: SetMode,
        context: &mut dyn CellContext,
    ) -> Result<bool, Error>
    where
        K: Store + DictKey,
        V: Store,
    {
        let (new_root, changed) = {
            let mut key_builder = CellBuilder::new();
            ok!(key.store_into(&mut key_builder, &mut Cell::default_finalizer()));
            ok!(dict_insert(
                self.root.as_ref(),
                &mut key_builder.as_data_slice(),
                K::BITS,
                value,
                mode,
                context
            ))
        };
        self.root = new_root;
        Ok(changed)
    }
}

/// An iterator over the entries of a [`Dict`].
///
/// This struct is created by the [`iter`] method on [`Dict`]. See its documentation for more.
///
/// [`iter`]: Dict::iter
pub struct Iter<'a, K, V> {
    inner: RawIter<'a>,
    _key: PhantomData<K>,
    _value: PhantomData<V>,
}

impl<K, V> Clone for Iter<'_, K, V> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            _key: PhantomData,
            _value: PhantomData,
        }
    }
}

impl<'a, K, V> Iter<'a, K, V>
where
    K: DictKey,
{
    /// Creates an iterator over the entries of a dictionary.
    pub fn new(root: &'a Option<Cell>) -> Self {
        Self {
            inner: RawIter::new(root, K::BITS),
            _key: PhantomData,
            _value: PhantomData,
        }
    }

    /// Changes the direction of the iterator to descending.
    #[inline]
    pub fn reversed(mut self) -> Self {
        self.inner = self.inner.reversed();
        self
    }

    /// Changes the behavior of the iterator to reverse the high bit.
    #[inline]
    pub fn signed(mut self) -> Self {
        self.inner = self.inner.signed();
        self
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
where
    K: DictKey,
    V: Load<'a>,
{
    type Item = Result<(K, V), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.inner.next()? {
            Ok((key, mut value)) => {
                let err = if let Some(key) = K::from_raw_data(key.raw_data()) {
                    match V::load_from(&mut value) {
                        Ok(value) => return Some(Ok((key, value))),
                        Err(e) => e,
                    }
                } else {
                    Error::CellUnderflow
                };
                Err(self.inner.finish(err))
            }
            Err(e) => Err(e),
        })
    }
}

/// An iterator over the keys of a [`Dict`].
///
/// This struct is created by the [`keys`] method on [`Dict`]. See its
/// documentation for more.
///
/// [`keys`]: Dict::keys
pub struct Keys<'a, K> {
    inner: RawIter<'a>,
    _key: PhantomData<K>,
}

impl<'a, K> Clone for Keys<'a, K> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            _key: PhantomData,
        }
    }
}

impl<'a, K> Keys<'a, K>
where
    K: DictKey,
{
    /// Creates an iterator over the keys of a dictionary.
    pub fn new(root: &'a Option<Cell>) -> Self {
        Self {
            inner: RawIter::new(root, K::BITS),
            _key: PhantomData,
        }
    }

    /// Changes the direction of the iterator to descending.
    #[inline]
    pub fn reversed(mut self) -> Self {
        self.inner = self.inner.reversed();
        self
    }

    /// Changes the behavior of the iterator to reverse the high bit.
    #[inline]
    pub fn signed(mut self) -> Self {
        self.inner = self.inner.signed();
        self
    }
}

impl<'a, K> Iterator for Keys<'a, K>
where
    K: DictKey,
{
    type Item = Result<K, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.inner.next()? {
            Ok((key, _)) => match K::from_raw_data(key.raw_data()) {
                Some(key) => Ok(key),
                None => Err(self.inner.finish(Error::CellUnderflow)),
            },
            Err(e) => Err(e),
        })
    }
}

/// An iterator over the values of a [`Dict`].
///
/// This struct is created by the [`values`] method on [`Dict`]. See its documentation for more.
///
/// [`values`]: Dict::values
pub struct Values<'a, V> {
    inner: RawValues<'a>,
    _value: PhantomData<V>,
}

impl<V> Clone for Values<'_, V> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            _value: PhantomData,
        }
    }
}

impl<'a, V> Values<'a, V> {
    /// Creates an iterator over the values of a dictionary.
    pub fn new(root: &'a Option<Cell>, bit_len: u16) -> Self {
        Self {
            inner: RawValues::new(root, bit_len),
            _value: PhantomData,
        }
    }

    /// Changes the direction of the iterator to descending.
    #[inline]
    pub fn reversed(mut self) -> Self {
        self.inner = self.inner.reversed();
        self
    }

    /// Changes the behavior of the iterator to reverse the high bit.
    #[inline]
    pub fn signed(mut self) -> Self {
        self.inner = self.inner.signed();
        self
    }
}

impl<'a, V> Iterator for Values<'a, V>
where
    V: Load<'a>,
{
    type Item = Result<V, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next()? {
            Ok(mut value) => match V::load_from(&mut value) {
                Ok(value) => Some(Ok(value)),
                Err(e) => Some(Err(self.inner.finish(e))),
            },
            Err(e) => Some(Err(e)),
        }
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Context;

    use super::*;
    use crate::prelude::*;

    #[test]
    fn dict_set() {
        let mut dict = Dict::<u32, u16>::new();
        assert!(dict.set(123, 0xffff).unwrap());
        assert_eq!(dict.get(123).unwrap(), Some(0xffff));

        assert!(dict.set(123, 0xcafe).unwrap());
        assert_eq!(dict.get(123).unwrap(), Some(0xcafe));
    }

    #[test]
    #[cfg_attr(miri, ignore)] // takes too long to execute on miri
    fn dict_set_complex() {
        let mut dict = Dict::<u32, bool>::new();
        for i in 0..520 {
            assert!(dict.set(i, true).unwrap());
        }
    }

    #[test]
    fn dict_bounds() {
        let mut dict = Dict::<i32, bool>::new();
        for i in -10..=10 {
            assert!(dict.set(i, i < 0).unwrap());
        }

        assert_eq!(dict.get_min(false).unwrap(), Some((0, false)));
        assert_eq!(dict.get_max(false).unwrap(), Some((-1, true)));

        assert_eq!(dict.get_min(true).unwrap(), Some((-10, true)));
        assert_eq!(dict.get_max(true).unwrap(), Some((10, false)));

        let mut dict = Dict::<u32, u8>::new();
        for i in 1..=3 {
            dict.set(i, 0xff).unwrap();
        }
        assert_eq!(dict.get_min(false).unwrap(), Some((1, 0xff)));
        assert_eq!(dict.get_max(false).unwrap(), Some((3, 0xff)));
    }

    #[test]
    fn dict_remove_bounds() {
        let mut dict = Dict::<i32, bool>::new();
        for i in -10..=10 {
            dict.set(i, i < 0).unwrap();
        }

        let parse_removed = |(i, (cell, range)): (i32, CellSliceParts)| {
            let mut value = range.apply(&cell)?;
            let value = bool::load_from(&mut value)?;
            Ok::<_, Error>((i, value))
        };

        // Min, unsigned
        {
            let mut dict = dict.clone();
            for i in 0..=10 {
                let removed = dict.remove_min_raw(false).unwrap().unwrap();
                assert_eq!(parse_removed(removed).unwrap(), (i, false));
            }
            for i in -10..=-1 {
                let removed = dict.remove_min_raw(false).unwrap().unwrap();
                assert_eq!(parse_removed(removed).unwrap(), (i, true));
            }
            assert!(dict.is_empty());
        }

        // Min, signed
        {
            let mut dict = dict.clone();
            for i in -10..=10 {
                let removed = dict.remove_min_raw(true).unwrap().unwrap();
                assert_eq!(parse_removed(removed).unwrap(), (i, i < 0));
            }
            assert!(dict.is_empty());
        }

        // Max, unsigned
        {
            let mut dict = dict.clone();
            for i in (-10..=-1).rev() {
                let removed = dict.remove_max_raw(false).unwrap().unwrap();
                assert_eq!(parse_removed(removed).unwrap(), (i, true));
            }
            for i in (0..=10).rev() {
                let removed = dict.remove_max_raw(false).unwrap().unwrap();
                assert_eq!(parse_removed(removed).unwrap(), (i, false));
            }
            assert!(dict.is_empty());
        }

        // Max, signed
        {
            let mut dict = dict.clone();
            for i in (-10..=10).rev() {
                let removed = dict.remove_max_raw(true).unwrap().unwrap();
                assert_eq!(parse_removed(removed).unwrap(), (i, i < 0));
            }
            assert!(dict.is_empty());
        }
    }

    #[test]
    fn dict_replace() {
        let mut dict = Dict::<u32, bool>::new();
        assert!(!dict.replace(123, false).unwrap());
        assert!(!dict.contains_key(123).unwrap());

        assert!(dict.set(123, false).unwrap());
        assert_eq!(dict.get(123).unwrap(), Some(false));
        assert!(dict.replace(123, true).unwrap());
        assert_eq!(dict.get(123).unwrap(), Some(true));
    }

    #[test]
    fn dict_add() {
        let mut dict = Dict::<u32, bool>::new();

        assert!(dict.add(123, false).unwrap());
        assert_eq!(dict.get(123).unwrap(), Some(false));

        assert!(!dict.add(123, true).unwrap());
        assert_eq!(dict.get(123).unwrap(), Some(false));
    }

    #[test]
    fn dict_remove() {
        let mut dict = Dict::<u32, u32>::new();

        for i in 0..10 {
            assert!(dict.set(i, i).unwrap());
        }

        let mut check_remove = |n: u32, expected: Option<u32>| -> anyhow::Result<()> {
            let removed = dict.remove(n).context("Failed to remove")?;
            anyhow::ensure!(removed == expected);
            Ok(())
        };

        check_remove(0, Some(0)).unwrap();

        check_remove(4, Some(4)).unwrap();

        check_remove(9, Some(9)).unwrap();
        check_remove(9, None).unwrap();

        check_remove(5, Some(5)).unwrap();
        check_remove(5, None).unwrap();

        check_remove(100, None).unwrap();

        check_remove(1, Some(1)).unwrap();
        check_remove(2, Some(2)).unwrap();
        check_remove(3, Some(3)).unwrap();
        check_remove(6, Some(6)).unwrap();
        check_remove(7, Some(7)).unwrap();
        check_remove(8, Some(8)).unwrap();

        assert!(dict.is_empty());
    }

    #[test]
    fn dict_iter() {
        let boc = Boc::decode_base64("te6ccgEBFAEAeAABAcABAgPOQAUCAgHUBAMACQAAAI3gAAkAAACjoAIBIA0GAgEgCgcCASAJCAAJAAAAciAACQAAAIfgAgEgDAsACQAAAFZgAAkAAABsIAIBIBEOAgEgEA8ACQAAADqgAAkAAABQYAIBIBMSAAkAAAAe4AAJAAAAv2A=").unwrap();
        let dict = boc.parse::<Dict<u32, u32>>().unwrap();

        let size = dict.values().count();
        assert_eq!(size, 10);

        for (i, entry) in dict.iter().enumerate() {
            let (key, _) = entry.unwrap();
            assert_eq!(key, i as u32);
        }

        let signed_range = -10..10;

        let mut dict = Dict::<i32, i32>::new();
        for i in signed_range.clone() {
            assert!(dict.set(i, i).unwrap());
        }

        let mut signed_range_iter = signed_range.clone();
        for (entry, i) in dict.iter().signed().zip(&mut signed_range_iter) {
            let (key, value) = entry.unwrap();
            assert_eq!(key, i);
            assert_eq!(value, i);
        }
        assert_eq!(signed_range_iter.next(), None);

        let mut signed_range_iter = signed_range.rev();
        for (entry, i) in dict.iter().reversed().signed().zip(&mut signed_range_iter) {
            let (key, value) = entry.unwrap();
            assert_eq!(key, i);
            assert_eq!(value, i);
        }
        assert_eq!(signed_range_iter.next(), None);
    }

    #[test]
    fn dict_next_prev_unsigned() {
        let mut dict = Dict::<u32, u32>::new();

        for i in 0..=10 {
            dict.set(i, i).unwrap();
        }

        for i in 20..=30 {
            dict.set(i, i).unwrap();
        }

        println!("{}", BocRepr::encode_base64(&dict).unwrap());

        assert_eq!(dict.get_prev(0, false).unwrap(), None);
        assert_eq!(dict.get_or_prev(0, false).unwrap(), Some((0, 0)));

        assert_eq!(dict.get_next(30, false).unwrap(), None);
        assert_eq!(dict.get_or_next(30, false).unwrap(), Some((30, 30)));

        assert_eq!(dict.get_prev(15, false).unwrap(), Some((10, 10)));
        assert_eq!(dict.get_or_prev(15, false).unwrap(), Some((10, 10)));

        assert_eq!(dict.get_next(15, false).unwrap(), Some((20, 20)));
        assert_eq!(dict.get_or_next(15, false).unwrap(), Some((20, 20)));

        assert_eq!(dict.get_next(19, false).unwrap(), Some((20, 20)));
        assert_eq!(dict.get_or_next(19, false).unwrap(), Some((20, 20)));

        assert_eq!(dict.get_prev(20, false).unwrap(), Some((10, 10)));
        assert_eq!(dict.get_or_prev(20, false).unwrap(), Some((20, 20)));

        assert_eq!(dict.get_next(100, false).unwrap(), None);
        assert_eq!(dict.get_or_next(100, false).unwrap(), None);

        assert_eq!(dict.get_prev(100, false).unwrap(), Some((30, 30)));
        assert_eq!(dict.get_or_prev(100, false).unwrap(), Some((30, 30)));
    }

    #[test]
    fn dict_next_prev_signed() {
        let mut dict = Dict::<i32, i32>::new();

        for i in -20..=-10 {
            dict.set(i, i).unwrap();
        }

        assert_eq!(dict.get_prev(-20, true).unwrap(), None);
        assert_eq!(dict.get_or_prev(-20, true).unwrap(), Some((-20, -20)));

        assert_eq!(dict.get_next(-10, true).unwrap(), None);
        assert_eq!(dict.get_or_next(-10, true).unwrap(), Some((-10, -10)));

        for i in 10..=20 {
            dict.set(i, i).unwrap();
        }

        println!("{}", BocRepr::encode_base64(&dict).unwrap());

        assert_eq!(dict.get_next(-100, true).unwrap(), Some((-20, -20)));
        assert_eq!(dict.get_or_next(-100, true).unwrap(), Some((-20, -20)));

        assert_eq!(dict.get_prev(-100, true).unwrap(), None);
        assert_eq!(dict.get_or_prev(-100, true).unwrap(), None);

        assert_eq!(dict.get_prev(-20, true).unwrap(), None);
        assert_eq!(dict.get_or_prev(-20, true).unwrap(), Some((-20, -20)));

        assert_eq!(dict.get_next(20, true).unwrap(), None);
        assert_eq!(dict.get_or_next(20, true).unwrap(), Some((20, 20)));

        assert_eq!(dict.get_prev(-10, true).unwrap(), Some((-11, -11)));
        assert_eq!(dict.get_or_prev(-10, true).unwrap(), Some((-10, -10)));

        assert_eq!(dict.get_next(-10, true).unwrap(), Some((10, 10)));
        assert_eq!(dict.get_or_next(-10, true).unwrap(), Some((-10, -10)));

        assert_eq!(dict.get_prev(-9, true).unwrap(), Some((-10, -10)));
        assert_eq!(dict.get_or_prev(-9, true).unwrap(), Some((-10, -10)));

        assert_eq!(dict.get_prev(0, true).unwrap(), Some((-10, -10)));
        assert_eq!(dict.get_or_prev(0, true).unwrap(), Some((-10, -10)));

        assert_eq!(dict.get_next(0, true).unwrap(), Some((10, 10)));
        assert_eq!(dict.get_or_next(0, true).unwrap(), Some((10, 10)));

        assert_eq!(dict.get_prev(10, true).unwrap(), Some((-10, -10)));
        assert_eq!(dict.get_or_prev(10, true).unwrap(), Some((10, 10)));

        assert_eq!(dict.get_next(100, true).unwrap(), None);
        assert_eq!(dict.get_or_next(100, true).unwrap(), None);

        assert_eq!(dict.get_prev(100, true).unwrap(), Some((20, 20)));
        assert_eq!(dict.get_or_prev(100, true).unwrap(), Some((20, 20)));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn big_dict() {
        use rand::{Rng, SeedableRng};

        let mut rng = rand_xorshift::XorShiftRng::from_seed([0u8; 16]);

        let values = (0..100000)
            .map(|_| (rng.gen::<u32>(), rng.gen::<u64>()))
            .collect::<Vec<_>>();

        // Wrap builder into a new function for the flamegraph
        #[inline(never)]
        fn test_big_dict(values: &[(u32, u64)]) -> Dict<u32, u64> {
            let mut result = Dict::<u32, u64>::new();
            for (key, value) in values {
                result.set(key, value).unwrap();
            }
            result
        }

        test_big_dict(&values);
    }
}
