use std::borrow::Borrow;
use std::marker::PhantomData;

use crate::cell::*;
use crate::util::*;
use crate::Error;

use super::raw::*;
use super::{dict_get, dict_insert, dict_load_from_root, serialize_entry, DictKey, SetMode};

/// Typed dictionary with fixed length keys.
pub struct Dict<C: CellFamily, K, V> {
    pub(crate) root: Option<CellContainer<C>>,
    _key: PhantomData<K>,
    _value: PhantomData<V>,
}

impl<'a, C: CellFamily, K, V> Load<'a, C> for Dict<C, K, V> {
    #[inline]
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            root: <_>::load_from(slice)?,
            _key: PhantomData,
            _value: PhantomData,
        })
    }
}

impl<C: CellFamily, K, V> Store<C> for Dict<C, K, V> {
    #[inline]
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.root.store_into(builder, finalizer)
    }
}

impl<C: CellFamily, K, V> Default for Dict<C, K, V> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<C: CellFamily, K, V> Clone for Dict<C, K, V> {
    fn clone(&self) -> Self {
        Self {
            root: self.root.clone(),
            _key: PhantomData,
            _value: PhantomData,
        }
    }
}

impl<C: CellFamily, K, V> Eq for Dict<C, K, V> {}

impl<C: CellFamily, K, V> PartialEq for Dict<C, K, V> {
    fn eq(&self, other: &Self) -> bool {
        match (&self.root, &other.root) {
            (Some(this), Some(other)) => this.eq(other),
            (None, None) => true,
            _ => false,
        }
    }
}

impl<C: CellFamily, K, V> From<Option<CellContainer<C>>> for Dict<C, K, V> {
    #[inline]
    fn from(dict: Option<CellContainer<C>>) -> Self {
        Self {
            root: dict,
            _key: PhantomData,
            _value: PhantomData,
        }
    }
}

impl<C: CellFamily, K, V> std::fmt::Debug for Dict<C, K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        debug_struct_field1_finish(f, "Dict", "root", &self.root)
    }
}

impl<C: CellFamily, K, V> Dict<C, K, V> {
    /// Creates an empty dictionary
    pub const fn new() -> Self {
        Self {
            root: None,
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
    pub const fn root(&self) -> &Option<CellContainer<C>> {
        &self.root
    }
}

impl<C, K, V> Dict<C, K, V>
where
    for<'c> C: CellFamily + 'c,
    K: DictKey,
{
    /// Loads a non-empty dictionary from a root cell.
    pub fn load_from_root_ext(
        slice: &mut CellSlice<'_, C>,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Option<Self> {
        Some(Self {
            root: Some(dict_load_from_root(slice, K::BITS, finalizer)?),
            _key: PhantomData,
            _value: PhantomData,
        })
    }
}

impl<C, K, V> Dict<C, K, V>
where
    for<'c> C: DefaultFinalizer + 'c,
    K: Store<C> + DictKey,
{
    /// Returns `true` if the dictionary contains a value for the specified key.
    pub fn contains_key<Q>(&self, key: Q) -> Result<bool, Error>
    where
        Q: Borrow<K>,
    {
        fn contains_key_impl<C, K>(root: &Option<CellContainer<C>>, key: &K) -> Result<bool, Error>
        where
            for<'c> C: DefaultFinalizer + 'c,
            K: Store<C> + DictKey,
        {
            let key = ok!(serialize_entry(key, &mut C::default_finalizer()));
            Ok(ok!(dict_get(root, K::BITS, key.as_ref().as_slice())).is_some())
        }
        contains_key_impl(&self.root, key.borrow())
    }
}

impl<C, K, V> Dict<C, K, V>
where
    for<'c> C: DefaultFinalizer + 'c,
    K: Store<C> + DictKey,
{
    /// Returns the value corresponding to the key.
    ///
    /// Key is serialized using the default finalizer.
    pub fn get<'a: 'b, 'b, Q>(&'a self, key: Q) -> Result<Option<V>, Error>
    where
        Q: Borrow<K> + 'b,
        V: Load<'a, C>,
    {
        self.get_ext(key, &mut C::default_finalizer())
    }

    /// Returns the raw value corresponding to the key.
    ///
    /// Key is serialized using the default finalizer.
    pub fn get_raw<'a: 'b, 'b, Q>(&'a self, key: Q) -> Result<Option<CellSlice<'a, C>>, Error>
    where
        Q: Borrow<K> + 'b,
    {
        self.get_raw_ext(key, &mut C::default_finalizer())
    }
}

impl<C, K, V> Dict<C, K, V>
where
    for<'c> C: DefaultFinalizer + 'c,
    K: Store<C> + DictKey,
    V: Store<C>,
{
    /// Sets the value associated with the key in the dictionary.
    ///
    /// Use [`set_ext`] if you need to use a custom finalizer.
    ///
    /// [`set_ext`]: Dict::set_ext
    pub fn set<Q, T>(&mut self, key: Q, value: T) -> Result<(), Error>
    where
        Q: Borrow<K>,
        T: Borrow<V>,
    {
        self.set_ext(key, value, &mut C::default_finalizer())
    }

    /// Sets the value associated with the key in the dictionary
    /// only if the key was already present in it.
    ///
    /// Use [`replace_ext`] if you need to use a custom finalizer.
    ///
    /// [`replace_ext`]: Dict::replace_ext
    pub fn replace<Q, T>(&mut self, key: Q, value: T) -> Result<(), Error>
    where
        Q: Borrow<K>,
        T: Borrow<V>,
    {
        self.replace_ext(key, value, &mut C::default_finalizer())
    }

    /// Sets the value associated with key in dictionary,
    /// but only if it is not already present.
    ///
    /// Use [`add_ext`] if you need to use a custom finalizer.
    ///
    /// [`add_ext`]: Dict::add_ext
    pub fn add<Q, T>(&mut self, key: Q, value: T) -> Result<(), Error>
    where
        Q: Borrow<K>,
        T: Borrow<V>,
    {
        self.add_ext(key, value, &mut C::default_finalizer())
    }
}

impl<C: CellFamily, K, V> Dict<C, K, V>
where
    K: Store<C> + DictKey,
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
    pub fn iter<'a>(&'a self) -> Iter<'_, C, K, V>
    where
        V: Load<'a, C>,
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
    pub fn keys(&'_ self) -> Keys<'_, C, K> {
        Keys::new(&self.root)
    }
}

impl<C, K, V> Dict<C, K, V>
where
    for<'c> C: DefaultFinalizer + 'c,
    K: DictKey,
{
    /// Gets an iterator over the values of the dictionary, in order by key.
    /// The iterator element type is `Result<V>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn values<'a>(&'a self) -> Values<'a, C, V>
    where
        V: Load<'a, C>,
    {
        Values::new(&self.root, K::BITS)
    }
}

impl<C, K, V> Dict<C, K, V>
where
    for<'c> C: CellFamily + 'c,
    K: Store<C> + DictKey,
{
    /// Returns the value corresponding to the key.
    ///
    /// Key is serialized using the provided finalizer.
    pub fn get_ext<'a: 'b, 'b, Q>(
        &'a self,
        key: Q,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Result<Option<V>, Error>
    where
        Q: Borrow<K> + 'b,
        V: Load<'a, C>,
    {
        pub fn get_ext_impl<'a: 'b, 'b, C, K, V>(
            root: &'a Option<CellContainer<C>>,
            key: &'b K,
            finalizer: &mut dyn Finalizer<C>,
        ) -> Result<Option<V>, Error>
        where
            for<'c> C: CellFamily + 'c,
            K: Store<C> + DictKey,
            V: Load<'a, C>,
        {
            let key = ok!(serialize_entry(key, finalizer));
            let Some(mut value) = ok!(dict_get(root, K::BITS, key.as_ref().as_slice())) else {
                return Ok(None);
            };

            match V::load_from(&mut value) {
                Some(value) => Ok(Some(value)),
                None => Err(Error::CellUnderflow),
            }
        }

        get_ext_impl(&self.root, key.borrow(), finalizer)
    }

    /// Returns the value corresponding to the key.
    ///
    /// Key is serialized using the provided finalizer.
    pub fn get_raw_ext<'a: 'b, 'b, Q>(
        &'a self,
        key: Q,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Result<Option<CellSlice<'a, C>>, Error>
    where
        Q: Borrow<K> + 'b,
    {
        pub fn get_raw_ext_impl<'a: 'b, 'b, C, K>(
            root: &'a Option<CellContainer<C>>,
            key: &'b K,
            finalizer: &mut dyn Finalizer<C>,
        ) -> Result<Option<CellSlice<'a, C>>, Error>
        where
            for<'c> C: CellFamily + 'c,
            K: Store<C> + DictKey,
        {
            let key = ok!(serialize_entry(key, finalizer));
            dict_get(root, K::BITS, key.as_ref().as_slice())
        }

        get_raw_ext_impl(&self.root, key.borrow(), finalizer)
    }

    /// Gets an iterator over the raw entries of the dictionary, sorted by key.
    /// The iterator element type is `Result<(CellBuilder<C>, CellSlice<C>)>`.
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
    pub fn raw_iter(&'_ self) -> RawIter<'_, C> {
        RawIter::new(&self.root, K::BITS)
    }

    /// Gets an iterator over the raw keys of the dictionary, in sorted order.
    /// The iterator element type is `Result<CellBuilder<C>>`.
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
    pub fn raw_keys(&'_ self) -> RawKeys<'_, C> {
        RawKeys::new(&self.root, K::BITS)
    }
}

impl<C, K, V> Dict<C, K, V>
where
    for<'c> C: CellFamily + 'c,
    K: DictKey,
{
    /// Gets an iterator over the raw values of the dictionary, in order by key.
    /// The iterator element type is `Result<CellSlice<C>>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn raw_values(&'_ self) -> RawValues<'_, C> {
        RawValues::new(&self.root, K::BITS)
    }
}

impl<C, K, V> Dict<C, K, V>
where
    for<'c> C: CellFamily + 'c,
    K: Store<C> + DictKey,
    V: Store<C>,
{
    /// Sets the value associated with the key in the dictionary.
    pub fn set_ext<Q, T>(
        &mut self,
        key: Q,
        value: T,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Result<(), Error>
    where
        Q: Borrow<K>,
        T: Borrow<V>,
    {
        self.insert_impl(key.borrow(), value.borrow(), SetMode::Set, finalizer)
    }

    /// Sets the value associated with the key in the dictionary
    /// only if the key was already present in it.
    pub fn replace_ext<Q, T>(
        &mut self,
        key: Q,
        value: T,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Result<(), Error>
    where
        Q: Borrow<K>,
        T: Borrow<V>,
    {
        self.insert_impl(key.borrow(), value.borrow(), SetMode::Replace, finalizer)
    }

    /// Sets the value associated with key in dictionary,
    /// but only if it is not already present.
    pub fn add_ext<Q, T>(
        &mut self,
        key: Q,
        value: T,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Result<(), Error>
    where
        Q: Borrow<K>,
        T: Borrow<V>,
    {
        self.insert_impl(key.borrow(), value.borrow(), SetMode::Add, finalizer)
    }

    fn insert_impl(
        &mut self,
        key: &K,
        value: &V,
        mode: SetMode,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Result<(), Error>
    where
        for<'c> C: CellFamily + 'c,
        K: Store<C> + DictKey,
        V: Store<C>,
    {
        let key = ok!(serialize_entry(key, finalizer));
        let value = ok!(serialize_entry(value, finalizer));
        self.root = ok!(dict_insert(
            &self.root,
            &mut key.as_ref().as_slice(),
            K::BITS,
            &value.as_ref().as_slice(),
            mode,
            finalizer
        ));
        Ok(())
    }
}

/// An iterator over the entries of a [`Dict`].
///
/// This struct is created by the [`iter`] method on [`Dict`]. See its documentation for more.
///
/// [`iter`]: Dict::iter
pub struct Iter<'a, C: CellFamily, K, V> {
    inner: RawIter<'a, C>,
    _key: PhantomData<K>,
    _value: PhantomData<V>,
}

impl<C: CellFamily, K, V> Clone for Iter<'_, C, K, V> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            _key: PhantomData,
            _value: PhantomData,
        }
    }
}

impl<'a, C: CellFamily, K, V> Iter<'a, C, K, V>
where
    K: DictKey,
{
    /// Creates an iterator over the entries of a dictionary.
    pub fn new(root: &'a Option<CellContainer<C>>) -> Self {
        Self {
            inner: RawIter::new(root, K::BITS),
            _key: PhantomData,
            _value: PhantomData,
        }
    }
}

impl<'a, C, K, V> Iterator for Iter<'a, C, K, V>
where
    for<'c> C: DefaultFinalizer + 'c,
    K: DictKey,
    V: Load<'a, C>,
{
    type Item = Result<(K, V), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.inner.next()? {
            Ok((key, mut value)) => {
                if let Some(key) = K::from_raw_data(key.raw_data()) {
                    if let Some(value) = V::load_from(&mut value) {
                        return Some(Ok((key, value)));
                    }
                }
                Err(self.inner.finish(Error::CellUnderflow))
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
pub struct Keys<'a, C: CellFamily, K> {
    inner: RawIter<'a, C>,
    _key: PhantomData<K>,
}

impl<'a, C: CellFamily, K> Clone for Keys<'a, C, K> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            _key: PhantomData,
        }
    }
}

impl<'a, C: CellFamily, K> Keys<'a, C, K>
where
    K: DictKey,
{
    /// Creates an iterator over the keys of a dictionary.
    pub fn new(root: &'a Option<CellContainer<C>>) -> Self {
        Self {
            inner: RawIter::new(root, K::BITS),
            _key: PhantomData,
        }
    }
}

impl<'a, C, K> Iterator for Keys<'a, C, K>
where
    for<'c> C: DefaultFinalizer + 'c,
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
pub struct Values<'a, C: CellFamily, V> {
    inner: RawValues<'a, C>,
    _value: PhantomData<V>,
}

impl<C: CellFamily, V> Clone for Values<'_, C, V> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            _value: PhantomData,
        }
    }
}

impl<'a, C: CellFamily, V> Values<'a, C, V> {
    /// Creates an iterator over the values of a dictionary.
    pub fn new(root: &'a Option<CellContainer<C>>, bit_len: u16) -> Self {
        Self {
            inner: RawValues::new(root, bit_len),
            _value: PhantomData,
        }
    }
}

impl<'a, C, V> Iterator for Values<'a, C, V>
where
    for<'c> C: CellFamily + 'c,
    V: Load<'a, C>,
{
    type Item = Result<V, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next()? {
            Ok(mut value) => match V::load_from(&mut value) {
                Some(value) => Some(Ok(value)),
                None => Some(Err(self.inner.finish(Error::CellUnderflow))),
            },
            Err(e) => Some(Err(e)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{RcBoc, RcCellFamily};

    #[test]
    fn dict_set() {
        let mut dict = Dict::<RcCellFamily, u32, u16>::new();
        dict.set(123, 0xffff).unwrap();
        assert_eq!(dict.get(123).unwrap(), Some(0xffff));

        dict.set(123, 0xcafe).unwrap();
        assert_eq!(dict.get(123).unwrap(), Some(0xcafe));
    }

    #[test]
    #[cfg_attr(miri, ignore)] // takes too long to execute on miri
    fn dict_set_complex() {
        let mut dict = Dict::<RcCellFamily, u32, bool>::new();
        for i in 0..520 {
            dict.set(i, true).unwrap();
        }
    }

    #[test]
    fn dict_replace() {
        let mut dict = Dict::<RcCellFamily, u32, bool>::new();
        dict.replace(123, false).unwrap();
        assert!(!dict.contains_key(123).unwrap());

        dict.set(123, false).unwrap();
        assert_eq!(dict.get(123).unwrap(), Some(false));
        dict.replace(123, true).unwrap();
        assert_eq!(dict.get(123).unwrap(), Some(true));
    }

    #[test]
    fn dict_add() {
        let mut dict = Dict::<RcCellFamily, u32, bool>::new();

        dict.add(123, false).unwrap();
        assert_eq!(dict.get(123).unwrap(), Some(false));

        dict.add(123, true).unwrap();
        assert_eq!(dict.get(123).unwrap(), Some(false));
    }

    #[test]
    fn dict_iter() {
        let boc = RcBoc::decode_base64("te6ccgEBFAEAeAABAcABAgPOQAUCAgHUBAMACQAAAI3gAAkAAACjoAIBIA0GAgEgCgcCASAJCAAJAAAAciAACQAAAIfgAgEgDAsACQAAAFZgAAkAAABsIAIBIBEOAgEgEA8ACQAAADqgAAkAAABQYAIBIBMSAAkAAAAe4AAJAAAAv2A=").unwrap();
        let dict = boc.parse::<Dict<_, u32, u32>>().unwrap();

        let size = dict.values().count();
        assert_eq!(size, 10);

        for (i, entry) in dict.iter().enumerate() {
            let (key, _) = entry.unwrap();
            assert_eq!(key, i as u32);
        }
    }

    #[test]
    fn big_dict() {
        use rand::{Rng, SeedableRng};

        let mut rng = rand_xorshift::XorShiftRng::from_seed([0u8; 16]);

        let values = (0..100000)
            .map(|_| (rng.gen::<u32>(), rng.gen::<u64>()))
            .collect::<Vec<_>>();

        let mut result = Dict::<RcCellFamily, u32, u64>::new();
        for (key, value) in &values {
            result.set(key, value).unwrap();
        }
    }
}
