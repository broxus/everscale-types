use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::marker::PhantomData;

use super::raw::*;
use super::typed::*;
use super::{
    aug_dict_find_by_extra, aug_dict_insert, aug_dict_remove_owned,
    build_aug_dict_from_sorted_iter, read_label, DictKey, SearchByExtra, SetMode,
};
use crate::cell::*;
use crate::error::*;
use crate::util::*;

/// A trait for values that can be used as augmented values in an augmented dictionary.
pub trait AugDictExtra: Default {
    /// Merges two augmented values.
    ///
    /// # Parameters
    /// - `left` - The left branch (should start with `extra`).
    /// - `right` - The right branch (should start with `extra`).
    /// - `b` - The builder to store the result (only `extra`).
    /// - `cx` - The cell context.
    fn comp_add(
        left: &mut CellSlice,
        right: &mut CellSlice,
        b: &mut CellBuilder,
        cx: &dyn CellContext,
    ) -> Result<(), Error>;
}

/// Typed augmented dictionary with fixed length keys.
///
/// # TLB scheme
///
/// ```text
/// ahm_edge#_ {n:#} {V:Type} {A:Type} {l:#} {m:#}
///   label:(HmLabel ~l n) {n = (~m) + l}
///   node:(HashmapAugNode m V A) = HashmapAug n V A;
///
/// ahmn_leaf#_ {V:Type} {A:Type} extra:A value:V = HashmapAugNode 0 V A;
/// ahmn_fork#_ {n:#} {V:Type} {A:Type} left:^(HashmapAug n V A)
///   right:^(HashmapAug n V A) extra:A = HashmapAugNode (n + 1) V A;
///
/// ahme_empty$0 {n:#} {V:Type} {A:Type} extra:A = HashmapAugE n V A;
/// ahme_root$1 {n:#} {V:Type} {A:Type} root:^(HashmapAug n V A) extra:A = HashmapAugE n V A;
/// ```
pub struct AugDict<K, A, V> {
    dict: Dict<K, (A, V)>,
    extra: A,
    _key: PhantomData<K>,
    _value: PhantomData<(A, V)>,
}

impl<K, A: ExactSize, V> ExactSize for AugDict<K, A, V> {
    #[inline]
    fn exact_size(&self) -> Size {
        self.dict.exact_size() + self.extra.exact_size()
    }
}

impl<'a, K, A: Load<'a>, V> Load<'a> for AugDict<K, A, V> {
    #[inline]
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        Ok(Self {
            dict: ok!(Dict::load_from(slice)),
            extra: ok!(A::load_from(slice)),
            _key: PhantomData,
            _value: PhantomData,
        })
    }
}

impl<K, A: Store, V> Store for AugDict<K, A, V> {
    #[inline]
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        ok!(self.dict.store_into(builder, context));
        self.extra.store_into(builder, context)
    }
}

impl<K, A: Default, V> Default for AugDict<K, A, V> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<K, A: Clone, V> Clone for AugDict<K, A, V> {
    fn clone(&self) -> Self {
        Self {
            dict: self.dict.clone(),
            extra: self.extra.clone(),
            _key: PhantomData,
            _value: PhantomData,
        }
    }
}

impl<K, A: Eq, V> Eq for AugDict<K, A, V> {}

impl<K, A: PartialEq, V> PartialEq for AugDict<K, A, V> {
    fn eq(&self, other: &Self) -> bool {
        self.dict.eq(&other.dict) && self.extra.eq(&other.extra)
    }
}

impl<K, A: std::fmt::Debug, V> std::fmt::Debug for AugDict<K, A, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        debug_struct_field2_finish(f, "AugDict", "dict", &self.dict, "extra", &self.extra)
    }
}

impl<K, A: Default, V> AugDict<K, A, V> {
    /// Creates an empty dictionary
    pub fn new() -> Self {
        Self {
            dict: Dict::new(),
            extra: A::default(),
            _key: PhantomData,
            _value: PhantomData,
        }
    }

    /// Manually constructs the dictionaty from parts.
    pub const fn from_parts(dict: Dict<K, (A, V)>, extra: A) -> Self {
        Self {
            dict,
            extra,
            _key: PhantomData,
            _value: PhantomData,
        }
    }

    /// Returns an underlying dictionary and the extra value.
    pub fn into_parts(self) -> (Dict<K, (A, V)>, A) {
        (self.dict, self.extra)
    }

    /// Converts into a dictionary with an equivalent value type.
    #[inline]
    pub fn cast_into<Q, T>(self) -> AugDict<Q, A, T>
    where
        Q: EquivalentRepr<K>,
        (A, T): EquivalentRepr<(A, V)>,
    {
        AugDict {
            dict: self.dict.cast_into(),
            extra: self.extra,
            _key: PhantomData,
            _value: PhantomData,
        }
    }
}

impl<K: DictKey, A, V> AugDict<K, A, V> {
    /// Loads a non-empty dictionary from a root cell.
    pub fn load_from_root_ext<'a>(
        slice: &mut CellSlice<'a>,
        context: &dyn CellContext,
    ) -> Result<Self, Error>
    where
        A: Load<'a>,
        V: Load<'a>,
    {
        let (extra, root) = ok!(load_from_root::<A, V>(slice, K::BITS, context));

        Ok(Self {
            dict: Dict::from(Some(root)),
            extra,
            _key: PhantomData,
            _value: PhantomData,
        })
    }
}

impl<K, A, V> AugDict<K, A, V>
where
    K: DictKey,
    for<'a> A: Default + Load<'a>,
{
    /// Recomputes the root extra value.
    pub fn update_root_extra(&mut self) -> Result<(), Error> {
        self.extra = match &self.dict.root {
            Some(root) => {
                let slice = &mut ok!(root.as_slice());
                let prefix = ok!(read_label(slice, K::BITS));
                if prefix.size_bits() != K::BITS {
                    ok!(slice.skip_first(0, 2));
                }
                ok!(A::load_from(slice))
            }
            None => A::default(),
        };
        Ok(())
    }
}

fn load_from_root<'a, A, V>(
    slice: &mut CellSlice<'a>,
    key_bit_len: u16,
    context: &dyn CellContext,
) -> Result<(A, Cell), Error>
where
    A: Load<'a>,
    V: Load<'a>,
{
    let root = *slice;

    let label = ok!(read_label(slice, key_bit_len));
    let extra = if label.size_bits() != key_bit_len {
        ok!(slice.skip_first(0, 2));
        ok!(A::load_from(slice))
    } else {
        let extra = ok!(A::load_from(slice));
        ok!(V::load_from(slice));
        extra
    };

    let root_bits = root.size_bits() - slice.size_bits();
    let root_refs = root.size_refs() - slice.size_refs();

    let mut b = CellBuilder::new();
    ok!(b.store_slice(root.get_prefix(root_bits, root_refs)));
    match b.build_ext(context) {
        Ok(cell) => Ok((extra, cell)),
        Err(e) => Err(e),
    }
}

impl<K, A, V> AugDict<K, A, V> {
    /// Returns `true` if the dictionary contains no elements.
    pub const fn is_empty(&self) -> bool {
        self.dict.is_empty()
    }

    /// Returns the underlying dictionary.
    #[inline]
    pub const fn dict(&self) -> &Dict<K, (A, V)> {
        &self.dict
    }

    /// Returns the root augmented value.
    #[inline]
    pub const fn root_extra(&self) -> &A {
        &self.extra
    }
}

impl<K, A, V> AugDict<K, A, V>
where
    K: Store + DictKey,
{
    /// Returns `true` if the dictionary contains a value for the specified key.
    pub fn contains_key<Q>(&self, key: Q) -> Result<bool, Error>
    where
        Q: Borrow<K>,
    {
        self.dict.contains_key(key)
    }
}

impl<K, A, V> AugDict<K, A, V>
where
    K: Store + DictKey,
{
    /// Returns the value corresponding to the key.
    pub fn get<'a: 'b, 'b, Q>(&'a self, key: Q) -> Result<Option<(A, V)>, Error>
    where
        Q: Borrow<K> + 'b,
        (A, V): Load<'a>,
    {
        self.dict.get(key)
    }
}

impl<K, A, V> AugDict<K, A, V>
where
    K: DictKey,
{
    /// Searches for an item using a predicate on extra values.
    ///
    /// Used as a secondary index.
    pub fn find_by_extra<'a, S>(&'a self, flow: S) -> Result<Option<(K, A, V)>, Error>
    where
        S: SearchByExtra<A>,
        A: Load<'a>,
        V: Load<'a>,
    {
        let Some((key, extra, mut value)) = ok!(aug_dict_find_by_extra::<A, S>(
            self.dict.root.as_ref(),
            K::BITS,
            flow
        )) else {
            return Ok(None);
        };

        let Some(key) = K::from_raw_data(key.raw_data()) else {
            return Err(Error::CellUnderflow);
        };
        let value = ok!(V::load_from(&mut value));
        Ok(Some((key, extra, value)))
    }
}

impl<K, A, V> AugDict<K, A, V>
where
    K: Store + DictKey,
    for<'a> A: AugDictExtra + Store + Load<'a>,
    V: Store,
{
    /// Builds a dictionary from a sorted collection.
    pub fn try_from_btree<Q, E, T>(sorted: &BTreeMap<Q, (E, T)>) -> Result<Self, Error>
    where
        Q: Borrow<K>,
        E: Borrow<A>,
        T: Borrow<V>,
        K: Ord,
    {
        let root = ok!(build_aug_dict_from_sorted_iter(
            sorted
                .iter()
                .map(|(k, (a, v))| (k.borrow(), a.borrow(), v.borrow())),
            K::BITS,
            A::comp_add,
            Cell::empty_context()
        ));

        let mut result = Self {
            dict: Dict::from_raw(root),
            extra: A::default(),
            _key: PhantomData,
            _value: PhantomData,
        };
        ok!(result.update_root_extra());
        Ok(result)
    }

    /// Builds a dictionary from a sorted slice.
    pub fn try_from_sorted_slice<Q, E, T>(sorted: &[(Q, E, T)]) -> Result<Self, Error>
    where
        Q: Borrow<K>,
        E: Borrow<A>,
        T: Borrow<V>,
        K: Ord,
    {
        let root = ok!(build_aug_dict_from_sorted_iter(
            sorted
                .iter()
                .map(|(k, a, v)| (k.borrow(), a.borrow(), v.borrow())),
            K::BITS,
            A::comp_add,
            Cell::empty_context()
        ));

        let mut result = Self {
            dict: Dict::from_raw(root),
            extra: A::default(),
            _key: PhantomData,
            _value: PhantomData,
        };
        ok!(result.update_root_extra());
        Ok(result)
    }

    /// Sets the augmented value associated with the key in the aug dictionary.
    ///
    /// Use [`set_ext`] if you need to use a custom cell context.
    ///
    /// [`set_ext`]: AugDict::set_ext
    pub fn set<Q, E, T>(&mut self, key: Q, aug: E, value: T) -> Result<bool, Error>
    where
        Q: Borrow<K>,
        E: Borrow<A>,
        T: Borrow<V>,
    {
        self.set_ext(key, aug, value, Cell::empty_context())
    }

    /// Sets the value associated with the key in the dictionary.
    pub fn set_ext<Q, E, T>(
        &mut self,
        key: Q,
        aug: E,
        value: T,
        context: &dyn CellContext,
    ) -> Result<bool, Error>
    where
        Q: Borrow<K>,
        E: Borrow<A>,
        T: Borrow<V>,
    {
        self.insert_impl(
            key.borrow(),
            aug.borrow(),
            value.borrow(),
            SetMode::Set,
            context,
        )
    }

    /// Sets the augmented value associated with the key in the aug dictionary
    /// only if the key was already present in it.
    ///
    /// Use [`replace_ext`] if you need to use a custom cell context.
    ///
    /// [`replace_ext`]: AugDict::replace_ext
    pub fn replace<Q, E, T>(&mut self, key: Q, aug: E, value: T) -> Result<bool, Error>
    where
        Q: Borrow<K>,
        E: Borrow<A>,
        T: Borrow<V>,
    {
        self.replace_ext(key, aug, value, Cell::empty_context())
    }

    /// Sets the value associated with the key in the dictionary
    /// only if the key was already present in it.
    pub fn replace_ext<Q, E, T>(
        &mut self,
        key: Q,
        aug: E,
        value: T,
        context: &dyn CellContext,
    ) -> Result<bool, Error>
    where
        Q: Borrow<K>,
        E: Borrow<A>,
        T: Borrow<V>,
    {
        self.insert_impl(
            key.borrow(),
            aug.borrow(),
            value.borrow(),
            SetMode::Replace,
            context,
        )
    }

    /// Sets the value associated with key in aug dictionary,
    /// but only if it is not already present.
    ///
    /// Use [`add_ext`] if you need to use a custom cell context.
    ///
    /// [`add_ext`]: AugDict::add_ext
    pub fn add<Q, E, T>(&mut self, key: Q, aug: E, value: T) -> Result<bool, Error>
    where
        Q: Borrow<K>,
        E: Borrow<A>,
        T: Borrow<V>,
    {
        self.add_ext(key, aug, value, Cell::empty_context())
    }

    /// Sets the value associated with key in dictionary,
    /// but only if it is not already present.
    pub fn add_ext<Q, E, T>(
        &mut self,
        key: Q,
        aug: E,
        value: T,
        context: &dyn CellContext,
    ) -> Result<bool, Error>
    where
        Q: Borrow<K>,
        E: Borrow<A>,
        T: Borrow<V>,
    {
        self.insert_impl(
            key.borrow(),
            aug.borrow(),
            value.borrow(),
            SetMode::Add,
            context,
        )
    }

    /// Removes the value associated with key in aug dictionary.
    /// Returns an optional removed value as cell slice parts.
    pub fn remove<Q>(&mut self, key: Q) -> Result<Option<(A, V)>, Error>
    where
        Q: Borrow<K>,
        for<'a> A: Load<'a> + 'static,
        for<'a> V: Load<'a> + 'static,
    {
        match ok!(self.remove_raw_ext(key, Cell::empty_context())) {
            Some((cell, range)) => {
                let mut slice = ok!(range.apply(&cell));
                let extra = ok!(A::load_from(&mut slice));
                let value = ok!(V::load_from(&mut slice));
                Ok(Some((extra, value)))
            }
            None => Ok(None),
        }
    }

    /// Removes the value associated with key in dictionary.
    /// Returns an optional removed value as cell slice parts.
    pub fn remove_raw_ext<Q>(
        &mut self,
        key: Q,
        context: &dyn CellContext,
    ) -> Result<Option<CellSliceParts>, Error>
    where
        Q: Borrow<K>,
    {
        self.remove_impl(key.borrow(), context)
    }

    fn insert_impl(
        &mut self,
        key: &K,
        extra: &A,
        value: &V,
        mode: SetMode,
        context: &dyn CellContext,
    ) -> Result<bool, Error> {
        let mut key_builder = CellBuilder::new();
        ok!(key.store_into(&mut key_builder, Cell::empty_context()));
        let inserted = ok!(aug_dict_insert(
            &mut self.dict.root,
            &mut key_builder.as_data_slice(),
            K::BITS,
            extra,
            value,
            mode,
            A::comp_add,
            context,
        ));

        if inserted {
            ok!(self.update_root_extra());
        }

        Ok(inserted)
    }

    fn remove_impl(
        &mut self,
        key: &K,
        context: &dyn CellContext,
    ) -> Result<Option<(Cell, CellSliceRange)>, Error> {
        let mut key_builder = CellBuilder::new();
        ok!(key.store_into(&mut key_builder, Cell::empty_context()));
        let res = ok!(aug_dict_remove_owned(
            &mut self.dict.root,
            &mut key_builder.as_data_slice(),
            K::BITS,
            false,
            A::comp_add,
            context,
        ));

        if res.is_some() {
            ok!(self.update_root_extra());
        }

        Ok(res)
    }

    /// Split dictionary into 2 dictionaries by the first key bit.
    pub fn split(&self) -> Result<(Self, Self), Error> {
        self.split_by_prefix_ext(&Default::default(), Cell::empty_context())
    }

    /// Split dictionary into 2 dictionaries by the first key bit.
    pub fn split_ext(&self, context: &dyn CellContext) -> Result<(Self, Self), Error> {
        self.split_by_prefix_ext(&Default::default(), context)
    }

    /// Split dictionary into 2 dictionaries at the prefix.
    pub fn split_by_prefix(&self, key_prefix: &CellSlice<'_>) -> Result<(Self, Self), Error> {
        self.split_by_prefix_ext(key_prefix, Cell::empty_context())
    }

    /// Split dictionary into 2 dictionaries at the prefix.
    pub fn split_by_prefix_ext(
        &self,
        key_prefix: &CellSlice<'_>,
        context: &dyn CellContext,
    ) -> Result<(Self, Self), Error> {
        let (left, right) = ok!(self.dict.split_by_prefix_ext(key_prefix, context));

        let mut left = Self {
            dict: left,
            extra: A::default(),
            _key: PhantomData,
            _value: PhantomData,
        };
        ok!(left.update_root_extra());

        let mut right = Self {
            dict: right,
            extra: A::default(),
            _key: PhantomData,
            _value: PhantomData,
        };
        ok!(right.update_root_extra());

        Ok((left, right))
    }
}

impl<K, A, V> AugDict<K, A, V>
where
    K: DictKey,
{
    /// Gets an iterator over the entries of the dictionary, sorted by key.
    /// The iterator element type is `Result<(K, A, V)>`.
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
    pub fn iter<'a>(&'a self) -> AugIter<'a, K, A, V>
    where
        V: Load<'a>,
    {
        AugIter::new(self.dict.root())
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
        Keys::new(self.dict.root())
    }
}

impl<K, A, V> AugDict<K, A, V>
where
    K: DictKey,
{
    /// Gets an iterator over the augmented values of the dictionary, in order by key.
    /// The iterator element type is `Result<V>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn values<'a>(&'a self) -> Values<'a, (A, V)>
    where
        V: Load<'a>,
    {
        Values::new(self.dict.root(), K::BITS)
    }
}

impl<K, A, V> AugDict<K, A, V>
where
    K: Store + DictKey,
{
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
    /// [`values`]: AugDict::values
    /// [`raw_values`]: AugDict::raw_values
    pub fn raw_iter(&'_ self) -> RawIter<'_> {
        RawIter::new(self.dict.root(), K::BITS)
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
    /// [`values`]: AugDict::values
    /// [`raw_values`]: AugDict::raw_values
    pub fn raw_keys(&'_ self) -> RawKeys<'_> {
        RawKeys::new(self.dict.root(), K::BITS)
    }
}

impl<K, A, V> AugDict<K, A, V>
where
    K: DictKey,
{
    /// Gets an iterator over the raw values of the dictionary, in order by key.
    /// The iterator element type is `Result<CellSlice>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn raw_values(&'_ self) -> RawValues<'_> {
        RawValues::new(self.dict.root(), K::BITS)
    }
}

#[cfg(feature = "serde")]
impl<K, A, V> serde::Serialize for AugDict<K, A, V>
where
    K: serde::Serialize + Store + DictKey,
    for<'a> A: serde::Serialize + Store + Load<'a>,
    for<'a> V: serde::Serialize + Load<'a>,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::{Error, SerializeMap};

        #[derive(serde::Serialize)]
        struct AugDictHelper<'a, K, A, V>
        where
            K: serde::Serialize + Store + DictKey,
            A: serde::Serialize + Store + Load<'a>,
            V: serde::Serialize + Load<'a>,
        {
            #[serde(serialize_with = "serialize_dict_entries")]
            entires: &'a AugDict<K, A, V>,
            extra: &'a A,
        }

        fn serialize_dict_entries<'a, K, A, V, S>(
            dict: &'a AugDict<K, A, V>,
            serializer: S,
        ) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
            K: serde::Serialize + Store + DictKey,
            A: serde::Serialize + Store + Load<'a>,
            V: serde::Serialize + Load<'a>,
        {
            let mut ser = serializer.serialize_map(None)?;
            for ref entry in dict.iter() {
                let (key, extra, value) = match entry {
                    Ok(entry) => entry,
                    Err(e) => return Err(Error::custom(e)),
                };
                ok!(ser.serialize_entry(key, &(extra, value)));
            }
            ser.end()
        }

        if serializer.is_human_readable() {
            AugDictHelper {
                entires: self,
                extra: &self.extra,
            }
            .serialize(serializer)
        } else {
            crate::boc::BocRepr::serialize(self, serializer)
        }
    }
}

/// An iterator over the entries of an [`AugDict`].
///
/// This struct is created by the [`iter`] method on [`AugDict`]. See its documentation for more.
///
/// [`iter`]: AugDict::iter
pub struct AugIter<'a, K, A, V> {
    inner: Iter<'a, K, (A, V)>,
}

impl<K, A, V> Clone for AugIter<'_, K, A, V> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K, A, V> AugIter<'a, K, A, V>
where
    K: DictKey,
{
    /// Creates an iterator over the entries of a dictionary.
    pub fn new(root: &'a Option<Cell>) -> Self {
        Self {
            inner: Iter::new(root),
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

impl<'a, K, A, V> Iterator for AugIter<'a, K, A, V>
where
    K: DictKey,
    (A, V): Load<'a>,
{
    type Item = Result<(K, A, V), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next()? {
            Ok((key, (aug, value))) => Some(Ok((key, aug, value))),
            Err(e) => Some(Err(e)),
        }
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Context;

    use super::*;

    #[derive(Debug, Default, Load, Store, Eq, PartialEq)]
    struct OrCmp(bool);

    impl AugDictExtra for OrCmp {
        fn comp_add(
            left: &mut CellSlice,
            right: &mut CellSlice,
            b: &mut CellBuilder,
            _: &dyn CellContext,
        ) -> Result<(), Error> {
            let left = left.load_bit()?;
            let right = right.load_bit()?;
            b.store_bit(left | right)
        }
    }

    #[derive(Debug, Default, Load, Store, Eq, PartialEq)]
    struct SomeValue(u32);

    impl AugDictExtra for SomeValue {
        fn comp_add(
            left: &mut CellSlice,
            right: &mut CellSlice,
            b: &mut CellBuilder,
            _: &dyn CellContext,
        ) -> Result<(), Error> {
            let left = left.load_u32()?;
            let right = right.load_u32()?;
            b.store_u32(left.saturating_add(right))
        }
    }

    impl rand::distributions::Distribution<SomeValue> for rand::distributions::Standard {
        #[inline]
        fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> SomeValue {
            SomeValue(rand::distributions::Standard.sample(rng))
        }
    }

    #[test]
    fn dict_set() {
        let mut dict = AugDict::<u32, OrCmp, u16>::new();
        assert_eq!(*dict.root_extra(), OrCmp(false));

        dict.set(123, OrCmp(false), 0xffff).unwrap();
        assert_eq!(dict.get(123).unwrap(), Some((OrCmp(false), 0xffff)));
        assert_eq!(*dict.root_extra(), OrCmp(false));

        dict.set(123, OrCmp(true), 0xcafe).unwrap();
        assert_eq!(dict.get(123).unwrap(), Some((OrCmp(true), 0xcafe)));
        assert_eq!(*dict.root_extra(), OrCmp(true));
    }

    #[test]
    fn dict_set_complex() {
        let mut dict = AugDict::<u32, OrCmp, u32>::new();
        assert_eq!(*dict.root_extra(), OrCmp(false));

        for i in 0..520 {
            dict.set(i, OrCmp(true), 123).unwrap();
        }
        assert_eq!(*dict.root_extra(), OrCmp(true));
    }

    #[test]
    fn dict_replace() {
        let mut dict = AugDict::<u32, OrCmp, u16>::new();
        assert_eq!(*dict.root_extra(), OrCmp(false));
        dict.replace(123, OrCmp(false), 0xff).unwrap();
        assert!(!dict.contains_key(123).unwrap());
        assert_eq!(*dict.root_extra(), OrCmp(false));

        dict.set(123, OrCmp(false), 0xff).unwrap();
        assert_eq!(dict.get(123).unwrap(), Some((OrCmp(false), 0xff)));
        assert_eq!(*dict.root_extra(), OrCmp(false));

        dict.replace(123, OrCmp(true), 0xaa).unwrap();
        assert_eq!(dict.get(123).unwrap(), Some((OrCmp(true), 0xaa)));
        assert_eq!(*dict.root_extra(), OrCmp(true));
    }

    #[test]
    fn dict_add() {
        let mut dict = AugDict::<u32, OrCmp, u16>::new();
        assert_eq!(*dict.root_extra(), OrCmp(false));

        dict.add(123, OrCmp(false), 0x12).unwrap();
        assert_eq!(dict.get(123).unwrap(), Some((OrCmp(false), 0x12)));
        assert_eq!(*dict.root_extra(), OrCmp(false));

        dict.add(123, OrCmp(true), 0x11).unwrap();
        assert_eq!(dict.get(123).unwrap(), Some((OrCmp(false), 0x12)));
        assert_eq!(*dict.root_extra(), OrCmp(false));
    }

    #[test]
    fn dict_remove() {
        let mut dict = AugDict::<u32, OrCmp, u32>::new();
        assert_eq!(*dict.root_extra(), OrCmp(false));

        for i in 0..10 {
            assert!(dict.set(i, OrCmp(i % 2 == 0), i).unwrap());
        }
        assert_eq!(*dict.root_extra(), OrCmp(true));

        let mut check_remove = |n: u32, expected: Option<(OrCmp, u32)>| -> anyhow::Result<()> {
            let removed = dict.remove(n).context("Failed to remove")?;
            anyhow::ensure!(removed == expected);
            Ok(())
        };

        check_remove(0, Some((OrCmp(true), 0))).unwrap();

        check_remove(4, Some((OrCmp(true), 4))).unwrap();

        check_remove(9, Some((OrCmp(false), 9))).unwrap();
        check_remove(9, None).unwrap();

        check_remove(5, Some((OrCmp(false), 5))).unwrap();
        check_remove(5, None).unwrap();

        check_remove(100, None).unwrap();

        check_remove(1, Some((OrCmp(false), 1))).unwrap();
        check_remove(2, Some((OrCmp(true), 2))).unwrap();
        check_remove(3, Some((OrCmp(false), 3))).unwrap();
        check_remove(6, Some((OrCmp(true), 6))).unwrap();
        check_remove(7, Some((OrCmp(false), 7))).unwrap();
        check_remove(8, Some((OrCmp(true), 8))).unwrap();

        assert!(dict.is_empty());
    }

    #[test]
    fn dict_iter() {
        let mut dict = AugDict::<u32, SomeValue, u32>::new();
        assert_eq!(*dict.root_extra(), SomeValue(0));

        let mut expected_extra = 0;
        for i in 0..10 {
            expected_extra += i;
            dict.set(i, SomeValue(i), 9 - i).unwrap();
        }
        assert_eq!(*dict.root_extra(), SomeValue(expected_extra));

        let size = dict.values().count();
        assert_eq!(size, 10);

        for (i, entry) in dict.iter().enumerate() {
            let (key, aug, value) = entry.unwrap();
            assert_eq!(SomeValue(key), aug);
            assert_eq!(key, i as u32);
            assert_eq!(value, 9 - i as u32);
        }
    }

    #[cfg(feature = "models")]
    #[test]
    fn aug_test() {
        use crate::models::{AccountBlock, CurrencyCollection};
        use crate::prelude::Boc;

        let boc = Boc::decode(include_bytes!("./tests/account_blocks_aug_dict.boc")).unwrap();

        let original_dict = boc
            .parse::<AugDict<HashBytes, CurrencyCollection, AccountBlock>>()
            .unwrap();

        let mut data = Vec::new();
        for entry in original_dict.iter() {
            data.push(entry.unwrap());
        }
        data.reverse();

        let mut new_dict: AugDict<HashBytes, CurrencyCollection, AccountBlock> = AugDict::new();
        for (key, aug, value) in data.iter() {
            new_dict.add(key, aug, value).unwrap();
        }
        assert_eq!(new_dict.root_extra(), original_dict.root_extra());

        let serialized = CellBuilder::build_from(&new_dict).unwrap();
        assert_eq!(serialized.repr_hash(), boc.repr_hash());

        for (key, _, _) in data.iter() {
            new_dict.remove(key).unwrap();
        }
        assert!(new_dict.is_empty());
        assert_eq!(new_dict.root_extra(), &CurrencyCollection::ZERO);
    }

    #[test]
    fn build_from_array() {
        for entries in [
            &[
                (0u32, SomeValue(123), 1u32),
                (1, SomeValue(10), 2),
                (2, SomeValue(20), 4),
                (2, SomeValue(20), 3),
                (3, SomeValue(40), 4),
                (4, SomeValue(50), 5),
            ][..],
            &[
                (534837844, SomeValue(331123), 3117028142),
                (1421713188, SomeValue(5345345), 3155891450),
                (1526242096, SomeValue(567567), 2789399854),
                (1971086295, SomeValue(5345), 1228713494),
                (4258889371, SomeValue(4956495), 3256452222),
            ],
        ] {
            let result = AugDict::<u32, SomeValue, u32>::try_from_sorted_slice(entries).unwrap();

            let mut dict = AugDict::<u32, SomeValue, u32>::new();
            for (k, a, v) in entries {
                dict.add(k, a, v).unwrap();
            }

            println!("{}", result.dict.root.as_ref().unwrap().display_tree());
            println!(
                "BOC: {}",
                crate::boc::BocRepr::encode_base64(&result).unwrap()
            );

            assert_eq!(result, dict);
        }
    }

    #[test]
    fn build_from_any_array() {
        for _ in 0..100 {
            let n = 1 + rand::random::<usize>() % 1000;
            let mut entries = (0..n)
                .map(|_| {
                    (
                        rand::random::<u32>(),
                        rand::random::<SomeValue>(),
                        rand::random::<u32>(),
                    )
                })
                .collect::<Vec<_>>();
            entries.sort_by_key(|(k, _, _)| *k);

            let built_from_dict =
                AugDict::<u32, SomeValue, u32>::try_from_sorted_slice(&entries).unwrap();

            let mut dict = AugDict::<u32, SomeValue, u32>::new();
            for (k, a, v) in entries {
                dict.add(k, a, v).unwrap();
            }

            // println!("{}", built_from_dict.as_ref().unwrap().display_tree());

            assert_eq!(built_from_dict, dict);
        }
    }

    #[test]
    fn search_by_lt() {
        #[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Store, Load)]
        struct MaxValue(u64);

        impl AugDictExtra for MaxValue {
            fn comp_add(
                left: &mut CellSlice,
                right: &mut CellSlice,
                b: &mut CellBuilder,
                _: &dyn CellContext,
            ) -> Result<(), Error> {
                let left = left.load_u64()?;
                let right = right.load_u64()?;
                b.store_u64(left.max(right))
            }
        }

        let mut items = AugDict::<u32, MaxValue, u32>::new();
        items.set(0, MaxValue(100), 123).unwrap();
        items.set(2, MaxValue(150), 234).unwrap();
        items.set(4, MaxValue(200), 345).unwrap();
        items.set(6, MaxValue(350), 456).unwrap();
        items.set(7, MaxValue(300), 567).unwrap();
        items.set(8, MaxValue(250), 678).unwrap();

        // Search by ordering
        let highest = items.find_by_extra(std::cmp::Ordering::Greater).unwrap();
        assert_eq!(highest, Some((6, MaxValue(350), 456)));
    }
}
