use std::borrow::Borrow;
use std::marker::PhantomData;

use crate::cell::*;
use crate::error::*;
use crate::util::*;

use super::raw::*;
use super::typed::*;
use super::{read_label, DictKey};

pub(crate) trait AugDictSkipValue<'a, C: CellFamily> {
    fn skip_value(slice: &mut CellSlice<'a, C>) -> bool;
}

impl<'a, C: CellFamily> AugDictSkipValue<'a, C> for crate::num::Tokens {
    #[inline]
    fn skip_value(slice: &mut CellSlice<'a, C>) -> bool {
        if let Some(token_bytes) = slice.load_small_uint(4) {
            slice.try_advance(8 * token_bytes as u16, 0)
        } else {
            false
        }
    }
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
pub struct AugDict<C: CellFamily, K, A, V> {
    dict: Dict<C, K, (A, V)>,
    extra: A,
    _key: PhantomData<K>,
    _value: PhantomData<(A, V)>,
}

impl<'a, C: CellFamily, K, A: Load<'a, C>, V> Load<'a, C> for AugDict<C, K, A, V> {
    #[inline]
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            dict: Dict::load_from(slice)?,
            extra: A::load_from(slice)?,
            _key: PhantomData,
            _value: PhantomData,
        })
    }
}

impl<C: CellFamily, K, A: Store<C>, V> Store<C> for AugDict<C, K, A, V> {
    #[inline]
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.dict.store_into(builder, finalizer) && self.extra.store_into(builder, finalizer)
    }
}

impl<C: CellFamily, K, A: Default, V> Default for AugDict<C, K, A, V> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<C: CellFamily, K, A: Clone, V> Clone for AugDict<C, K, A, V> {
    fn clone(&self) -> Self {
        Self {
            dict: self.dict.clone(),
            extra: self.extra.clone(),
            _key: PhantomData,
            _value: PhantomData,
        }
    }
}

impl<C: CellFamily, K, A: Eq, V> Eq for AugDict<C, K, A, V> {}

impl<C: CellFamily, K, A: PartialEq, V> PartialEq for AugDict<C, K, A, V> {
    fn eq(&self, other: &Self) -> bool {
        self.dict.eq(&other.dict) && self.extra.eq(&other.extra)
    }
}

impl<C: CellFamily, K, A: std::fmt::Debug, V> std::fmt::Debug for AugDict<C, K, A, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        debug_struct_field2_finish(f, "AugDict", "dict", &self.dict, "extra", &self.extra)
    }
}

impl<C: CellFamily, K, A: Default, V> AugDict<C, K, A, V> {
    /// Creates an empty dictionary
    pub fn new() -> Self {
        Self {
            dict: Dict::new(),
            extra: A::default(),
            _key: PhantomData,
            _value: PhantomData,
        }
    }
}

impl<C, K: DictKey, A, V> AugDict<C, K, A, V>
where
    for<'c> C: CellFamily + 'c,
{
    pub(crate) fn load_from_root<'a>(
        slice: &mut CellSlice<'a, C>,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Option<Self>
    where
        A: Load<'a, C>,
        V: AugDictSkipValue<'a, C>,
    {
        let (extra, root) = load_from_root::<C, A, V>(slice, K::BITS, finalizer)?;

        Some(Self {
            dict: Dict::from(Some(root)),
            extra,
            _key: PhantomData,
            _value: PhantomData,
        })
    }
}

fn load_from_root<'a, C, A, V>(
    slice: &mut CellSlice<'a, C>,
    key_bit_len: u16,
    finalizer: &mut dyn Finalizer<C>,
) -> Option<(A, CellContainer<C>)>
where
    for<'c> C: CellFamily + 'c,
    A: Load<'a, C>,
    V: AugDictSkipValue<'a, C>,
{
    let root = *slice;

    let label = read_label(slice, key_bit_len)?;
    let extra = if label.remaining_bits() != key_bit_len {
        if !slice.try_advance(0, 2) {
            return None;
        }
        A::load_from(slice)?
    } else {
        let extra = A::load_from(slice)?;
        if !V::skip_value(slice) {
            return None;
        }
        extra
    };

    let root_bits = root.remaining_bits() - slice.remaining_bits();
    let root_refs = root.remaining_refs() - slice.remaining_refs();

    let mut builder = CellBuilder::<C>::new();
    if builder.store_slice(root.get_prefix(root_bits, root_refs)) {
        Some((extra, builder.build_ext(finalizer)?))
    } else {
        None
    }
}

impl<C: CellFamily, K, A, V> AugDict<C, K, A, V> {
    /// Returns `true` if the dictionary contains no elements.
    pub const fn is_empty(&self) -> bool {
        self.dict.is_empty()
    }

    /// Returns the underlying dictionary.
    #[inline]
    pub const fn dict(&self) -> &Dict<C, K, (A, V)> {
        &self.dict
    }

    /// Returns the root augmented value.
    #[inline]
    pub const fn root_extra(&self) -> &A {
        &self.extra
    }
}

impl<C, K, A, V> AugDict<C, K, A, V>
where
    for<'c> C: DefaultFinalizer + 'c,
    K: Store<C> + DictKey,
{
    /// Returns `true` if the dictionary contains a value for the specified key.
    pub fn contains_key<Q>(&self, key: Q) -> Result<bool, Error>
    where
        Q: Borrow<K>,
    {
        self.dict.contains_key(key)
    }
}

impl<C, K, A, V> AugDict<C, K, A, V>
where
    for<'c> C: DefaultFinalizer + 'c,
    K: Store<C> + DictKey,
{
    /// Returns the value corresponding to the key.
    ///
    /// Key is serialized using the default finalizer.
    pub fn get<'a: 'b, 'b, Q>(&'a self, key: Q) -> Result<Option<(A, V)>, Error>
    where
        Q: Borrow<K> + 'b,
        (A, V): Load<'a, C>,
    {
        self.dict.get_ext(key, &mut C::default_finalizer())
    }
}

// TODO: add support for `extra` in edges

// impl<C, K, A, V> AugDict<C, K, A, V>
// where
//     for<'c> C: DefaultFinalizer + 'c,
//     K: Store<C> + DictKey,
//     A: Store<C>,
//     V: Store<C>,
// {
//     /// Sets the augmented value associated with the key in the dictionary.
//     ///
//     /// Use [`set_ext`] if you need to use a custom finalizer.
//     ///
//     /// [`set_ext`]: AugDict::set_ext
//     pub fn set<Q, E, T>(&mut self, key: Q, aug: E, value: T) -> Result<(), Error>
//     where
//         Q: Borrow<K>,
//         E: Borrow<A>,
//         T: Borrow<V>,
//     {
//         self.set_ext(key, aug, value, &mut C::default_finalizer())
//     }

//     /// Sets the augmented value associated with the key in the dictionary
//     /// only if the key was already present in it.
//     ///
//     /// Use [`replace_ext`] if you need to use a custom finalizer.
//     ///
//     /// [`replace_ext`]: AugDict::replace_ext
//     pub fn replace<Q, E, T>(&mut self, key: Q, aug: E, value: T) -> Result<(), Error>
//     where
//         Q: Borrow<K>,
//         E: Borrow<A>,
//         T: Borrow<V>,
//     {
//         self.replace_ext(key, aug, value, &mut C::default_finalizer())
//     }

//     /// Sets the value associated with key in dictionary,
//     /// but only if it is not already present.
//     ///
//     /// Use [`add_ext`] if you need to use a custom finalizer.
//     ///
//     /// [`add_ext`]: AugDict::add_ext
//     pub fn add<Q, E, T>(&mut self, key: Q, aug: E, value: T) -> Result<(), Error>
//     where
//         Q: Borrow<K>,
//         E: Borrow<A>,
//         T: Borrow<V>,
//     {
//         self.add_ext(key, aug, value, &mut C::default_finalizer())
//     }
// }

impl<C, K, A, V> AugDict<C, K, A, V>
where
    for<'c> C: DefaultFinalizer + 'c,
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
    pub fn iter<'a>(&'a self) -> AugIter<'_, C, K, A, V>
    where
        V: Load<'a, C>,
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
    pub fn keys(&'_ self) -> Keys<'_, C, K> {
        Keys::new(self.dict.root())
    }
}

impl<C, K, A, V> AugDict<C, K, A, V>
where
    for<'c> C: DefaultFinalizer + 'c,
    K: DictKey,
{
    /// Gets an iterator over the augmented values of the dictionary, in order by key.
    /// The iterator element type is `Result<V>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn values<'a>(&'a self) -> Values<'a, C, (A, V)>
    where
        V: Load<'a, C>,
    {
        Values::new(self.dict.root(), K::BITS)
    }
}

impl<C, K, A, V> AugDict<C, K, A, V>
where
    for<'c> C: CellFamily + 'c,
    K: Store<C> + DictKey,
{
    /// Returns the augmented value corresponding to the key.
    ///
    /// Key is serialized using the provided finalizer.
    pub fn get_ext<'a: 'b, 'b, Q>(
        &'a self,
        key: Q,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Result<Option<(A, V)>, Error>
    where
        Q: Borrow<K> + 'b,
        A: Load<'a, C>,
        V: Load<'a, C>,
    {
        self.dict.get_ext(key, finalizer)
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
    /// [`values`]: AugDict::values
    /// [`raw_values`]: AugDict::raw_values
    pub fn raw_iter(&'_ self) -> RawIter<'_, C> {
        RawIter::new(self.dict.root(), K::BITS)
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
    /// [`values`]: AugDict::values
    /// [`raw_values`]: AugDict::raw_values
    pub fn raw_keys(&'_ self) -> RawKeys<'_, C> {
        RawKeys::new(self.dict.root(), K::BITS)
    }
}

impl<C, K, A, V> AugDict<C, K, A, V>
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
        RawValues::new(self.dict.root(), K::BITS)
    }
}

// impl<C, K, A, V> AugDict<C, K, A, V>
// where
//     for<'c> C: CellFamily + 'c,
//     K: Store<C> + DictKey,
//     A: Store<C>,
//     V: Store<C>,
// {
//     /// Sets the value associated with the key in the dictionary.
//     pub fn set_ext<Q, E, T>(
//         &mut self,
//         key: Q,
//         aug: E,
//         value: T,
//         finalizer: &mut dyn Finalizer<C>,
//     ) -> Result<(), Error>
//     where
//         Q: Borrow<K>,
//         E: Borrow<A>,
//         T: Borrow<V>,
//     {
//         self.insert_impl(
//             key.borrow(),
//             aug.borrow(),
//             value.borrow(),
//             SetMode::Set,
//             finalizer,
//         )
//     }

//     /// Sets the value associated with the key in the dictionary
//     /// only if the key was already present in it.
//     pub fn replace_ext<Q, E, T>(
//         &mut self,
//         key: Q,
//         aug: E,
//         value: T,
//         finalizer: &mut dyn Finalizer<C>,
//     ) -> Result<(), Error>
//     where
//         Q: Borrow<K>,
//         E: Borrow<A>,
//         T: Borrow<V>,
//     {
//         self.insert_impl(
//             key.borrow(),
//             aug.borrow(),
//             value.borrow(),
//             SetMode::Replace,
//             finalizer,
//         )
//     }

//     /// Sets the value associated with key in dictionary,
//     /// but only if it is not already present.
//     pub fn add_ext<Q, E, T>(
//         &mut self,
//         key: Q,
//         aug: E,
//         value: T,
//         finalizer: &mut dyn Finalizer<C>,
//     ) -> Result<(), Error>
//     where
//         Q: Borrow<K>,
//         E: Borrow<A>,
//         T: Borrow<V>,
//     {
//         self.insert_impl(
//             key.borrow(),
//             aug.borrow(),
//             value.borrow(),
//             SetMode::Add,
//             finalizer,
//         )
//     }

//     fn insert_impl(
//         &mut self,
//         key: &K,
//         aug: &A,
//         value: &V,
//         mode: SetMode,
//         finalizer: &mut dyn Finalizer<C>,
//     ) -> Result<(), Error>
//     where
//         for<'c> C: CellFamily + 'c,
//         K: Store<C> + DictKey,
//         A: Store<C>,
//         V: Store<C>,
//     {
//         let key = ok!(serialize_entry(key, finalizer));
//         let value = ok!(serialize_aug_entry(aug, value, finalizer));
//         self.dict.root = ok!(dict_insert(
//             &self.dict.root,
//             &mut key.as_ref().as_slice(),
//             K::BITS,
//             &value.as_ref().as_slice(),
//             mode,
//             finalizer
//         ));
//         Ok(())
//     }
// }

/// An iterator over the entries of an [`AugDict`].
///
/// This struct is created by the [`iter`] method on [`AugDict`]. See its documentation for more.
///
/// [`iter`]: AugDict::iter
pub struct AugIter<'a, C: CellFamily, K, A, V> {
    inner: Iter<'a, C, K, (A, V)>,
}

impl<C: CellFamily, K, A, V> Clone for AugIter<'_, C, K, A, V> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, C: CellFamily, K, A, V> AugIter<'a, C, K, A, V>
where
    K: DictKey,
{
    /// Creates an iterator over the entries of a dictionary.
    pub fn new(root: &'a Option<CellContainer<C>>) -> Self {
        Self {
            inner: Iter::new(root),
        }
    }
}

impl<'a, C, K, A, V> Iterator for AugIter<'a, C, K, A, V>
where
    for<'c> C: DefaultFinalizer + 'c,
    K: DictKey,
    (A, V): Load<'a, C>,
{
    type Item = Result<(K, A, V), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next()? {
            Ok((key, (aug, value))) => Some(Ok((key, aug, value))),
            Err(e) => Some(Err(e)),
        }
    }
}

// fn serialize_aug_entry<C: CellFamily, A: Store<C>, V: Store<C>>(
//     aug: &A,
//     entry: &V,
//     finalizer: &mut dyn Finalizer<C>,
// ) -> Result<CellContainer<C>, Error> {
//     let mut builder = CellBuilder::<C>::new();
//     if aug.store_into(&mut builder, finalizer) && entry.store_into(&mut builder, finalizer) {
//         if let Some(key) = builder.build_ext(finalizer) {
//             return Ok(key);
//         }
//     }
//     Err(Error::CellOverflow)
// }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prelude::RcBoc;

    // #[test]
    // fn dict_set() {
    //     let mut dict = AugDict::<RcCellFamily, u32, bool, u16>::new();
    //     dict.set(123, false, 0xffff).unwrap();
    //     assert_eq!(dict.get(123).unwrap(), Some((false, 0xffff)));

    //     dict.set(123, true, 0xcafe).unwrap();
    //     assert_eq!(dict.get(123).unwrap(), Some((true, 0xcafe)));
    // }

    // #[test]
    // fn dict_set_complex() {
    //     let mut dict = AugDict::<RcCellFamily, u32, bool, u32>::new();
    //     for i in 0..520 {
    //         dict.set(i, true, 123).unwrap();
    //     }
    // }

    // #[test]
    // fn dict_replace() {
    //     let mut dict = AugDict::<RcCellFamily, u32, bool, u16>::new();
    //     dict.replace(123, false, 0xff).unwrap();
    //     assert!(!dict.contains_key(123).unwrap());

    //     dict.set(123, false, 0xff).unwrap();
    //     assert_eq!(dict.get(123).unwrap(), Some((false, 0xff)));
    //     dict.replace(123, true, 0xaa).unwrap();
    //     assert_eq!(dict.get(123).unwrap(), Some((true, 0xaa)));
    // }

    // #[test]
    // fn dict_add() {
    //     let mut dict = AugDict::<RcCellFamily, u32, bool, u16>::new();

    //     dict.add(123, false, 0x12).unwrap();
    //     assert_eq!(dict.get(123).unwrap(), Some((false, 0x12)));

    //     dict.add(123, true, 0x11).unwrap();
    //     assert_eq!(dict.get(123).unwrap(), Some((false, 0x12)));
    // }

    #[test]
    fn dict_iter() {
        let boc = RcBoc::decode_base64("te6ccgEBFAEApAABCYAAAABAAQIDzkAFAgIB1AQDABEAAAACQAAAACAAEQAAAAIAAAAAYAIBIA0GAgEgCgcCASAJCAARAAAAAcAAAACgABEAAAABgAAAAOACASAMCwARAAAAAUAAAAEgABEAAAABAAAAAWACASARDgIBIBAPABEAAAAAwAAAAaAAEQAAAACAAAAB4AIBIBMSABEAAAAAQAAAAiAAEQAAAAAAAAACYA==").unwrap();
        let dict = boc.parse::<AugDict<_, u32, u32, u32>>().unwrap();

        assert_eq!(*dict.root_extra(), 0);

        let size = dict.values().count();
        assert_eq!(size, 10);

        for (i, entry) in dict.iter().enumerate() {
            let (key, aug, value) = entry.unwrap();
            assert_eq!(key, aug);
            assert_eq!(key, i as u32);
            assert_eq!(value, 9 - i as u32);
        }
    }
}
