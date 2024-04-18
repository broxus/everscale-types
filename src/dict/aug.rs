use std::borrow::Borrow;
use std::marker::PhantomData;

use super::{aug_dict_insert, SetMode};
use crate::cell::*;
use crate::error::*;
use crate::util::*;

use super::raw::*;
use super::typed::*;
use super::{read_label, DictKey};

pub(crate) trait AugDictSkipValue<'a> {
    fn skip_value(slice: &mut CellSlice<'a>) -> bool;
}

impl<'a> AugDictSkipValue<'a> for crate::num::Tokens {
    #[inline]
    fn skip_value(slice: &mut CellSlice<'a>) -> bool {
        if let Ok(token_bytes) = slice.load_small_uint(4) {
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
pub struct AugDict<K, A, V> {
    dict: Dict<K, (A, V)>,
    extra: A,
    _key: PhantomData<K>,
    _value: PhantomData<(A, V)>,
}

impl<K, A: ExactSize, V> ExactSize for AugDict<K, A, V> {
    #[inline]
    fn exact_size(&self) -> CellSliceSize {
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
        context: &mut dyn CellContext,
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
}

impl<K: DictKey, A, V> AugDict<K, A, V> {
    #[allow(unused)]
    pub(crate) fn load_from_root<'a>(
        slice: &mut CellSlice<'a>,
        context: &mut dyn CellContext,
    ) -> Result<Self, Error>
    where
        A: Load<'a>,
        V: AugDictSkipValue<'a>,
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

fn load_from_root<'a, A, V>(
    slice: &mut CellSlice<'a>,
    key_bit_len: u16,
    context: &mut dyn CellContext,
) -> Result<(A, Cell), Error>
where
    A: Load<'a>,
    V: AugDictSkipValue<'a>,
{
    let root = *slice;

    let label = ok!(read_label(slice, key_bit_len));
    let extra = if label.remaining_bits() != key_bit_len {
        if !slice.try_advance(0, 2) {
            return Err(Error::CellUnderflow);
        }
        ok!(A::load_from(slice))
    } else {
        let extra = ok!(A::load_from(slice));
        if !V::skip_value(slice) {
            return Err(Error::CellUnderflow);
        }
        extra
    };

    let root_bits = root.remaining_bits() - slice.remaining_bits();
    let root_refs = root.remaining_refs() - slice.remaining_refs();

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

// TODO: add support for `extra` in edges

impl<K, A, V> AugDict<K, A, V>
where
    K: Store + DictKey,
    A: Store,
    V: Store,
{
    /// Sets the augmented value associated with the key in the aug dictionary.
    ///
    /// Use [`set_ext`] if you need to use a custom cell context.
    ///
    /// [`set_ext`]: AugDict::set_ext
    pub fn set<Q, E, T>(
        &mut self,
        key: Q,
        aug: E,
        value: T,
        extra_comparator: fn(
            left: &CellSlice,
            right: &CellSlice,
            builder: &mut CellBuilder,
            context: &mut dyn CellContext,
        ) -> Result<(), Error>,
    ) -> Result<bool, Error>
    where
        Q: Borrow<K>,
        E: Borrow<A>,
        T: Borrow<V>,
    {
        self.set_ext(
            key,
            aug,
            value,
            extra_comparator,
            &mut Cell::empty_context(),
        )
    }

    /// Sets the value associated with the key in the dictionary.
    pub fn set_ext<Q, E, T>(
        &mut self,
        key: Q,
        aug: E,
        value: T,
        extra_comparator: fn(
            left: &CellSlice,
            right: &CellSlice,
            builder: &mut CellBuilder,
            context: &mut dyn CellContext,
        ) -> Result<(), Error>,
        context: &mut dyn CellContext,
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
            extra_comparator,
            context,
        )
    }

    /// Sets the augmented value associated with the key in the aug dictionary
    /// only if the key was already present in it.
    ///
    /// Use [`replace_ext`] if you need to use a custom cell context.
    ///
    /// [`replace_ext`]: AugDict::replace_ext
    pub fn replace<Q, E, T>(
        &mut self,
        key: Q,
        aug: E,
        value: T,
        extra_comparator: fn(
            left: &CellSlice,
            right: &CellSlice,
            builder: &mut CellBuilder,
            context: &mut dyn CellContext,
        ) -> Result<(), Error>,
    ) -> Result<bool, Error>
    where
        Q: Borrow<K>,
        E: Borrow<A>,
        T: Borrow<V>,
    {
        self.replace_ext(
            key,
            aug,
            value,
            extra_comparator,
            &mut Cell::empty_context(),
        )
    }

    /// Sets the value associated with the key in the dictionary
    /// only if the key was already present in it.
    pub fn replace_ext<Q, E, T>(
        &mut self,
        key: Q,
        aug: E,
        value: T,
        extra_comparator: fn(
            left: &CellSlice,
            right: &CellSlice,
            builder: &mut CellBuilder,
            context: &mut dyn CellContext,
        ) -> Result<(), Error>,
        context: &mut dyn CellContext,
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
            extra_comparator,
            context,
        )
    }

    /// Sets the value associated with key in aug dictionary,
    /// but only if it is not already present.
    ///
    /// Use [`add_ext`] if you need to use a custom cell context.
    ///
    /// [`add_ext`]: AugDict::add_ext
    pub fn add<Q, E, T>(
        &mut self,
        key: Q,
        aug: E,
        value: T,
        extra_comparator: fn(
            left: &CellSlice,
            right: &CellSlice,
            builder: &mut CellBuilder,
            context: &mut dyn CellContext,
        ) -> Result<(), Error>,
    ) -> Result<bool, Error>
    where
        Q: Borrow<K>,
        E: Borrow<A>,
        T: Borrow<V>,
    {
        self.add_ext(
            key,
            aug,
            value,
            extra_comparator,
            &mut Cell::empty_context(),
        )
    }

    /// Sets the value associated with key in dictionary,
    /// but only if it is not already present.
    pub fn add_ext<Q, E, T>(
        &mut self,
        key: Q,
        aug: E,
        value: T,
        extra_comparator: fn(
            left: &CellSlice,
            right: &CellSlice,
            builder: &mut CellBuilder,
            context: &mut dyn CellContext,
        ) -> Result<(), Error>,
        context: &mut dyn CellContext,
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
            extra_comparator,
            context,
        )
    }

    fn insert_impl(
        &mut self,
        key: &K,
        extra: &A,
        value: &V,
        mode: SetMode,
        comparator: fn(
            left: &CellSlice,
            right: &CellSlice,
            builder: &mut CellBuilder,
            context: &mut dyn CellContext,
        ) -> Result<(), Error>,
        context: &mut dyn CellContext,
    ) -> Result<bool, Error>
    where
        K: Store + DictKey,
        A: Store,
        V: Store,
    {
        let mut key_builder = CellBuilder::new();
        ok!(key.store_into(&mut key_builder, &mut Cell::empty_context()));
        aug_dict_insert(
            &mut self.dict.root,
            &mut key_builder.as_data_slice(),
            K::BITS,
            extra,
            value,
            mode,
            comparator,
            context,
        )
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
    pub fn iter<'a>(&'a self) -> AugIter<'_, K, A, V>
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

// impl<K, A, V> AugDict<K, A, V>
// where
//     K: Store + DictKey,
//     A: Store,
//     V: Store,
// {
//     /// Sets the value associated with the key in the dictionary.
//     pub fn set_ext<Q, E, T>(
//         &mut self,
//         key: Q,
//         aug: E,
//         value: T,
//         context: &mut dyn CellContext,
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
//             context,
//         )
//     }

//     /// Sets the value associated with the key in the dictionary
//     /// only if the key was already present in it.
//     pub fn replace_ext<Q, E, T>(
//         &mut self,
//         key: Q,
//         aug: E,
//         value: T,
//         context: &mut dyn CellContext,
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
//             context,
//         )
//     }

//     /// Sets the value associated with key in dictionary,
//     /// but only if it is not already present.
//     pub fn add_ext<Q, E, T>(
//         &mut self,
//         key: Q,
//         aug: E,
//         value: T,
//         context: &mut dyn CellContext,
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
//             context,
//         )
//     }

//     fn insert_impl(
//         &mut self,
//         key: &K,
//         aug: &A,
//         value: &V,
//         mode: SetMode,
//         context: &mut dyn CellContext,
//     ) -> Result<(), Error>
//     where
//         K: Store + DictKey,
//         A: Store,
//         V: Store,
//     {
//         let key = ok!(serialize_entry(key, context));
//         let value = ok!(serialize_aug_entry(aug, value, context));
//         self.dict.root = ok!(dict_insert(
//             &self.dict.root,
//             &mut key.as_ref().as_slice(),
//             K::BITS,
//             &value.as_ref().as_slice(),
//             mode,
//             context,
//         ));
//         Ok(())
//     }
// }

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

// fn serialize_aug_entry<A: Store, V: Store>(
//     aug: &A,
//     entry: &V,
//     context: &mut dyn CellContext,
// ) -> Result<CellContainer, Error> {
//     let mut builder = CellBuilder::new();
//     if aug.store_into(&mut builder, context) && entry.store_into(&mut builder, context) {
//         if let Some(key) = builder.build_ext(context) {
//             return Ok(key);
//         }
//     }
//     Err(Error::CellOverflow)
// }

#[cfg(test)]
mod tests {
    use std::str::FromStr;
    use everscale_types::models::Block;
    use crate::boc::BocRepr;
    use crate::models::{AccountBlock, CurrencyCollection};
    use super::*;
    use crate::prelude::Boc;

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
        let boc = Boc::decode_base64("te6ccgEBFAEApAABCYAAAABAAQIDzkAFAgIB1AQDABEAAAACQAAAACAAEQAAAAIAAAAAYAIBIA0GAgEgCgcCASAJCAARAAAAAcAAAACgABEAAAABgAAAAOACASAMCwARAAAAAUAAAAEgABEAAAABAAAAAWACASARDgIBIBAPABEAAAAAwAAAAaAAEQAAAACAAAAB4AIBIBMSABEAAAAAQAAAAiAAEQAAAAAAAAACYA==").unwrap();
        let dict = boc.parse::<AugDict<u32, u32, u32>>().unwrap();

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

    #[test]
    fn aug_test() {
        //let boc = Boc::decode_base64("te6ccgICBFsAAQAAjsMAAAQQEe9VqgAAACoEWARVAeoAAQOJSjP2/cSS9rli/7+/1+4pu3HAlbLYUN1nMXx70o8cEDjFAjBVANDEL9leiYDIyg8M1LSX1kurJURSmmT+2/Bh4ET7putAAHEAKgACAQmhDP1wGgADAgkQhn64DQAgAAQCCRBb4m2dAAsABQIJEC7u/PEABwAGAqe/QaMWXvwYBGTp6SxRBicVuKhyPspTOz0wuzH2WIk0KAaBJUj3heDRiy9+DAIydPSWKIMTitxUOR9lKZ2emF2Y+yxEmhQDoAAAFimp9uRHIElSPeIAiQCNA6e/X5CvfvE9MjIHhOdNHTq0IenyyPrz9s0/NRVy1F1tEpaAUi7wBc/IV794npkZA8Jzpo6dWhD0+WR9eftmn5qKuWoutolLngAAFimp9uRKAUi7wCAACgAJAAgAgnJpOJckQnAxrphsV0MflErz3Xx0QZ9Q4IdMyqvVJUIQa6++dV2XZrPzn2z/xzwvzPNTVeiTNieU2W15J2WA9eBzAQu6gDWsVygBUwEJuHyCmOgB3QIJECzzcK0AEAAMA6e/Xdjy1akV/urmNpdm+BdTJaKeH4hI/kzoV3wRe/1JMoaAQmcKRa7seWrUiv91cxtLs3wLqZLRTw/EJH8mdCu+CL3+pJlDngAAFimp9uRCAQmcKSAADwAOAA0AgnJrk8JdlX9o3tvDgWlOBqo7shoL9wuUG1yQ9raOxlHajqXtWhlAe+nqOf2S9/UQ+yRSjeQxnHYGucj2E0N0XB39AQm8f/tAyAEWAQu6gCJryYgByQILVAkpo9lAAB8AEQOlvukjUxhhK8eAf+tFuTiEpZlSoXC5HaiZ/N5RyV6n/5i6AJOKa5Z0kamMMJXjwD/1otycQlLMqVC4XI7UTP5vKOSvU//MXnQAAFimp9uRIAk4proAFgATABIAgnKQlUCHzT/2OXAiCyfPBmZkaRTkAFVq1Bb/LdqqgndBETm/Efye3sOR+B8Mbl0jKpS6aSBjDbXPZniXqDCrLCRBAgmhGP9fAgAVABQBBww/18EAwQEHDD/XwQCAAgkQBByj3QAcABcCBw0V1QEAGwAYAglkyq1mEAAaABkBBwxq/qEAqQEHDD/XwQCuAQm4Y1f1CADZAgcPBs7dAB4AHQEJvGNX9QgAowEJsnTegegAzAKnvtyLiuWZfDHso+1uW2wqA/zk6NBy0cGzvftgJ5v+P9QCBAFHgRZORcVyzL4Y9lH2ty22FQH+cnRoOWjg2d79sBPN/x/qAoAAAFimp9uRDoEAUeBIAO4A8gILZQKpxKcQACQAIQIJECFMTB0AIwAiAqe+/nIV1yWzQuYDAm38u0hDBIk2jqs0XLBMICygQk5M4LoA6L8LlP85CuuS2aFzAYE2/l2kIYJEm0dVmi5YJhAWUCEnJnBegAAAWKan25E0gDovwugA4gDmAqe++GwQfU1azNASs3nhNNr8QIX1kHnnHVfusenU8Eh+pAoDQMp4FNw2CD6mrWZoCVm88JptfiBC+sg8846r91j06ngkP1IGgAAAWKan25EogNAynggBKwEvA6W/AhJZz5ry7sEmh+8KampJqVRSw30nWwEBGOBP/nqhG/0AlP/lSkEJLOfNeXdgk0P3hTU1JNSqKWG+k62AgIxwJ/89UI3/OgAALFNT7ciQCU/+VQApACYAJQCCcur/wbjQ6qZF5agqgx7bUkvmPL6hkkvmcrPxvKKsIKYaiSWQyZuxXy/hpExtQ9ebp6uJ8YKkLS8DleMVMr7SGWUCC80Aa+RwEAAoACcBCUPkEWhAASEBCUPLgFhAALcBCajOkbdVAHcBAYIAKwIBAQBaACwCAQEARAAtAgEBADMALgIDUEAAMQAvA0O+yJNbfxnJ2G3QVqDQ/+f2Iyqe5Hg+tu6N9ozTRpThxTAUAH4AzAAwAgdmIbOtAH4AdwNDvse729c0rQHIp+QM9kHTGT+idbkUccpP+V8lg2JKO7r4FACFALcAMgIHZgosMQCFAIACAQEAOwA0AgEBADkANQIBAQA3ADYCQ764vLl2QHgrNwQgIGZkVs37Gk4JJUrQsa7DxN+upimoIAgBMwErA0O+hy5GA09ol1KszJyyLMimfMlb9FEHba3G8t81PZFfWfAoAKEA7gA4AgdmMkCxAKEAiQNDvstoj0l9yqGLtfUbHYR4deIlAvgjzvwO4DeE7pyznYDIFACmAO4AOgIHZhAX1QCmAKMCAQEAQgA8AgEBAEAAPQIBAQA/AD4CQ75As8X5WqazwKzFCFaIYWw4dKROZ+HE78cqyeSpCMAHQBAA9wDuAkO+XlDj6zs8hy3IXaX7h8iEjs6T931FM0WaJVvmTuVDzkAQAJEAiQNDvqrWhj5kHrB81EojroHb2+E5v5C44WFj3UBWSS6dgDIwKACsASsAQQIHZhAX1QCsAKkDQ77bro4HHBA9fUzBflHBF9uFLXoc/xRS980mlrxoNstRKBQAswHdAEMCB2YKLDEAswCuAgEBAFIARQIBAQBIAEYDQ78RGftWcvu56xle1eQ6bKH4zXq1fBFS6ujBaymPULJLnAoAvwFTAEcCB2e4XKMAvwC3AgEBAEoASQJDvtY+wnF+KrgzaOnQa1aEpd9v995dSAJ1ZSgC1Dl1fPVwBAEIAO4CAQEATgBLAgNAQABNAEwCQ74gLxB7r2+fYJj8fZA5H8ssv3gYj9IbvZFOXfavsmp/wCAA6gDiAkO+GkhAknJGNSE41GoBcDcXuYDiiCPBx3obu0z3aL/zTMAgAUEBKwIDUEAAUABPAkO+Jw2wuCJwFLCYdpda6LqHMEIekOkmRF1LhA5cB8xOcUAgAQoA7gNDvhyQccEoi7iGaB/aWu6SVMKBsjZlIiOB949WkCl2SUoAoADHASEAUQIHZgosMQDHAMECAQEAWABTAgEBAFYAVANDvu/l9+l6/4wMn8isHGX9FZ2nQGR+xjvOqWdWxmIeqHp4FADeAIkAVQIHZhAX1QDeANkDQ77C3Cc5+LD+1tLX9xGnqdQNA/OzYqXAjgmnjtapF3rPmBQA7AErAFcCB2Ye37cA7ADiA0O/ECPlWANMxzdIY5yjcsS+cnRQVFEwkNkDtVQd5O6ak1AKAREByQBZAgdmKSiLAREA7gIBAQBoAFsCAQEAYwBcAgEBAF8AXQNDvzZG7yBN/h/pXrD6wnKfMV9EhEIwbdpFr/DDnQY7jmv8CgEdAO4AXgIHZhWYswEdARYCA1BAAGIAYANDvoAILNtFfYObO1HTyoXK9Mb8MywtKXBUj5wsrwj+7JXAKAEoAVMAYQIHZhRLXQEoASECQ76t1fMTSXpnADwr9PdM+DDQhet68ZG4zX05097zncBPcAgAmACJAgV8QEAAZgBkA0O90HMTFTOIwZZSbnnd0qr8w9lbNkX3ED8Dk6Ay5T65VQFAAUgAiQBlAgdmLTedAUgBKwNDvdLhdIqVkKRetp/aqt01uhimTLQg+sra2XNvr+y9vS4BQAHEAOIAZwIHZhWYswHEAVMCAQEAbQBpAgEBAGsAagJDvw8KifIdmO8LkhCVi3MhiPBhAIYcKAotfahX76qqkqBEAgE/ASsDQ78KlneOTreDxm8477S5nynH90S/WvvvVuat7Id9TiD4UAoB1QB3AGwCB2Yhs60B1QHJAgNQQABvAG4CQ77fciwYHScMEwoaVLKX1U5zENaY7BdVJElfDR0gYnLWqAQAmgCJA0O+6eP/y8yTTbtFvEA5vtbTYCf+8VjnMzgluZRWR0kzzhAUAeUBFgBwAgdmFEtdAeUB3QELoA0XYrggAHICCxAGi7FcEAESAHMCCxAFRkqUEAC0AHQCCQ0Q+MgQAIYAdQIJUxXv7gQAfwB2AlG+yJNbfxnJ2G3QVqDQ/+f2Iyqe5Hg+tu6N9ozTRpThxTGIbOsBmIbOtAB+AHcDtXIISWc+a8u7BJofvCmpqSalUUsN9J1sBARjgT/56oRv8AACxTU+3Ig3SDNThgxsSSRcmzDJS8UwLDE2KIgG1Us362yly7+91WAAAsU077TeJmH7G2AANHSNuqgAfAB7AHgCGQSA18k1pOkAGHN/sxEAegB5AG/JjKNaTCGzeAAAAAAABAACAAAAAhny7TLn9L8UUkQw+BoqqhB7VYxBM+OK4rPK+P5ifHGCQZBOtACeRP3sPQkAAAAAAAAAAADVAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACCcur/wbjQ6qZF5agqgx7bUkvmPL6hkkvmcrPxvKKsIKYa5WYQlLx5GKcs6TabJbSE1LKJz5GHOz5BL2yJgqXMcvcCAeAA0wB9AQHfAdYBDEYGAxDZ1gDTAlG+x7vb1zStAcin5Az2QdMZP6J1uRRxyk/5XyWDYko7uvmCiwwBmCiwxACFAIADtXnSRqYwwlePAP/Wi3JxCUsypULhcjtRM/m8o5K9T/8xcAACxTU+3IpDWRz/Qaw3f3xOwXf6VcCEEaslSoHuBdeEO9oW9MX5QKAAAsU1PtyJtmH7G2AAFGH+vggAhACDAIECFQwJAUlSpBhh/r4RAIIAwwCeQILMBUToAAAAAAAAAAAXAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACCchkZ8xiTYvCaEJvn1chUSwus83qXuIuZGTBODE96gHU9MrP01SGYCFLF2k5RdhcZWHTablZefH6LYMXWtxNAs88BAaAAvgEMRgYDBRYYAL4CCQy5ORAQAKcAhwIJDISxCBAAogCIAlG+w5cjAae0S6lWZk5ZFmRTPmSt+iiDttbjeW+ansivrPmMkCwBmMkCxAChAIkDt34NGLL34MAjJ09JYogxOK3FQ5H2UpnZ6YXZj7LESaFAMAACxTU+3IjnSB2jNPtlPdEwSJaGc/azFk7rCe/BcM9Z/PiDZEFwfvAAAr9YXA/85mH7G2AAtIElSPeIAI4AjQCKAh8FAKTORQkwAO5X2IDKzvIRAIwAiwBvya+faE0CXGAAAAAAAAwAAgAAAAuwuZ60BmxTz9fOmBQnWwLRJUM0U5OGYWEmcPq+OeLE5EaRDrQAoGAz60w9CQAAAAAAAAAACDsAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIJyd40z0uKeV9pWb4hCXH9C2WnH10ks3Nx5VznqPZ5dnFbP8aynEvr9ndkGZb2nNUKFjnoV0X8wpr2fK/QsYjCSGgIB4AD5AI8CAdkAkgCQAQHUAJEBjeAHBoxZe/BgEZOnpLFEGJxW4qHI+ylM7PTC7MfZYiTQoBgAAFimp9uRJsw/Y2wmfHaBAAAAAUAAAAAAHYUKlKo38AEQiOXgAgsCASAAlgCTAgEgAJUAlAEBIAFJAQEgAN8CASAAmQCXAQEgAJgA7eAHBoxZe/BgEZOnpLFEGJxW4qHI+ylM7PTC7MfZYiTQoBgAAFimp9uRIMw/Y2w6BObSsw/Y2wAAAAAAAAAAAAAAAAAAAAAAAABCkFT9yefuc7Q9vTb5AAAAAAAAAAoTaaVsujSJROMDAJWLSFKa+WUuanben8VAAQEgAJoBXeAHBoxZe/BgEZOnpLFEGJxW4qHI+ylM7PTC7MfZYiTQoBgAAFimp9uRHsw/Y2zAAJsBS1AciqeAE6SNTGGErx4B/60W5OISlmVKhcLkdqJn83lHJXqf/mLwAJwBQ4ATpI1MYYSvHgH/rRbk4hKWZUqFwuR2omfzeUclep/+YvAAnQFjgBk/2AB0Qj788sABWKFpYnYkxXjcvEWPzOJ03q57/yFhoAAAAAAAqPsiRyrERquhXdAAngFrgAmkZOWE74jXPrhfHemnLMFmI4MPHI3GrUldCo2fTsIG4AAAAAAAAAAAAAABM18U30AAAAA4AJ8BA9BAAKABg4AZP9gAdEI+/PLAAVihaWJ2JMV43LxFj8zidN6ue/8hYaAAAAAAAACBxwPMKQltkiYAAAAAAAAAAAAAAAAAAAAAEAG9AQxGBgMZIFgA+QJRvstoj0l9yqGLtfUbHYR4deIlAvgjzvwO4DeE7pyznYDJhAX1AZhAX1QApgCjA7V50kamMMJXjwD/1otycQlLMqVC4XI7UTP5vKOSvU//MXAAAsU1PtyI761i1HavUVtDbJ+YES2rrzC+qH3eediGuQsoBASmv9vwAALFNT7ciBZh+xtgABRjV/UIAKUApADaAIJyASw/6td5ZbFGmvPfD4raaE9UCQa5LTaSnJ+uk/pR0K0VaKijFECnlvy2HXdrgZI7B63MCwgjW8oVXfmY4tDlawEBoAEEAQxGBgMIC+oBBAIJDDSICBAArQCoAlG+1WtDHzIPWD5qJRHXQO3t8JzfyFxwsLHuoCskl07AGRmEBfUBmEBfVACsAKkDtXnSRqYwwlePAP/Wi3JxCUsypULhcjtRM/m8o5K9T/8xcAACxTU+3Im8eAjMRZEyvJWq5TSxBhVKWtiK++5jspzNUjvVc+1Y8sAAAsU1PtyJpmH7G2AAFGNX9QgAqwCqANoAgnLdq6TMrFqvL6IhNPs67Hp6vQZWOu7+DkGVfv137JDaWRkZ8xiTYvCaEJvn1chUSwus83qXuIuZGTBODE96gHU9AQGgATsBDEYGAwgL6gE7AlG+266OBxwQPX1MwX5RwRfbhS16HP8UUvfNJpa8aDbLUSmCiwwBmCiwxACzAK4DtXnSRqYwwlePAP/Wi3JxCUsypULhcjtRM/m8o5K9T/8xcAACxTU+3Imosh/rbQgmZ4EuQ9zeeuJLgUnyHT6DoPVoVBGAjO5bSTAAAsU1PtyJRmH7G2AAFGH+vggAsgCxAK8CFQwJAn4l21hh/r4RALAAwwCeQILMCjXYAAAAAAAAAAAXAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACCci7IFzWk/EKn01iDEd6fX07KDSxSV7WOIQ3tWOnKwkcJ3aukzKxary+iITT7Oux6er0GVjru/g5BlX79d+yQ2lkBAaAB5AEMRgYDBRYYAeQCCxAENVHMEADIALUCCQ+FEaQQAMAAtgJRvxEZ+1Zy+7nrGV7V5DpsofjNerV8EVLq6MFrKY9Qskuc9wuUQM9wuUYAvwC3A7VyCElnPmvLuwSaH7wpqakmpVFLDfSdbAQEY4E/+eqEb/AAAsU1PtyKAJ0KuuhEZDYs0Qk5x4sIdZ2JARlhTFR9waJlwOwpAtsQAALFNT7ciDZh+xtgADR5cAsIALwAuwC4AhUECQF9eEAYeR6qEQC6ALkAb8mD0JBMCiwgAAAAAAAEAAIAAAAD6PuxuL94kPYHBSNPw4fUzXkxCq8QqscWReNoxa0HKPhAUBYMAJ5GbkwGGoAAAAAAAAAAAMYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIJy5WYQlLx5GKcs6TabJbSE1LKJz5GHOz5BL2yJgqXMcveU6J9Y+l3PkAzKo7f4rqM6wIryzwH+d7NMwx52SYTxcgIB4AFeAL0BAd8AvgCxSABBCSznzXl3YJND94U1NSTUqilhvpOtgICMcCf/PVCN/wAnSRqYwwlePAP/Wi3JxCUsypULhcjtRM/m8o5K9T/8xdAUlSpABgosMAAAWKan25FCzD9jbEABDEYGA9wuUQFeAlG/CckHHBKIu4hmgf2lruklTCgbI2ZSIjgfePVpApdklKDBRYYAzBRYYgDHAMEDtXnSRqYwwlePAP/Wi3JxCUsypULhcjtRM/m8o5K9T/8xcAACxTU+3IpXBU+NyhQ6NIlVTrNQibZhlxYIi8lRPNq6dAlJHMdPaHAAAsU1PtyKRmH7G2AAFGH+vggAxgDFAMICFQwJKIf3+5hh/r4RAMQAwwBbwAAAAAAAAAAAAAAAAS1FLaRJ5QuM990nhh8UYSKv4bVGu4tw/IIW8MYUE5+OBACeQILMPQkAAAAAAAAAAAAXAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACCcjKz9NUhmAhSxdpOUXYXGVh02m5WXnx+i2DF1rcTQLPPOb8R/J7ew5H4HwxuXSMqlLppIGMNtc9meJeoMKssJEEBAaABJwEMRgYDBRYYAScCCQywQCgQAO0AyQIJDF3vFBAA4QDKAglTCAvqBADYAMsCQ75ZolbukMQJvGto9qf+HD/DvzW6JkKXgFuijaAaGIR2IAEA1ADMA7V50kamMMJXjwD/1otycQlLMqVC4XI7UTP5vKOSvU//MXAAAsU1PtyIE2tGss3sDwbW654b1y+8BBbM0jg2CXXONgcdaiSUiy8gAALFNO+03lZh+xtgADR03oHoANEA0ADNAhEMgMdGG84+REAAzwDOAG/JjKNaTCGzeAAAAAAAAgAAAAAAAodpSy5T3oC9HBzhToEk1pnd59iVPbzqNuE0szbIQMXSQZBOtACdQ+WjE4gAAAAAAAAAADBAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIACCcpCVQIfNP/Y5cCILJ88GZmRpFOQAVWrUFv8t2qqCd0ERASw/6td5ZbFGmvPfD4raaE9UCQa5LTaSnJ+uk/pR0K0CAeAA1ADSAQHfANMBsWgBOkjUxhhK8eAf+tFuTiEpZlSoXC5HaiZ/N5RyV6n/5i8ACCElnPmvLuwSaH7wpqakmpVFLDfSdbAQEY4E/+eqEb/TWk6QAAYhs6wAAFimp9uRBMw/Y2zAANcBRYgBOkjUxhhK8eAf+tFuTiEpZlSoXC5HaiZ/N5RyV6n/5i4MANUB4aQytfojLVyzkKGPsWCka03dTems8JXAqrKScVQ57RUQDsR+5Op1/A9f/hx2BBziy5TJtkrC/r6HofJbVTq0c4XBV5K65vUvqyGd0F/O8qDl6QE6SQC2Awb46+Bz1ARVdkAAAGO684kTmYfsdtM7mRsgANYBZYAEEJLOfNeXdgk0P3hTU1JNSqKWG+k62AgIxwJ/89UI3+AAAAAAAAAAAAAAABrSdIAQOADXAWtGqdfsAAAAAAAAAAAAAAAJLJRXkIAV3Y8tWpFf7q5jaXZvgXUyWinh+ISP5M6Fd8EXv9STKHAB2AJRvn+X36Xr/jAyfyKwcZf0VnadAZH7GO86pZ1bGYh6oenmEBfUBmEBfVAA3gDZA7V50kamMMJXjwD/1otycQlLMqVC4XI7UTP5vKOSvU//MXAAAsU1PtyJRD7vYfF2algXFicNBdcV+PjujlG5PPbM+YTAQg4G/wGAAALFNT7ciOZh+xtgABRjV/UIAN0A3ADaARMMCOYloFBjV/UJANsAnEDbKJxAAAAAAHgAAAAxAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACCchVoqKMUQKeW/LYdd2uBkjsHrcwLCCNbyhVd+Zji0OVrLsgXNaT8QqfTWIMR3p9fTsoNLFJXtY4hDe1Y6crCRwkBAaAA3wEMRgYDCAvqAN8Br0gBwaMWXvwYBGTp6SxRBicVuKhyPspTOz0wuzH2WIk0KAcAJ0kamMMJXjwD/1otycQlLMqVC4XI7UTP5vKOSvU//MXOYloEBhAX1AAAWKan25EizD9jbMAA4AB5BONBUAAFPtMeipUOAAAAAAABUfZEjlWIjVdCu4AAAAAAAAEDjgeYUhLbJEwAAAAAAAAAAAAAAAJmvim+oAJRvsLcJzn4sP7W0tf3Eaep1A0D87NipcCOCaeO1qkXes+Zh7ftgZh7ftwA7ADiA7dz/OQrrktmhcwGBNv5dpCGCRJtHVZouWCYQFlAhJyZwXAAAsU1PtyJo/9R8PLp3QqPfOd6mMtF5vqNuMOS4yfk3uY1ZiCiVe4AAALFNO+03aZh+xtgAFSAOi/C6ADnAOYA4wIbBIEqCStbumWYgDe/fBEA5QDkAG/JjyT0TE32PAAAAAAABgACAAAABACpiHVGRJFW2jA5iwAXBPGjCXc1bU47FwdFuGI2X9hCQhBaxACeTkWMPQkAAAAAAAAAAAGaAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACCcj30pQmhOA3kmD1vL5XzlZC1wx3uQffOLZQgSfD4UcYiFj6btpsLVDWVcnklkDgJT2ow7rXAJSU8+IOWFVGXRc4CAeABNwDoAgHdAOsA6QEBIADqAc/gAf5yFdcls0LmAwJt/LtIQwSJNo6rNFywTCAsoEJOTOC4AABYpqfbkTjMP2NsK+vBRwAAAAAAAAAAAAAABMSzf6gAAAABYATpI1MYYSvHgH/rRbk4hKWZUqFwuR2omfzeUclep/+YvAE5AQEgAcUBDEYGAw9v2wE3AlG/ECPlWANMxzdIY5yjcsS+cnRQVFEwkNkDtVQd5O6ak1DFJRFAzFJRFgERAO4Dt3k5FxXLMvhj2Ufa3LbYVAf5ydGg5aODZ3v2wE83/H+oAAACxTU+3IhyIwN5FpNEvu+jkiaCzch3nQaquR7DQDt+CkbFfKLjxbAAAsUxtN7xRmH7G2AA1IEAUeBIAPMA8gDvAh0MwJZ9STUtpl9YgPceshEA8QDwAG/JuZwMTRz99AAAAAAADgACAAAADNtBeU2qaIhPDStzTFd4V0i7rv38QL9ty4v2yyqEhDZcR9FKzACgYD9DTD0JAAAAAAAAAAAKRwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgnInJiPC560IDQ6uqivG4lo6JPGUkNlNW6nRJsaVTq3HNfVtHAOERXGU6gB1Z0QrwLtTRT4Quj6XYTe0jGg3h/mJAgHgAdAA9AIB2QEAAPUCAUgA+AD2AQEgAPcBjeAEnIuK5Zl8Meyj7W5bbCoD/OTo0HLRwbO9+2Anm/4/1AAAAFimp9uRGsw/Y2wmfHaBAAAAAUAAAAAAADb9oy9y99cuZN/gAmwBASAA+QGxaAEnIuK5Zl8Meyj7W5bbCoD/OTo0HLRwbO9+2Anm/4/1AQA4NGLL34MAjJ09JYogxOK3FQ5H2UpnZ6YXZj7LESaFANMADuV8BjJAsAAAWKan25EYzD9jbMAA+gKPNFTjRQAFPtMeipUOAAAADAEAAAACgkAMn+wAOiEffnlgAKxQtLE7EmK8bl4ix+ZxOm9XPf+QsNAAAAAAAFR9kSOVYiNV0K7oAP8A+wFDgBOkjUxhhK8eAf+tFuTiEpZlSoXC5HaiZ/N5RyV6n/5i8AD8AUOAE6SNTGGErx4B/60W5OISlmVKhcLkdqJn83lHJXqf/mLwAP0BQ4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABAA/gNjgBOkjUxhhK8eAf+tFuTiEpZlSoXC5HaiZ/N5RyV6n/5i4AAAAAAAAAAAAAAAAL68IAQB2gHpAekCA8/AAasBUAIBIAEGAQECASABAwECAQEgAR4BASABBAGvSAEnIuK5Zl8Meyj7W5bbCoD/OTo0HLRwbO9+2Anm/4/1AQAnSRqYwwlePAP/Wi3JxCUsypULhcjtRM/m8o5K9T/8xc5iWgQGEBfUAABYpqfbkRTMP2NswAEFAHkE40FQAAU+0x6KlQ5AAAAAAAAAAAAAAAJLJRXkAAAAAAAAAAAAAAAAAcLtYMAAAAAAAVH2RI5ViI1XQrugAgEgAQkBBwEBIAEIAO3gBJyLiuWZfDHso+1uW2wqA/zk6NBy0cGzvftgJ5v+P9QAAABYpqfbkRLMP2NsOgTm0rMP2NsAAAAAAAAAAAAAAAAAAAAAAAiYWoYdsNvMAE+BCscdtoAAAAAAAAAgfZx5ksP5TnTGvwRfvimnmrS2INejaLibwAEBIAEKAV3gBJyLiuWZfDHso+1uW2wqA/zk6NBy0cGzvftgJ5v+P9QAAABYpqfbkRDMP2NswAELAUtQHIqngBOkjUxhhK8eAf+tFuTiEpZlSoXC5HaiZ/N5RyV6n/5i8AEMAUOAE6SNTGGErx4B/60W5OISlmVKhcLkdqJn83lHJXqf/mLwAQ0BY4AUk5qcKxU0Kqq8xI6zxcnOzaRMAW8AGxI8jfJSPgiVJ6AAAAAAAAAAAAAAASWSivIQAQ4Ba4AZP9gAdEI+/PLAAVihaWJ2JMV43LxFj8zidN6ue/8hYaAAAAAAAKj7IkcqxEaroV3AAAAAOAEPAQPQQAEQAYOAFJOanCsVNCqqvMSOs8XJzs2kTAFvABsSPI3yUj4IlSegAAAAAAAAAAAAAAAA4XawYAAAAAAAAAAAAAAAAAAAABABvQEMRgYDFJRFAdACCQ1FZsgQAccBEwIJDNlouBABKQEUAgkMU8gcEAEgARUCUb82Ru8gTf4f6V6w+sJynzFfRIRCMG3aRa/ww50GO45r/MKzFkDMKzFmAR0BFgO1eu7Hlq1Ir/dXMbS7N8C6mS0U8PxCR/JnQrvgi9/qSZQwAALFNT7ciOYqcITWEP6OkKfSiSXNQjb8nIOplyqkEXbGYbnJO7MiMAACxTU+3IhWYfsbYAA0f/tAyAEbARoBFwIVBAkC+vCAGH9Y5xEBGQEYAG/Jh5w+TBRLOAAAAAAABAACAAAAAy55R6/pFaOfyhmsonzJ2beBIiNMGvcKsO73970XL2PWQRArxACeSAZsDDUAAAAAAAAAAAD3AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACCct15xrMNIfd/hAw/83mAKVuqvGPX6swzY6uKaaKchcvIpe1aGUB76eo5/ZL39RD7JFKN5DGcdga5yPYTQ3RcHf0CAeABHgEcAQHfAeYBDEYGAwrMWQEeAbFoASci4rlmXwx7KPtbltsKgP85OjQctHBs737YCeb/j/UBACu7Hlq1Ir/dXMbS7N8C6mS0U8PxCR/JnQrvgi9/qSZQ0C+vCAAGFZiyAABYpqfbkRbMP2NswAEfAYtz4iFDAAAAAAAAAAAAAAAJLJRXkIAH+chXXJbNC5gMCbfy7SEMEiTaOqzRcsEwgLKBCTkzguAAAAAAAAAAAAAAAAAAAAAQAegCUb8wAgs20V9g5s7UdPKhcr0xvwzLC0pcFSPnCyvCP7slcMKJa4DMKJa6ASgBIQO1cghJZz5ry7sEmh+8KampJqVRSw30nWwEBGOBP/nqhG/wAALFNT7ciif+5wjNR0qAV3kwaRij7CGswS0axWF6f/Q90oJ9aCC5AAACxTU+3IoGYfsbYAA0fIItCAElASQBIgIVBAkowkHbmHwwzBEBIwHfAJ5HN4w9CQAAAAAAAAAAAOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIJylOifWPpdz5AMyqO3+K6jOsCK8s8B/nezTMMedkmE8XKJJZDJm7FfL+GkTG1D15unq4nxgqQtLwOV4xUyvtIZZQIB4AFbASYBAd8BJwCxSABBCSznzXl3YJND94U1NSTUqilhvpOtgICMcCf/PVCN/wAnSRqYwwlePAP/Wi3JxCUsypULhcjtRM/m8o5K9T/8xdKIf3+4BgosMAAAWKan25FGzD9jbEABDEYGAwolrgFbAgt8QyFoJwQBUgEqAlG90HMTFTOIwZZSbnnd0qr8w9lbNkX3ED8Dk6Ay5T65VRi03nAZi03nQAFIASsDt3Nw2CD6mrWZoCVm88JptfiBC+sg8846r91j06ngkP1IEAACxTU+3IlAFTNCR5FqpdKPeM3nQnciB33JhqT+zLU6ZpMgnPAuOtAAAsPgX8ESFmH7G2AAtIDQMp4IATABLwEsAh0E+TMlSS2IjNqYgKv45xEBLgEtAG/Jqj50TPQEjAAAAAAADAACAAAAC4BygrZK2AhmlGvJjIYGdaXIyWad7kqwFvGz3C+IQ+UGRZDvJACgYCwGbD0JAAAAAAAAAAAGUwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgnLq+roIZmf7T7Wumtta1eBQF21t1Db3Eqcf7qS4UcR85zO/cd04WeVehI6DaBo7+VIArPogUUw8g6MuPc/pzy1eAgHgAUkBMQIB2QE0ATIBAdQBMwGN4AG4bBB9TVrM0BKzeeE02vxAhfWQeecdV+6x6dTwSH6kCAAAWKan25EyzD9jbCZ8doEAAAABQAAAAAAAAAAAAAVSjmTrBaACsgIBIAE9ATUCASABOgE2AQEgATcBsWgAbhsEH1NWszQErN54TTa/ECF9ZB55x1X7rHp1PBIfqQMAD/OQrrktmhcwGBNv5dpCGCRJtHVZouWCYQFlAhJyZwXStbumWAYe37YAAFimp9uRMMw/Y2zAATgDmxrtSF4AAAAAAAAAAAAAAAmJZv9QgBOkjUxhhK8eAf+tFuTiEpZlSoXC5HaiZ/N5RyV6n/5i4AAAAAAAAAAAAAAAAL68IAAAAAAoAAAAZAHpATkBYAIDz8ABUQGrAQEgATsBr0gAbhsEH1NWszQErN54TTa/ECF9ZB55x1X7rHp1PBIfqQMAJ0kamMMJXjwD/1otycQlLMqVC4XI7UTP5vKOSvU//MXOYloEBhAX1AAAWKan25EuzD9jbMABPAB5BONBUAAFPtMeipUOQAAAAAAAAAAAAAACZr4pvoAAAAAAAAAAAAAAAAHYH1uAAAAAAAAAAAAAAAJiWb/UIAIBIAFAAT4BASABPwDt4AG4bBB9TVrM0BKzeeE02vxAhfWQeecdV+6x6dTwSH6kCAAAWKan25EszD9jbDoE5tKzD9jbAAAAAAAAAAAAAAAAAhKW0GlvHQ3rw3YUp2sToZ4CQz6AAAAAAAAAAAAAAAABU8o4YQ0f+3qi2vXc93M9eVA5EMABASABQQFd4AG4bBB9TVrM0BKzeeE02vxAhfWQeecdV+6x6dTwSH6kCAAAWKan25EqzD9jbMABQgFLUByKp4ATpI1MYYSvHgH/rRbk4hKWZUqFwuR2omfzeUclep/+YvABQwFDgBOkjUxhhK8eAf+tFuTiEpZlSoXC5HaiZ/N5RyV6n/5i8AFEAWOACaRk5YTviNc+uF8d6acswWYjgw8cjcatSV0KjZ9OwgbgAAAAAAAAAAAAAAEzXxTfUAFFAWuAFJOanCsVNCqqvMSOs8XJzs2kTAFvABsSPI3yUj4IlSegAAAAAAAAAAAAAAExLN/qAAAAADgBRgED0EABRwGDgAmkZOWE74jXPrhfHemnLMFmI4MPHI3GrUldCo2fTsIG4AAAAAAAAAAAAAAAAOwPrcAAAAAAAAAAAAAAAAAAAAAQAb0BDEYGAxabzgFJAbFoAcGjFl78GARk6eksUQYnFbiocj7KUzs9MLsx9liJNCgHAA3DYIPqatZmgJWbzwmm1+IEL6yDzzjqv3WPTqeCQ/UgUtiIzagGLTecAABYpqfbkSTMP2NswAFKAo80VONFAAU+0x6KlQ4AAAAMAQAAAAKCQATSMnLCd8Rrn1wvjvTTlmCzEcGHjkbjVqSuhUbPp2EDcAAAAAAAAAAAAAAAma+Kb6gBTwFLAUOAE6SNTGGErx4B/60W5OISlmVKhcLkdqJn83lHJXqf/mLwAUwBQ4ATpI1MYYSvHgH/rRbk4hKWZUqFwuR2omfzeUclep/+YvABTQFDgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEAFOA2OAE6SNTGGErx4B/60W5OISlmVKhcLkdqJn83lHJXqf/mLgAAAAAAAAAAAAAAAAvrwgBAHbAekB6QIDz8ABUQFQAEMgBk/2AB0Qj788sABWKFpYnYkxXjcvEWPzOJ03q57/yFhsAEMgAmkZOWE74jXPrhfHemnLMFmI4MPHI3GrUldCo2fTsIG8AlG90uF0ipWQpF62n9qq3TW6GKZMtCD6ytrZc2+v7L29LhhWYsgZhWYswAHEAVMDt3z8hXv3iemRkDwnOmjp1aEPT5ZH15+2afmoq5ai62iUsAACxTU+3InWTepmYbHDAd0iO0iF5oQGe2LxEJm63DUOeFbeTI5wUcAAAsU1PtyJRmH7G2AAVIA1rFcoAVgBVwFUAhcMCSrkp8mYgCdHLREBVgFVAHHKAKy+qE3MpUQAAAAAAAYAAgAAAAR9ItY5SzxWUOdP1eMHUW5ze0S3PTeqB1xU88wYjskcBlrULJwAnkoOLD0JAAAAAAAAAAABMwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgnJ/AJ/7sTnA7SqbZ4Q0wwrfpqtai+d1zaFq9Frk22F5qK++dV2XZrPzn2z/xzwvzPNTVeiTNieU2W15J2WA9eBzAgHgAcUBWQIB3QFdAVoBASABWwGxaAGfkK9+8T0yMgeE500dOrQh6fLI+vP2zT81FXLUXW0SlwAIISWc+a8u7BJofvCmpqSalUUsN9J1sBARjgT/56oRv9KMJB24BhRLXAAAWKan25E+zD9jbMABXAFrZ6C5XwAAAAAAAAAAAAAACYlm/1CAB/nIV1yWzQuYDAm38u0hDBIk2jqs0XLBMICygQk5M4LwAegBASABXgKxaAGfkK9+8T0yMgeE500dOrQh6fLI+vP2zT81FXLUXW0SlwAIISWc+a8u7BJofvCmpqSalUUsN9J1sBARjgT/56oRv9AX14QAB7hcogAAWKan25E8zD9jbeABpgFfAlMVoDj7AAAAAYAH+chXXJbNC5gMCbfy7SEMEiTaOqzRcsEwgLKBCTkzgvABYQFgAEOAE6SNTGGErx4B/60W5OISlmVKhcLkdqJn83lHJXqf/mLwAgaK2zUBwwFiBCSK7VMg4wMgwP/jAiDA/uMC8gsBoAFkAWMB6QO+7UTQ10nDAfhmifhpIds80wABjhqBAgDXGCD5AQHTAAGU0/8DAZMC+ELi+RDyqJXTAAHyeuLTPwH4QyG58rQg+COBA+iogggbd0CgufK0+GPTHwH4I7zyudMfAds88jwBvQFwAWUEfO1E0NdJwwH4ZiLQ0wP6QDD4aak4APhEf29xggiYloBvcm1vc3BvdPhk4wIhxwDjAiHXDR/yvCHjAwHbPPI8AZ0BvgG+AWUCKCCCEGeguV+74wIgghB9b/JUu+MCAXIBZgM8IIIQaLVfP7rjAiCCEHPiIUO64wIgghB9b/JUuuMCAW8BaQFnAzYw+Eby4Ez4Qm7jACGT1NHQ3vpA0ds8MNs88gABnwFoAaMAaPhL+EnHBfLj6PhL+E34SnDIz4WAygBzz0DOcc8LblUgyM+QU/a2gssfzgHIzs3NyYBA+wADTjD4RvLgTPhCbuMAIZPU0dDe03/6QNN/1NHQ+kDSANTR2zww2zzyAAGfAWoBowRu+Ev4SccF8uPoJcIA8uQaJfhMu/LkJCT6Qm8T1wv/wwAl+EvHBbOw8uQG2zxw+wJVA9s8iSXCAAGkAY0BvQFrAZqOgJwh+QDIz4oAQMv/ydDiMfhMJ6G1f/hsVSEC+EtVBlUEf8jPhYDKAHPPQM5xzwtuVUDIz5GeguV+y3/OVSDIzsoAzM3NyYEAgPsAWwFsAQpUcVTbPAFtArj4S/hN+EGIyM+OK2zWzM7JVQQg+QD4KPpCbxLIz4ZAygfL/8nQBibIz4WIzgH6AovQAAAAAAAAAAAAAAAAB88WIds8zM+DVTDIz5BWgOPuzMsfzgHIzs3NyXH7AAHDAW4ANNDSAAGT0gQx3tIAAZPSATHe9AT0BPQE0V8DARww+EJu4wD4RvJz0fLAZAFwAhbtRNDXScIBjoDjDQFxAZ8DZnDtRND0BXEhgED0Do6A33IigED0Do6A33AgiPhu+G34bPhr+GqAQPQO8r3XC//4YnD4YwG8AbwB6QRQIIIQDwJYqrvjAiCCECDrx2274wIgghBGqdfsu+MCIIIQZ6C5X7vjAgGQAYUBfAFzBFAgghBJaVh/uuMCIIIQViVIrbrjAiCCEGZdzp+64wIgghBnoLlfuuMCAXoBeAF2AXQDSjD4RvLgTPhCbuMAIZPU0dDe03/6QNTR0PpA0gDU0ds8MNs88gABnwF1AaMC5PhJJNs8+QDIz4oAQMv/ydDHBfLkTNs8cvsC+EwloLV/+GwBjjVTAfhJU1b4SvhLcMjPhYDKAHPPQM5xzwtuVVDIz5HDYn8mzst/VTDIzlUgyM5ZyM7Mzc3NzZohyM+FCM6Ab89A4smBAICmArUH+wBfBAGNAaQD7DD4RvLgTPhCbuMA0x/4RFhvdfhk0ds8IY4lI9DTAfpAMDHIz4cgzo0EAAAAAAAAAAAAAAAADmXc6fjPFszJcI4u+EQgbxMhbxL4SVUCbxHIcs9AygBzz0DOAfoC9ACAas9A+ERvFc8LH8zJ+ERvFOL7AOMA8gABnwF3AZsBNPhEcG9ygEBvdHBvcfhk+EGIyM+OK2zWzM7JAcMDRjD4RvLgTPhCbuMAIZPU0dDe03/6QNTR0PpA1NHbPDDbPPIAAZ8BeQGjARb4S/hJxwXy4+jbPAGVA/Aw+Eby4Ez4Qm7jANMf+ERYb3X4ZNHbPCGOJiPQ0wH6QDAxyM+HIM6NBAAAAAAAAAAAAAAAAAyWlYf4zxbLf8lwji/4RCBvEyFvEvhJVQJvEchyz0DKAHPPQM4B+gL0AIBqz0D4RG8Vzwsfy3/J+ERvFOL7AOMA8gABnwF7AZsAIPhEcG9ygEBvdHBvcfhk+EwEUCCCEDIE7Cm64wIgghBDhPKYuuMCIIIQRFdChLrjAiCCEEap1+y64wIBgwGBAX8BfQNKMPhG8uBM+EJu4wAhk9TR0N7Tf/pA1NHQ+kDSANTR2zww2zzyAAGfAX4BowHM+Ev4SccF8uPoJMIA8uQaJPhMu/LkJCP6Qm8T1wv/wwAk+CjHBbOw8uQG2zxw+wL4TCWhtX/4bAL4S1UTf8jPhYDKAHPPQM5xzwtuVUDIz5GeguV+y3/OVSDIzsoAzM3NyYEAgPsAAaQD4jD4RvLgTPhCbuMA0x/4RFhvdfhk0ds8IY4dI9DTAfpAMDHIz4cgznHPC2EByM+TEV0KEs7NyXCOMfhEIG8TIW8S+ElVAm8RyHLPQMoAc89AzgH6AvQAcc8LaQHI+ERvFc8LH87NyfhEbxTi+wDjAPIAAZ8BgAGbACD4RHBvcoBAb3Rwb3H4ZPhKA0Aw+Eby4Ez4Qm7jACGT1NHQ3tN/+kDSANTR2zww2zzyAAGfAYIBowHw+Er4SccF8uPy2zxy+wL4TCSgtX/4bAGOMlRwEvhK+EtwyM+FgMoAc89AznHPC25VMMjPkep7eK7Oy39ZyM7Mzc3JgQCApgK1B/sAjigh+kJvE9cL/8MAIvgoxwWzsI4UIcjPhQjOgG/PQMmBAICmArUH+wDe4l8DAaQD9DD4RvLgTPhCbuMA0x/4RFhvdfhk0x/R2zwhjiYj0NMB+kAwMcjPhyDOjQQAAAAAAAAAAAAAAAALIE7CmM8WygDJcI4v+EQgbxMhbxL4SVUCbxHIcs9AygBzz0DOAfoC9ACAas9A+ERvFc8LH8oAyfhEbxTi+wDjAPIAAZ8BhAGbAJr4RHBvcoBAb3Rwb3H4ZCCCEDIE7Cm6IYIQT0efo7oighAqSsQ+uiOCEFYlSK26JIIQDC/yDbolghB+3B03ulUFghAPAliqurGxsbGxsQRQIIIQEzKpMbrjAiCCEBWgOPu64wIgghAfATKRuuMCIIIQIOvHbbrjAgGOAYoBiAGGAzQw+Eby4Ez4Qm7jACGT1NHQ3vpA0ds84wDyAAGfAYcBmwFC+Ev4SccF8uPo2zxw+wLIz4UIzoBvz0DJgQCApgK1B/sAAaUD4jD4RvLgTPhCbuMA0x/4RFhvdfhk0ds8IY4dI9DTAfpAMDHIz4cgznHPC2EByM+SfATKRs7NyXCOMfhEIG8TIW8S+ElVAm8RyHLPQMoAc89AzgH6AvQAcc8LaQHI+ERvFc8LH87NyfhEbxTi+wDjAPIAAZ8BiQGbACD4RHBvcoBAb3Rwb3H4ZPhLA0ww+Eby4Ez4Qm7jACGW1NMf1NHQk9TTH+L6QNTR0PpA0ds84wDyAAGfAYsBmwJ4+En4SscFII6A3/LgZNs8cPsCIPpCbxPXC//DACH4KMcFs7COFCDIz4UIzoBvz0DJgQCApgK1B/sA3l8EAYwBpAEmMCHbPPkAyM+KAEDL/8nQ+EnHBQGNAFRwyMv/cG2AQPRD+EpxWIBA9BYBcliAQPQWyPQAyfhOyM+EgPQA9ADPgckD8DD4RvLgTPhCbuMA0x/4RFhvdfhk0ds8IY4mI9DTAfpAMDHIz4cgzo0EAAAAAAAAAAAAAAAACTMqkxjPFssfyXCOL/hEIG8TIW8S+ElVAm8RyHLPQMoAc89AzgH6AvQAgGrPQPhEbxXPCx/LH8n4RG8U4vsA4wDyAAGfAY8BmwAg+ERwb3KAQG90cG9x+GT4TQRMIIIIhX76uuMCIIILNpGZuuMCIIIQDC/yDbrjAiCCEA8CWKq64wIBmgGWAZMBkQM2MPhG8uBM+EJu4wAhk9TR0N76QNHbPDDbPPIAAZ8BkgGjAEL4S/hJxwXy4+j4TPLULsjPhQjOgG/PQMmBAICmILUH+wADRjD4RvLgTPhCbuMAIZPU0dDe03/6QNTR0PpA1NHbPDDbPPIAAZ8BlAGjARb4SvhJxwXy4/LbPAGVAZojwgDy5Boj+Ey78uQk2zxw+wL4TCShtX/4bAL4S1UD+Ep/yM+FgMoAc89AznHPC25VQMjPkGStRsbLf85VIMjOWcjOzM3NzcmBAID7AAGkA0Qw+Eby4Ez4Qm7jACGW1NMf1NHQk9TTH+L6QNHbPDDbPPIAAZ8BlwGjAij4SvhJxwXy4/L4TSK6joCOgOJfAwGZAZgBcvhKyM74SwHO+EwBy3/4TQHLH1Igyx9SEM74TgHMI/sEI9Agizits1jHBZPXTdDe10zQ7R7tU8nbPAG1ATLbPHD7AiDIz4UIzoBvz0DJgQCApgK1B/sAAaQD7DD4RvLgTPhCbuMA0x/4RFhvdfhk0ds8IY4lI9DTAfpAMDHIz4cgzo0EAAAAAAAAAAAAAAAACAhX76jPFszJcI4u+EQgbxMhbxL4SVUCbxHIcs9AygBzz0DOAfoC9ACAas9A+ERvFc8LH8zJ+ERvFOL7AOMA8gABnwGcAZsAKO1E0NP/0z8x+ENYyMv/yz/Oye1UACD4RHBvcoBAb3Rwb3H4ZPhOA7wh1h8x+Eby4Ez4Qm7jANs8cvsCINMfMiCCEGeguV+6jj0h038z+EwhoLV/+Gz4SQH4SvhLcMjPhYDKAHPPQM5xzwtuVSDIz5CfQjemzst/AcjOzc3JgQCApgK1B/sAAZ8BpAGeAYyOQCCCEBkrUbG6jjUh038z+EwhoLV/+Gz4SvhLcMjPhYDKAHPPQM5xzwtuWcjPkHDKgrbOy3/NyYEAgKYCtQf7AN7iW9s8AaMASu1E0NP/0z/TADH6QNTR0PpA03/TH9TR+G74bfhs+Gv4avhj+GICCvSkIPShAaEBwAQsoAAAAALbPHL7Aon4aon4a3D4bHD4bQGkAb0BvQGiA6aI+G6JAdAg+kD6QNN/0x/TH/pAN15A+Gr4a/hsMPhtMtQw+G4g+kJvE9cL/8MAIfgoxwWzsI4UIMjPhQjOgG/PQMmBAICmArUH+wDeMNs8+A/yAAHpAb0BowBG+E74TfhM+Ev4SvhD+ELIy//LP8+DzlUwyM7Lf8sfzM3J7VQBHvgnbxBopv5gobV/2zy2CQGlAAyCEAX14QACATQBrQGnAQHAAagCA8+gAaoBqQBDSAE6SNTGGErx4B/60W5OISlmVKhcLkdqJn83lHJXqf/mLwIBIAGsAasAQyAFJOanCsVNCqqvMSOs8XJzs2kTAFvABsSPI3yUj4IlSewAQQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIAIGits1AcMBrgQkiu1TIOMDIMD/4wIgwP7jAvILAb8BsAGvAekDiu1E0NdJwwH4Zon4aSHbPNMAAZ+BAgDXGCD5AVj4QvkQ8qje0z8B+EMhufK0IPgjgQPoqIIIG3dAoLnytPhj0x8B2zzyPAG9AbkBsQNS7UTQ10nDAfhmItDTA/pAMPhpqTgA3CHHAOMCIdcNH/K8IeMDAds88jwBvgG+AbEBFCCCEBWgOPu64wIBsgSQMPhCbuMA+EbycyGW1NMf1NHQk9TTH+L6QNTR0PpA0fhJ+ErHBSCOgN+OgI4UIMjPhQjOgG/PQMmBAICmILUH+wDiXwTbPPIAAbkBtgGzAcIBCF0i2zwBtAJ8+ErIzvhLAc5wAct/cAHLHxLLH874QYjIz44rbNbMzskBzCH7BAHQIIs4rbNYxwWT103Q3tdM0O0e7VPJ2zwBwwG1AATwAgEeMCH6Qm8T1wv/wwAgjoDeAbcBEDAh2zz4SccFAbgBfnDIy/9wbYBA9EP4SnFYgED0FgFyWIBA9BbI9ADJ+EGIyM+OK2zWzM7JyM+EgPQA9ADPgcn5AMjPigBAy//J0AHDAhbtRNDXScIBjoDjDQG7AboANO1E0NP/0z/TADH6QNTR0PpA0fhr+Gr4Y/hiAlRw7UTQ9AVxIYBA9A6OgN9yIoBA9A6OgN/4a/hqgED0DvK91wv/+GJw+GMBvAG8AQKJAb0AQ4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABAACvhG8uBMAgr0pCD0oQHBAcAAFHNvbCAwLjU3LjEBGKAAAAACMNs8+A/yAAHCACz4SvhD+ELIy//LP8+DzvhLyM7Nye1UAAwg+GHtHtkBDEYGAwrMWQHFAbFIAH+chXXJbNC5gMCbfy7SEMEiTaOqzRcsEwgLKBCTkzgvADPyFe/eJ6ZGQPCc6aOnVoQ9PlkfXn7Zp+airlqLraJS0q5KfJgGFZiyAABYpqfbkTbMP2NswAHGAYtz4iFDAAAAAAAAAAAAAAAJiWb/UIATpI1MYYSvHgH/rRbk4hKWZUqFwuR2omfzeUclep/+YuAAAAAAAAAAAAAAAAC+vCAQAegCCQxr/hAQAdwByAJRv0VLO8cnW8HjN5x32lzPlOP7ol+tfferc1b2Q76nEHwoYhs6wGYhs60B1QHJA7d67seWrUiv91cxtLs3wLqZLRTw/EJH8mdCu+CL3+pJlDAAAsU1PtyIVP6HQaKE9CNmnU5A3xCcyqCVYi3XVY8mVlxmpeiaq/gQAALFMObgkOZh+xtgADSAImvJiAHOAc0BygIbBIvuSTV3lxVYgCEckBEBzAHLAG/Jj28sTCkoTAAAAAAABAACAAAAAoOWy1PZEYfxJtqiUlp1dNT39pp+kEErSPKimoH3J6pUQhBfXACeSHoMPQkAAAAAAAAAAAD7AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACCcmuTwl2Vf2je28OBaU4GqjuyGgv3C5QbXJD2to7GUdqO3XnGsw0h93+EDD/zeYApW6q8Y9fqzDNjq4ppopyFy8gCAeAB1gHPAQHfAdABsUgBXdjy1akV/urmNpdm+BdTJaKeH4hI/kzoV3wRe/1JMocAJORcVyzL4Y9lH2ty22FQH+cnRoOWjg2d79sBPN/x/qATUtpl9AYpKIoAAFimp9uRDMw/Y2zAAdEBa3DYn8mAFJOanCsVNCqqvMSOs8XJzs2kTAFvABsSPI3yUj4IlSegAAAAAAAAAAAAAAElkoryEAHSAUOAE6SNTGGErx4B/60W5OISlmVKhcLkdqJn83lHJXqf/mLwAdMBQ4AEEJLOfNeXdgk0P3hTU1JNSqKWG+k62AgIxwJ/89UI3/AB1AFDgBOkjUxhhK8eAf+tFuTiEpZlSoXC5HaiZ/N5RyV6n/5i8AHZAQxGBgMQ2dYB1gGxaABBCSznzXl3YJND94U1NSTUqilhvpOtgICMcCf/PVCN/wArux5atSK/3VzG0uzfAupktFPD8QkfyZ0K74Ivf6kmUNNXeXFUBiGzrAAAWKan25EIzD9jbMAB1wFrZ6C5XwAAAAAAAAAAAAAACSyUV5CAE6SNTGGErx4B/60W5OISlmVKhcLkdqJn83lHJXqf/mLwAdgBQ4ATpI1MYYSvHgH/rRbk4hKWZUqFwuR2omfzeUclep/+YvgB2QGVBAAFPtMeipUOAAAAAAAAAAAAAAAABfXhAAAAAAAABUU/PZv8KRgyUy6ACaRk5YTviNc+uF8d6acswWYjgw8cjcatSV0KjZ9OwgbwAdoBYwAAAAAAAAAAAAAACZY9hrqAFJOanCsVNCqqvMSOs8XJzs2kTAFvABsSPI3yUj4IlSewAdsAIAAAAAAAAAAAAAAACYS0hk8CUb9qeP/y8yTTbtFvEA5vtbTYCf+8VjnMzgluZRWR0kzzhGFEtcBmFEtdAeUB3QO1fPyFe/eJ6ZGQPCc6aOnVoQ9PlkfXn7Zp+airlqLraJSwAALFNT7ciU0ApGrwoe1EjGnAidIqVMFjyJLrYSOiTs56gdGV99rxQAACxTTvtN3WYfsbYAA0fIKY6AHiAeEB3gIZBIDXyQK4cJMYfDDMEQHgAd8Ab8mD0JBMCiwgAAAAAAAEAAIAAAACSapNoNV/whtdCnwbAysfJf+JKCa3f6xrFcQVtSeLCAJAUBYMAJ5HN4wLJJwAAAAAAAAAAOAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIJyaTiXJEJwMa6YbFdDH5RK8918dEGfUOCHTMqr1SVCEGt/AJ/7sTnA7SqbZ4Q0wwrfpqtai+d1zaFq9Frk22F5qAIB4AHmAeMBAd8B5ACxSAGfkK9+8T0yMgeE500dOrQh6fLI+vP2zT81FXLUXW0SlwAnSRqYwwlePAP/Wi3JxCUsypULhcjtRM/m8o5K9T/8xdAn4l20BgosMAAAWKan25EqzD9jbEABDEYGAwolrgHmAbFoAV3Y8tWpFf7q5jaXZvgXUyWinh+ISP5M6Fd8EXv9STKHADPyFe/eJ6ZGQPCc6aOnVoQ9PlkfXn7Zp+airlqLraJS0CuHCTAGFEtcAABYpqfbkR7MP2NswAHnAWtnoLlfAAAAAAAAAAAAAAAJLJRXkIASci4rlmXwx7KPtbltsKgP85OjQctHBs737YCeb/j/UBAB6AFDgBOkjUxhhK8eAf+tFuTiEpZlSoXC5HaiZ/N5RyV6n/5i6AHpAAAKigQyAtZttTDTA5SrTjl2tdfRAk9p3PPDim1pps3Q2PV4yBjMZrallkxHQ7zx7I+ps8lRF/JT1aq9aCMT4cXYXd6LAhkCGQLTAesjW5Ajr+IAAAAqAAAAAAAAAAAAAAAAAAK2W8gAAAAAZh+xtgAALFNT7cinAj0L+SAC0QHtAewA2QAAAAAAAAAA//////////+BBH6NQz8rnfPTUEAROTsFkAACxTU89EBQI9C/n77hk+fbGEAuR2DvKgLh843ccv+r2e8BAcHpJdeZaqJFeT/ntPdJKSSngbCID5uXhR/57K3HQnen5a9kB5KTD+ghE4IEEfo1DPyud9AB7iITAQII/RqGflc76AKCAe8iEwEATykNzg3ceYgCJwHwIhMBACF+V8PtfxAIAhIB8SIRAPKkNSwQrWGoAfIC2iIRAOkBK/lbAd1IAfMC3CIRAORJEL7lDeOIAfQC3iIRAOOG4XU4w0xIAfUC4CIRAOLsmit387PoAfYC4iIRAOBIj+EYof6oAwsB9yIPAMcjMUSTs8gDCgH4Ig8Aw2y/3fh9CAH5AuYiDQCmHuFc16gDCQH6Ig0Ao+/mGwJIAfsC6SINAKJY70ViKAH8AusiDQChAc3ljsgB/QLtIg0AoKwTje9IAwgB/iINAKCAaD4IqAMHAf8iDQCggEplS0gCAALxIg0AoIARErJoAgEC8yILQCPgtnFiAwYCAiGXutl78GARk6eksUQYnFbiocj7KUzs9MLsx9liJNCgGBDuaygA0PBukc17cwnr8SjPPrLIrIuVU9Lrw7zUXnmu5J+kgkgAAFimp9uRHQIDInPADg0YsvfgwCMnT0liiDE4rcVDkfZSmdnphdmPssRJoUA0Gc7DknzDMP2NsAAAsU1PtyJRDuaygBNABCcCBCObAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMAJw8AAAAAAAAAAAAAAAAAAAABAAAAAAAAAAAAAAAAAAAAZAPogBCYCDgIFIUOAC9auJ9U2lB50J3kjZQWb0BLG3WPNGl+WyE9zWvFLUgEQAgYhq4AN9Kb/UvW+h7YEDWt9kx1oaOlTBtgC1DIVkW8l/XCkRhAAAADAAAAAAAAAAAAAAAAAAPQkAAAAAAAAAAAAAAAAAAAAu4AAAAAAAAAAAAAAAAAAAAAIAgciYwAAAAAAAAAAAAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAGAwACCCIB4AL/AgkiAc0CCgL9AQlQAAAALAILAgPPwAINAgwAIQAAAAAAK3bLbGd3yCAV7CHgACEAAAAAAAAAAAAAAEzjnhBEYCIDfmYDBQIPIgLEAhECEACHqfY2wAAAAAAAAAAAAAAAAAAAAAAAABCkFT9yefuc7Q9vTb5AAAAAAAAAAoTaaVsujSJROMDAJWLSFKa+WUuanben8VAiASADBAMDIhEA7toil9zRrmgCEwMNIhEA4yu8UAhSF8gDLgIUIhEA4foYZJXIbIgDLQIVIhEA4G41CPV4bMgDLAIWIhEA4D1q10cJxugDKwIXIg8A3d/tSAlkSAMqAhgiDwDJyd99xspIAykCGSIPAMAzoqUCTsgCGgMVIg8AwCeAQNiBqAIbAxciDwDAIuYFpdLIAygCHCINAL9n8JabiAIdAxoiDQCgcfAsAegCHgMcIg0AoE1COwEIAh8DHiINAKAh25UfaAIgAyAiCwCfMfioqAMnAiEiCwCe8MyqKAIiAyMiCwCe8MyqKAMmAiMhmLse/eJ6ZGQPCc6aOnVoQ9PlkfXn7Zp+airlqLraJSwIC+vCAMAYbkXYBP3svBxHsL/ERiM7C8i2LHgddaq6b6ni8j8gAAAsU1PtyJ0CJCJzwAz8hXv3iemRkDwnOmjp1aEPT5ZH15+2afmoq5ai62iUtAKewFY6wzD9jbAAALFNT7cigQF9eEATQARPAiUhkwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADACknNThWKmhVVXmJHWeLk52bSJgC3gA2JHkb5KR8ESpPYAiYha4AH+chXXJbNC5gMCbfy7SEMEiTaOqzRcsEwgLKBCTkzguAAAAAAAAAAAAydX7BzPwggAAAAMAROIhMBAC2qtgogXWmIAjwCKCITAQAiFMljR5EVKAIpAzEiEQDjRwjtIosWqANWAioiEQDhA2xQT09g6ANVAisiEQDgXy2F9cDSKANUAiwiEQDgKzijcWGbqAItAzYiDwDbAXlW58moA1MCLiIPANlfLopQV8gDUgIvIg0Aux8vvWfoA1ECMCINAKfQq6EPyAIxAzsiDQCjOvp07QgDUAIyIg0Aogqz6gMIA08CMyINAKF0krmiCAI0Az8iDQCgUk4yMugCNQNBIg0AoCKoTV3oAjYDQyILAJChF6roA04CNyILAJAJNDWIA00COCILAI6cAIKIA0wCOSILAIHc+HIoA0sCOiGXustWpFf7q5jaXZvgXUyWinh+ISP5M6Fd8EXv9STKGBA7nw5F+Sl2Vo9IKJwRF+c+UYdTTKm4nBvipeNM7LUIn+t+Za4AAFimp9uRHQI7InPACu7Hlq1Ir/dXMbS7N8C6mS0U8PxCR/JnQrvgi9/qSZQ0Ap7AVjrDMP2NsAAAsU1PtyJBA7nw5FNABE8DSiIRAOuV7KbYzFRoA8QCPSIRAOYsvYcbohzoAlICPiIRAOLpgL1hrn7IA3wCPyIRAOCnZmYkKm+IAkADWyIRAOBAjxi4LpZoA3sCQSIPANLV1dYFvIgCQgNeIg8AyB8P7NBJ6AJDA2AiDwDGYolHFHtoA3oCRCIPAMA1QZzoCMgCRQNjIg8AwDHaJNd2yAJGA2UiDwDALv7yhJpIA3kCRyIPAMArVwyY5agCSANoIg8AwCsu77nLyAJJA2oiDwDAKwn5wl2IAkoDbCIPAMAq75JgZggDeAJLIg8AwCrgQqaoCAN3AkwiDwDAKuBCpqgIAk0DcCIPUDAKuBCpqgICTgNyIZu6pjDCV48A/9aLcnEJSzKlQuFyO1Ez+byjkr1P/zFwMAq4EKmqAKAmXNCvnmVQLepTJf3N1wUif44l0Zs1JawRdQ/U65rQAACxTU+3IpYCTyJ3wAnSRqYwwlePAP/Wi3JxCUsypULhcjtRM/m8o5K9T/8xdAIEwGi/QzD9jbAAALFNT7cimYBVwIVNUBNAA3YCUAHnBV5K65vUvqyGd0F/O8qDl6QE6SQC2Awb46+Bz1ARVdkAAAGO684kToKvJXXN6l9WQzugv53lQcvSAnSSAWwGDfHXwOeoCKrsgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgIAAAAAAQEAAA4QgCUQBFoACryV1zepfVkM7oL+d5UHL0gJ0kgFsBg3x18DnqAiq7IBAiEQDjQzzJufOeKAJTA34iEQDiXHRWaH2vKAPDAlQiEQDhjeWWxJJeKAPCAlUiDwDPUz4mhLQIA8ECViIPAMW2HSVsB6gCVwODIg8AwU6RogoT6AJYA4UiDwDBJsiqWJ5IA8ACWSIPAMEigPIHEsgCWgOIIg0ApTAn8XwoAlsDiiINAKTnDkW2CAJcA4wiDQCgTB9HvkgDvwJdIg0AoEEufVCIAl4DjyINAKAm7C+h6AO+Al8iCwCHtr/jiAO9AmAiC1Ah7a/44gJhA5MiCwCHtr/jiAJiA5UiCwCHc1lACAJjA5chl7prlmXwx7KPtbltsKgP85OjQctHBs737YCeb/j/UABDuaygA4GkKGed3Q3GLj++Bg9U1ABqjHc+wCuzNZZPT183NjSoAAFimp9uRDwCZCJzwAk5FxXLMvhj2Ufa3LbYVAf5ydGg5aODZ3v2wE83/H+oBCeqxVwFwzD9jbAAALFNT7ciOQ7msoATQAQnAmUjmwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADA+gPAAAAAAAAAAAAAAAAAAAAAQAAAAAAAAAAAAAAAAAAAGQD6IAQmAm8CZiFDgAvWrifVNpQedCd5I2UFm9ASxt1jzRpflshPc1rxS1IBEAJnIauADfSm/1L1voe2BA1rfZMdaGjpUwbYAtQyFZFvJf1wpEYQAAAAwAAAAAAAAAAAAAAAAAD0JAAAAAAAAAAAAAAAAAAAALuAAAAAAAAAAAAAAAAAAAAACAJoImMAAAAAAAAAAAAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABgOjAmkiAeADogJqIgHNAmsDoAEJUAAAACwCbAIDz8ACbgJtACEAAAAAANCNv7pkCVPibfFkIAAhAAAAAAAAAAAAAAFrh3JZuKAiA35mAngCcCICxAOxAnEiASADsAJyIgEgA68CcyIBIAOuAnQiAVgDrQJ1IgFmAncCdgCFsG2AAAAAAAAAAAAAAAAAAAAAAARMLUMO2G3mACfAhWOO20AAAAAAAAAQPs48yWH8pzpjX4Iv3xTTzVpbEGvRtFxN4CIBZgOsA6siAW4CeQOzIgFYAnoDtSIBWAJ7A7ciASACfAO5IgEgAn0DuwICdwJ/An4AhbAgQAAAAAAAAAAAAAAAAAAAAAAES7GPUAT3iN7Or3Clwm1AAAAAAAAAB+W6eeuwpYnNJcuVoofxhjRfwsQyw6yhxCACAecCgQKAAIOicAAAAAAAAAAAAAAAAAAAAAAARLsY4P6j92W3aTlqJleIAAAAAAAAAH5bA8ucB7z5C+uYDqLditg6bA5z0BN9J/4Ag6GEAAAAAAAAAAAAAAAAAAAAAABEuxjFTyBYS00tuV/ykTAAAAAAAAAAflojy7lUygY/3wbtoHOkWDb0G6ZO6rEAniITAQG51Ay4cHrCaAKDA8YiEwEAUIu4kDLf1YgEUwKEIhMBAD5QyuIEnjQIAr4ChSIRAO7uTkayDpMIApgChiIRAOvy+5ZWB9kIA+0ChyIRAOMg0jUzsfWoA+wCiCIRAOGR5kLq9XhIA+sCiSIRAOBbx9TZ3RyoA+oCiiIPAM/O++O0+6gD6QKLIg8AwGaStG/saAKMA9AiDQCw5Eec2igCjQPSIg0AqiG9wI1oA+gCjiINAKRJwIV9CAPnAo8iDQCkFz6sJMgD5gKQIg0Ao8kG4UNIApED1yINAKAw4EoUCAKSA9kiCwCKzIV5KAPlApMiCwCIMhVgCAKUA9wiCwCIMhVgCAKVA94iC0Ah3NZQAgKWA+Ahl7qrrktmhcwGBNv5dpCGCRJtHVZouWCYQFlAhJyZwXAh3NZQAfW6KJiAuTLWeyg/36LoKDdXn1i+NcAF/vydcSGDDEVkAACxTU+3ImoClyJzwAP85CuuS2aFzAYE2/l2kIYJEm0dVmi5YJhAWUCEnJnBdAOQwHp2wzD9jbAAALFNT7cidQ7msoATQAPkA+MiEQDi+1KwXAa6CAQuApkiEQDiQ9vKjGFyKAQtApoiEQDhz9qw2IgxaAQsApsiEQDgOGfsIm1gyAKcA/IiDwDBBVC1aWBIAp0D9CIPAMCEzxw+wEgCngP2Ig8AwDmkDt1UCAKfA/giDQCoA9aTmOgEKwKgIg0ApbsO/uooBCoCoSINAKOv09GJaAKiA/wiDQCjbNky5WgEKQKjIgsAnkA1P2gEKAKkIgsAh3NZQAgCpQQAIgsAh3NZQAgCpgQCIgsAh3NZQAgCpwQEIgsAh3NZQAgCqAQGIgsAh3NZQAgCqQQIIZe6oPqatZmgJWbzwmm1+IEL6yDzzjqv3WPTqeCQ/UgQIdzWUANsPEftcYL7AJuQX84fMF3o4BpnD/F/t2huK+WX0c7BVAAAsU1PtyJSAqoic8ADcNgg+pq1maAlZvPCabX4gQvrIPPOOq/dY9Op4JD9SBQn4sVjvMMw/Y2wAACxTU+3ImkO5rKAE0AEJwKrI5sAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwPoDwAAAAAAAAAAAAAAAAAAAAEAAAAAAAAAAAAAAAAAAABkA+iAEJgK1AqwhQ4AL1q4n1TaUHnQneSNlBZvQEsbdY80aX5bIT3Na8UtSARACrSGrgA30pv9S9b6HtgQNa32THWho6VMG2ALUMhWRbyX9cKRGEAAAAMAAAAAAAAAAAAAAAAAA9CQAAAAAAAAAAAAAAAAAAAC7gAAAAAAAAAAAAAAAAAAAAAgCriJjAAAAAAAAAAAAAAAAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAYEFAKvIgHgBBMCsCIBzQKxBBEBCVAAAAAsArICA8/AArQCswAhAAAAAAAAAAAAAAUmExlMMqAAIQAAAAAAAAAAAAAFLfp9GF/gIgN+ZgK6ArYiAsQEGgK3IgEgArkCuACHp+xtgAAAAAAAAAAAAAAAAQlLaDS3job14bsKU7WJ0M8BIZ9AAAAAAAAAAAAAAAAAqeUcMIaP/b1RbXrue7mevKgciGAiASAEGQQYIgFYArsEHCIBIAK8BB4iAW4CvQQgIgFuBCQEIyITAQAvYnybUo+hCAK/BDAiEQDiCDCK5HlgSALABDIiEQDg1lxCfonNyALBBDQiEQDgaalHI2auiALCBDYiEQDgWPpcjySZCARSAsMiDwDVtMkAYImoAsQEOSIPAMFKCms1sWgCxQQ7Ig8AwDypGm9/aALGBD0iDwDANhfZXrgIAscEPyIPAMAyebovr+gEUQLIIg8AwDBupkl8SALJBEIiDQCgRWOIxmgCygREIgsAhNVbzcgEUALLIgsAg7f1GEgCzARHIgsAgQJBCYgCzQRJIZm7bOfNeXdgk0P3hTU1JNSqKWG+k62AgIxwJ/89UI3+BAX14QBHVDjblOujhnNCUJjypwMRLWkdFBn60UIPP/SkWb8yzIAAFimp9uRRQALOInPAAghJZz5ry7sEmh+8KampJqVRSw30nWwEBGOBP/nqhG/0Ap7AVjrDMP2NsAAAsU1PtyKRAX14QBNABE8CzyGTAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMAKSc1OFYqaFVVeYkdZ4uTnZtImALeADYkeRvkpHwRKk9gC0CFrgBOkjUxhhK8eAf+tFuTiEpZlSoXC5HaiZ/N5RyV6n/5i4AAAAAAAAAAAAAAgeNGzC8AAAAAwBE4BEQAAAAAAAAAAUALSAGuwQAAAAAAAAAABHoX8gAAWKan25FHROSDjglEXcQzQP7S13SSphQNkbMpERwPvHq0gUuySlEAjW5Ajr+IAAAAqAAAAAAAAAAAAAAAAAAK2W8cAAAAAZh+xswAALFNT3oZBAj0L+CAEVALVAtQA2QAAAAAAAAAA//////////+BBH6NRXNVQ5PTUD/hyojYkAACxTU8ABxQI9C/ggQR3MslvaMP0vYldUzFJPvaciSaGzj2yo+3/0fuCLQa3Z/eRoMiflvyXlFqmqsp5H6fi5vQq5galNmhqp/TNKghE4IEEfo1Fc1VDlAC1iITAQII/RqK5qqHKAPFAtciEwEATykN0qZkGIgDLwLYIhMBACF+V8PtfxAIAwwC2SIRAPKkNSwQrWGoAtsC2ihIAQEa+dJGyTPMuf4bwEkeiGdznAv9/1Dy/4u2/AdxHH7zHACgIhEA6QEr+VsB3UgC3QLcKEgBAZMsEPYyPHVNPU9Z8Dt4QTi9kDu21QEzu9gB7E09253LAe0iEQDkSRC+5Q3jiALfAt4oSAEBlV1vgUy3zUJNRjrL3gy7HTOGn5iQSF6P13OukbYKw2kAkiIRAOOG4XU4w0xIAuEC4ChIAQEzSJBOieBJLB+cKFtuZrWDjL6Un9kF/kZV5kn7s4ShPgCMIhEA4uyaK3fzs+gC4wLiKEgBAZFPadIJ+jxyiXCAXzRd/jr/LTaEgQQKKil957Y16NBYARciEQDgSI/hGKH+qAMLAuQiDwDHIzFEk7PIAwoC5SIPAMNsv934fQgC5wLmKEgBASHWQfs7VS85/CIbmw32OiqveU8q33hVP64G34VoWpA4ACIiDQCmHuFc16gDCQLoIg0Ao+/mGwJIAuoC6ShIAQG3djckD0rETOUckuK86w8wWRC7C7BOB8FNqE0DD4FgqAAeIg0AoljvRWIoAuwC6yhIAQGYgO+ch+VQW8H6UQ+aKTKQ/fqRTzJMGPvLT7etYEwMTwAbIg0AoQHN5Y7IAu4C7ShIAQEVxSUiKlTe3yNYLBnShuoRjC+nbexhnVQyENf6licmnAAaIg0AoKwTje9IAwgC7yINAKCAaD4IqAMHAvAiDQCggEplS0gC8gLxKEgBATmpmgB2/+M+n5CHyO4B2sNfzHfIkd1BreLxK/4gW2i+ABAiDQCggBESsmgC9ALzKEgBAcG6kt+q2KD1XYg79846FCqtQprvDhjdzqGhY54sAP8cABAiC0Aj4LZxYgMGAvUhl7rZe/BgEZOnpLFEGJxW4qHI+ylM7PTC7MfZYiTQoBgQ7msoAOkDtGafbKe6JgkS0M5+1mLJ3WE9+C4Z6z+fEGyILg/eAABX6wuB/50C9iJzwA4NGLL34MAjJ09JYogxOK3FQ5H2UpnZ6YXZj7LESaFANBnKw5H1gzB37CAAAK/WFwP/UQ7msoATQAQnAvcjmwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADACYPAAAAAAAAAAAAAAAAAAAAAQAAAAAAAAAAAAAAAAAAAGQD6IAQmAwEC+CFDgAvWrifVNpQedCd5I2UFm9ASxt1jzRpflshPc1rxS1IBEAL5IauADfSm/1L1voe2BA1rfZMdaGjpUwbYAtQyFZFvJf1wpEYQAAAAwAAAAAAAAAAAAAAAAAD0JAAAAAAAAAAAAAAAAAAAALuAAAAAAAAAAAAAAAAAAAAACAL6ImMAAAAAAAAAAAAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABgMAAvsiAeAC/wL8IgHNAv4C/ShIAQGIJDAeqr99a4LTCtcDYQ6oASXXCkv8MqhSjHwUasuyfAADKEgBAcQdVBlljHlaqEUL858WE7fo2XF44mIfSP4kNSpkzs26AAIoSAEBZa5oGoOXE/64paFLSASuEOYa2Qbka58iKPN7cae4vXQAAyhIAQE2NFJJHkgLaHDPGslX6f0kgzJvz5tCfyTksohD7GexYQADIgN+ZgMFAwIiAsUDBAMDKEgBAVpwj908gM/pi54d89cyFVP81XakNLfK4NMFO10M/sKXAAcoSAEBd2dWGNyJobnsvjLvPLKdPl1gH8cZEkn8q51ktuSAFIMAAyhIAQH5xghJ7qgePOKC26lUdn6TwRCkSoZEs3KeT2JoobhBJgAIKEgBAVca3q1wbRtoJ49kgHPmNMa60KdYTTynPdrZLsDYRTCzABIoSAEBH0th/reHJzEfW6IQU7m3GFW9yTQ06etEVL4DeDvNjN4AEChIAQER64mIKcusaLcW73Kae31TVfJzPoN0rDOyY7k0pLOI9QAXKEgBAYxI1vXAAzqWZfYgeZH2Ob9DZRcvv2kXNpVOVoN2Vkl/AB4oSAEB2EjUOdHE2SGdGknyq+kVgb5HMZzqmjTqG8qTJM7tfY8AIyhIAQGcEPP92zPrA6MGPPN6fleSGE+J5dx86zuN5dmO7VQXvwAoIhEA7toil9zRrmgDDgMNKEgBAU3/fmrI1GAQogIuB417WdTUElN9pdoqMMacYrv59c9oAe8iEQDjK7xQCFIXyAMuAw8iEQDh+hhklchsiAMtAxAiEQDgbjUI9XhsyAMsAxEiEQDgPWrXRwnG6AMrAxIiDwDd3+1ICWRIAyoDEyIPAMnJ333GykgDKQMUIg8AwDOipQJOyAMWAxUoSAEBqaloZI6YQiTbVryOvgBOEB0HpfNhbUlbOArj35OKGmwAJyIPAMAngEDYgagDGAMXKEgBAVDCSD8UJEstNZQEj90FYyGjWuFr8wRzJtTr7QLRNT6fACciDwDAIuYFpdLIAygDGSINAL9n8JabiAMbAxooSAEBOTEgbBAi6rfl+Dg8ekiutZ+NZlG1mZkgH6lx65zYX8UAHCINAKBx8CwB6AMdAxwoSAEB3HPJFHHXJYgyv/PkfU9qNlnox9HbLqdRDXjWi+AIhTsAGSINAKBNQjsBCAMfAx4oSAEB4UxmkH3U1KrkbDB7BiL319Dl+4eXo958CANEE3eHsfYAGCINAKAh25UfaAMhAyAoSAEBV4EzN2ligafdxqL3XfIWVYYg+a8+kxISilFpjlpyxCgACyILAJ8x+KioAycDIiILAJ7wzKooAyQDIyhIAQHv/caXpvh7+L/wHSCVgAH/wKlkn5hwtRI9WWrU/VQm5QACIgsAnvDMqigDJgMlKEgBAcAcFZGXFIM5LNCBxnvLxeduhxTnjy7289biDrOG8PcJAAwoSAEBfM6OKuik4AvJWlYKNxL/utH91crC3d6OKTOz7IhRgu0AEChIAQEvkbXvplAtT31Sv7oNRTVj5/32QZ65aonl2VuMXZ/ZTAAWKEgBAXlUTU5oXv3cwsoyIT9vHAmIL+ahQcUcU3Hi0bjs9qFyABwoSAEB9FLjP8Pw95UqRemdoeDouqDccXMmTLI7BsR3tjwLhYwAXyhIAQFFmrx7m0gSrbYv0UfcEbZVpMunKpTySHln9UW/Wm3n+QBNKEgBAWAkpdhA29xBEkT4J/eTRsHKQ0PdP48o1YShatky+5RVAecoSAEBkf8juFHrx6d5gWfdcEjAtOxGIWB0xSEALRWSdSkx97sAiChIAQFrtPsLUb9dew/OX1t81rPQEIwfmdXiGTW7cPERMAyYGgCLKEgBAbsLV+x4QobkBcFm70IMmVjvx2iF9lTa6/SFheM9fgRPAG0iEwEALaq2DrjlCIgDVwMwIhMBACIUyWNHlwxIAzIDMShIAQGTJxUGq/pKPh5HA70rNdWLaaEkKZVPEnfepk0DO/dyjQIFIhEA40cI7SKRDcgDVgMzIhEA4QNsUE9VWAgDVQM0IhEA4F8thfXGyUgDVAM1IhEA4Cs4o3FnksgDNwM2KEgBARRPm+ohb840+VQwkRs3AR2v0rzovTeASyPSCYbT1EpWAFsiDwDbAXlW7cDIA1MDOCIPANlfLopWTugDUgM5Ig0Aux8vw18IA1EDOiINAKfQq6cG6AM8AzsoSAEBabjftF3oAFfRRkslFkqgZPydBPuhpJ2ikfskQ4CPw3AAHyINAKM6+nrkKANQAz0iDQCiCrPv+igDTwM+Ig0AoXSSv5koA0ADPyhIAQGkJVCvk08xK+PQly0pBNdM3gHH54nzgHDK9fo0sYk0CQAcIg0AoFJOOCoIA0IDQShIAQGCfw6OSg3/spjHE+YByuk0yLTkcM7kpKMsEvkeqboDKgARIg0AoCKoU1UIA0QDQyhIAQFtDlG5IBWBR92NWyFPZ/CRDB+GC8VOcpzrSNrxMFRZvwAZIgsAkKEdoggDTgNFIgsAkAk6LKgDTQNGIgsAjpwGeagDTANHIgsAgdz+aUgDSwNIIZe6y1akV/urmNpdm+BdTJaKeH4hI/kzoV3wRe/1JMoYEDufzSif0Og0UJ6EbNOpyBviE5lUEqxFuuqx5MrLjNS9E1V/AgAAWKYc3BIdA0kic8AK7seWrUiv91cxtLs3wLqZLRTw/EJH8mdCu+CL3+pJlDQCnsBWOsMw/SvgAACxTDm4JEEDufzSk0AETwNKKEgBAQRA3SW0cmHGu0q4cTKg7RUEiH2jU5RVpZWir5pIBqQOAAooSAEBMq7odSjxvo4vc6ZqE1DXBrqtsKkfUIe2HIJp3tENIKoAByhIAQHe5CTXwcdx5MeMT0kaqVk8t65HZzwZzUn53hfzNCLY3wAPKEgBATuFLJwhOZHfj6TJ1d1VmePk3jKLCYFr2/JoUpsizXZSAAsoSAEBLTmQtrfFqMot6XOkBb3n+3siw4k+g7NnlXWNDuTEBj4ADyhIAQGcwKoY3r/Lnea7ZQfH7NmdEYwtiODptCgz7dM0Z5eIigAdKEgBAbWOLTCDWPt6Yj11/uIKYZVv+uloLkUpPDeRy3z3V+OjABwoSAEBdsChWLk4sIp8NggNO4h2okAH3oug9Tr4FMd9UO5FEk0AVihIAQGq7OPqvefp6tUtHSRoGMXEi+ISABBYx/bKjHJlRdMTqgAiKEgBAc2AJg4QIlieZiS6XdrDvalENH/mqMxZAq7jgM2F8EVqAC0oSAEBMmuHi2StJmE0uwz7gmezAX8/6roFdfrxtqQKkqTCTPAAaihIAQFMqr1AMO8EwyTVvS6FUlWMWAg/v/xI3AtCkCOoGjCWggBrKEgBAexg3UoVwoS2jLZEbgCArLUE6yW4yVUs3TFPsp6ZlIbqAd4iEQDrleyrcU38SAPEA1giEQDmLL2LtCPEyAN9A1kiEQDi6YDB+jAmqAN8A1oiEQDgp2ZqvKwXaANcA1soSAEB44B4YXSexzaQfrK1rfuZDmyHy4SqrTadGGX3TkUVcyEAjSIRAOBAjx1QsD5IA3sDXSIPANLV2m6HZGgDXwNeKEgBAWg+0MbS/GVCOhWkn6U3mPPlTUN4BUG+VyW30bShj1XXAJIiDwDIHxSFUfHIA2EDYChIAQHlpe/2/QjOj3T8LkYBSvzPvdHPwJovGcqkNIb3GxRRwAAvIg8AxmKN35YjSAN6A2IiDwDANUY1abCoA2QDYyhIAQFCQE6cpjszrNzCio2nb7Nl0gB4sZ506XFamoWRhJy5jgAlIg8AwDHevVkeqANmA2UoSAEBY3hkYyVf7ne3SglI2kWuS1cpF4k4wZ2meWBqeknmKh4AHiIPAMAvA4sGQigDeQNnIg8AwCtbpRqNiANpA2goSAEBRHPFtAvEAZS7Wm/Imn4+C8R4eH29MLSPx1QJEtI6nw4AGiIPAMArM4g7c6gDawNqKEgBAcULb1bGO70GYkX3X2nG15Mrwkd2N0qRtfD0VD00NBWDABYiDwDAKw6SRAVoA20DbChIAQF9gQedsTd+zWcpEWHTDOrA4OMdgkpfy/fXAXQthFqM4wAXIg8AwCr0KuIN6AN4A24iDwDAKuTbKE/oA3cDbyIPAMAq5NsoT+gDcQNwKEgBAXHvw3TwDa1l4MsBV48nGtpCVV83+5xXJ8nWv4VyN7sLAAwiD1AwCrk2yhP6A3MDcihIAQGmH5547f7gaNQeT52X5IieYnV5g3ZF/BiHYVsAuNeJDQAGIZu6pjDCV48A/9aLcnEJSzKlQuFyO1Ez+byjkr1P/zFwMAq5NsoT+NrRrLN7A8G1uueG9cvvAQWzNI4Ngl1zjYHHWoklIsvIAACxTTvtN5YDdCJ3wAnSRqYwwlePAP/Wi3JxCUsypULhcjtRM/m8o5K9T/8xdAIEwGi/QzD9hsgAALFNO+03mYBVybZQn9NAA3YDdShIAQFM2YkNfzGgsIjo/R4Y7A9T9wNykG8DZ3qkQK/HamYynAABKEgBAdZtGYdmq9vhJT80FYJslGw3H1ESVSQIYlrrCzHg7y3zAAooSAEBwGPg1A2bddMmZfFOWbunVRyYHF8jvCR22oDacF2ocyIADShIAQF1fOK8FVd42iXe5oS1f213PVJEHRNGgKYOjZe6fBij4QAXKEgBARyLc6wQfj3fBYftzJfHTGKS2rVt9JbGBgJBOFXQpGnbABwoSAEBM5qWY+SeCFqPACGtFtgDpdcm9gm47FWSyyvUMX9wQtYAcShIAQE3slhecXoI0J8uXJiSdG29HOnOcBEYU8UqHZ3VBxWs8gBYKEgBATutVkRE2bnL9qL5Koi2h0Sz+dJylMQkjaTC6vwvCMvgAFAiEQDjQzzJufOeKAN/A34oSAEBgUHLXminlHrgx1fvVIhkfCLL1S4bfDB5nVoyOnHdMdQCESIRAOJcdFZofa8oA8MDgCIRAOGN5ZbEkl4oA8IDgSIPAM9TPiaEtAgDwQOCIg8AxbYdJWwHqAOEA4MoSAEBMO/DRhUH5bNf3aUkCrVhgh2ii7WThgGj0gDGB9bb2jcAKCIPAMFOkaIKE+gDhgOFKEgBAeXKIPzuEIyW3bNSKaGhHZTlgxV84p0LJWMqW18ocm1/AIQiDwDBJsiqWJ5IA8ADhyIPAMEigPIHEsgDiQOIKEgBARDKEONTlCdn/JvUt/U53kH3mKfiGLc4XbtvUx7C+VckABwiDQClMCfxfCgDiwOKKEgBAXuQ3onKQ4aV5P+cNXUKJxisGc5umneByDDjyPCuLt1CAB4iDQCk5w5FtggDjQOMKEgBAUYer1DJ3qysdg2jbN+zmQXhOmQU8Q2ZilB9NxdClBdFABkiDQCgTB9HvkgDvwOOIg0AoEEufVCIA5ADjyhIAQEIVa8IqKiepBgltB6rFVvTX6RsqD0QR6CmmLq2SkKgXAAXIg0AoCbsL6HoA74DkSILAIe2v+OIA70DkiILUCHtr/jiA5QDkyhIAQGIrZXgiHhJz9KXdGCNIx8wjetBZIaCzjnmlBWGNajtpwANIgsAh7a/44gDlgOVKEgBASfHdwG5OJTjL09z9zWrXDCok8gfu3ansPvhD1p/Hw/dAAoiCwCHc1lACAOYA5coSAEBVw3Q+f8BPCTqIkOZunUfY67gMClJVDi2y8ym0k/iiIMADyGXumuWZfDHso+1uW2wqA/zk6NBy0cGzvftgJ5v+P9QAEO5rKABEYG8i0miX3fRyRNBZuQ7zoNVXI9hoB2/BSNivlFx4tgAAWKY2m94pAOZInPACTkXFcsy+GPZR9rctthUB/nJ0aDlo4Nne/bATzf8f6gEJ6rFXAQDMP09qAAAsUxtN7xpDuaygBNABCcDmiObAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMD6A8AAAAAAAAAAAAAAAAAAAABAAAAAAAAAAAAAAAAAAAAZAPogBCYDpAObIUOAC9auJ9U2lB50J3kjZQWb0BLG3WPNGl+WyE9zWvFLUgEQA5whq4AN9Kb/UvW+h7YEDWt9kx1oaOlTBtgC1DIVkW8l/XCkRhAAAADAAAAAAAAAAAAAAAAAAPQkAAAAAAAAAAAAAAAAAAAAu4AAAAAAAAAAAAAAAAAAAAAIA50iYwAAAAAAAAAAAAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAGA6MDniIB4AOiA58iAc0DoQOgKEgBASD4f0VMV5a0d7GwQ6N+OXO+i5Wr991KldY3TwXSvDuEAAMoSAEBjX8+oQi5e1ZkVP6bKgPjh/6Hxte7v0J5GO9Ppk3dwxQAAihIAQFNiwppOD5yM83FNO82NLE3t0MqjibXQOvknmVPPq0wVwADKEgBAanE+wG+ilo7Vld4ylpaoYrCNLMCq7ILy4UCVa87bN5wAAMiA35mA7IDpSICxAOxA6YiASADsAOnIgEgA68DqCIBIAOuA6kiAVgDrQOqIgOVMAOsA6sAg6dqAAAAAAAAAAAAAAAAAAAAAAAiYWn1lqB0Fxh0bZLHuAQAAAAAAAAAger3cxFpqQXNR38n+ManNUX/U0ZkPeM8CShIAQHdG8Ae08nhXMRpMCMUgTX41h7mKO7jWp7GMDu8urvCswABAIW9u2gAAAAAAAAAAAAAAAAAAAAAAImFodrRYYUDA+fIj4w9YAAAAAAAAAIFnQjkSsHxqP1xL5KcgnNz32cvnDcirrW8KEgBAa1k17Cjf6Y/oJJPy2Lx5LPboF6/bwAue2YG43jXlLUDAAUoSAEBPwl5doUK960iYiFsf/UZmNZwDBycqobHKZaqI+xhyuYACyhIAQH6QCKJBYhFYD96fVTfbeBjYFKfTTLgdAMapm/O4zimaQAIKEgBATTK3eHpx7quJevxpMx7ZkHgyy/zGn3swKKtA3REEbhdAA4iAW4DtAOzKEgBAbT+en94cYme/j4v7fWf+wQM0IBK0QR2IJnwilu0Sgz0ABEiAVgDtgO1KEgBAaIPgJfiCr9dTlZ/wQijCuvmMZ1B3Za8Fuyw75fiA5hgAAkiAVgDuAO3KEgBATfNFhbk3BVxxzS30kVxinQmC5VDIfsxPJP/V1NkIthiAAciASADugO5KEgBAaq5DrSu9m8TljpC/gX339jDUCYTwB//04Q/WbUCSkGNAAYiASADvAO7KEgBAb25mpljz/8YLgAhbz2siG+pP9U4NurqgHEYpP77FwqXAAYoSAEBZ9QwxzI0h+iz2QLXb8CbXLKoDI74nLXA+RxVAoATBmIAAyhIAQGKXh5wfrrhMMwOFxLtSN6E4yThNKy7RroRqlHEtss+CwAOKEgBAT8oDDTtCeBaqTGM8aaLF6XlHhW8ZOC9/eLqEhEiz3zzABEoSAEBRyrIeOZBII91PNnvoMpcs+/nm/B5Dh2xdXuu0U+wjSgAGihIAQGi8/dXkKpPTO10uywDSWqaRjJJ5ML/Obwnsh6/wNrqbAAfKEgBAcLdajpzYOvft2A/5Jlue9DfMz558SUFlvqAHSxEcOVCAG0oSAEBDSB+aJoRW0DOp6UlWof1lY3/+3CStgtLzi12DF4mH1YAlChIAQEcmgRbw/T5SKjzN413lbNjALVEVI8KQmVLJTuwXLdlPQCSKEgBAab1VPsyUO/d2EC3nj9eAn/q8XKjOSPC1FhFRAW8u54UAK8iEwEBudQMuEBGbqgDxwPGKEgBAangYsT74WJ4+RtvmZ7qp/zaw+XtY6vweVdj2f/DSvlVAfIiEwEAUIu4kAKrgcgEUwPIIhMBAD5QyuHUaeBIBC8DySIRAO7uTkaB2j9IA+4DyiIRAOvy+5ZWB9kIA+0DyyIRAOMg0jUzsfWoA+wDzCIRAOGR5kLq9XhIA+sDzSIRAOBbx9TZ3RyoA+oDziIPAM/O++O0+6gD6QPPIg8AwGaStG/saAPRA9AoSAEB3PExU87o6+Kwnrl0q2qkl31ofya5K4RfEGeqfsf0BRsAIyINALDkR5zaKAPTA9IoSAEBwiRabvrwJq8GajaW0Ghfl+Y9mAOBqeLB3k0IoiGralIAIyINAKohvcCNaAPoA9QiDQCkScCFfQgD5wPVIg0ApBc+rCTIA+YD1iINAKPJBuFDSAPYA9coSAEBRTEVNe94QCWx9BmYPnS8NZ6NGijIzGjOmvl0EJNiMRoAGSINAKAw4EoUCAPaA9koSAEBgu2AijUF/jsG6un0jQ1DGAOx/lXJ8f1ni0nTr+mVQrYAFiILAIrMhXkoA+UD2yILAIgyFWAIA90D3ChIAQGeqDcN0ZuzESvbGYH+GdMFoGH5AkYEsKYh9tSgCa5CDQAQIgsAiDIVYAgD3wPeKEgBAejMTqHB0jiMVP5oM+Ai/mwBum+J0Tl7Oz0oyusbkemjAA0iC0Ah3NZQAgPhA+AoSAEBvXOoG6omRg0fQye+E5LbUFDPEYFfoR3mXq7ctEos9XoADCGXuquuS2aFzAYE2/l2kIYJEm0dVmi5YJhAWUCEnJnBcCHc1lAA/9R8PLp3QqPfOd6mMtF5vqNuMOS4yfk3uY1ZiCiVe4AAALFNO+03agPiInPAA/zkK65LZoXMBgTb+XaQhgkSbR1WaLlgmEBZQIScmcF0A5DAenbDMP2GyAAAsU077Td1DuaygBNAA+QD4yhIAQF9ObImttXsV5npSHQ7xnKg4ME4CP3jgtGRdXjxUjHUnAAJKEgBAX1vRwZY6ONvXpxhzh5JBXuUorJ0qaUfXTjB/jYkZe/sAA8oSAEB6BEjVACAelwgZsA/dnsz5SQZfNqeuwvr2E6X1LGu6NoACyhIAQGzOm1Mp/H2OvUgmn6I0rIHv6guqpAbSoOKaRHD+OO5+wAaKEgBAQw9aqVgY1nC+BNLJUEfDHLJH3LfUqKX0J0k3eOGBof/ABooSAEB8Ei0SvqTDOc/9DoKU9nUEguN93VE+mXVsjk7O6mmI+wAJChIAQGCzaXOAKAiqBVo10U3vHdN+9w12nVTz1B3RiXyjlmCbgAkKEgBAfUaWnC+1QU5uAprL6DM7dR4xJfZJXf/KlUtMZaMhLUOACkoSAEB5SxR7QlkQAT53vX1ddK1UqdOx6id3TFeyCgXl1T3kXIATShIAQEJ9YvF1sjK5XOgB2trGFJXNJJ5rNum0SQEWwcN4z0pkgBbKEgBAQ3mzGgXEFHODA6WGVMlnED84S4m8o/aWQn/w76xqMJ9AHAiEQDi+1KwK9JmSAQuA+8iEQDiQ9vKXC0eaAQtA/AiEQDhz9qwqFPdqAQsA/EiEQDgOGfr8jkNCAPzA/IoSAEBzIRK8knCul195i1kUDCvPazfjlghe8vaD8MDyGWDuTIAKiIPAMEFUIU1DIgD9QP0KEgBAUhojhcgb4FMnL21bn1zBey1kOAb5092ZWTQGhl5CkfxACQiDwDAhM7sCmyIA/cD9ihIAQHOv1p17fl8M3CzJKJE+EXk2mCWid/xrDH5FgG7tygysAAiIg8AwDmj3qkASAP5A/goSAEBC0S8dLXwdCEZw+FQWLg4ux/D2lekb5BEW7fbxBz9RVsAHyINAKgDpl9FKAQrA/oiDQClut7KlmgEKgP7Ig0Ao6+jnTWoA/0D/ChIAQHO6uqXVPcf+mr3h2YS7c0IxmqRkmEF4uc7FVfoPt/TQAAcIg0Ao2yo/pGoBCkD/iILAJ4QAOuoBCgD/yILAIdDJOxIBAEEAChIAQHBZ1ZGasfJjP/qbJPJ3enz0V2jyqFHomTL6A/nlgoF6AAHIgsAh0Mk7EgEAwQCKEgBAYeFsv0W8lKNbKcP5dRKenBidxHrBFHXYn1ioDH9Hb9EAAYiCwCHQyTsSAQFBAQoSAEBnTALpWQtvr3GXTsc23aH0PPmVaVaE8fyLwTXD0MrQF8AByILAIdDJOxIBAcEBihIAQHafXTW+A442NkyfCGXlwI2FAlB0J62OBWl+NWQsHAR7QAOIgsAh0Mk7EgECQQIKEgBAZLfjioH75Mj06L84Ng+QrZqcWYl5DMpuDpuK/1UuxYTAAwhl7qg+pq1maAlZvPCabX4gQvrIPPOOq/dY9Op4JD9SBAh0Mk7EAVM0JHkWql0o94zedCdyIHfcmGpP7MtTpmkyCc8C460AACw+BfwRIYECiJzwANw2CD6mrWZoCVm88JptfiBC+sg8846r91j06ngkP1IFCfixWO8QzDfTWAAALD4F/BEjQ6GSdiTQAQnBAsjmwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADA+gPAAAAAAAAAAAAAAAAAAAAAQAAAAAAAAAAAAAAAAAAAGQD6IAQmBBUEDCFDgAvWrifVNpQedCd5I2UFm9ASxt1jzRpflshPc1rxS1IBEAQNIauADfSm/1L1voe2BA1rfZMdaGjpUwbYAtQyFZFvJf1wpEYQAAAAwAAAAAAAAAAAAAAAAAD0JAAAAAAAAAAAAAAAAAAAALuAAAAAAAAAAAAAAAAAAAAACAQOImMAAAAAAAAAAAAAAAAAAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABgQUBA8iAeAEEwQQIgHNBBIEEShIAQFM0uQVUrXhvLgnG/t1WS0yJozW3tE//PK4As82/1Co4wADKEgBAUEz9rag2D+Nb2cSooejeX3b8glqY/bpIKlJFyXBut+IAAIoSAEB6vBU7/9uD1OQHTJczB3HpYY8jCcf8DclBkvrcPgUYFwABChIAQFCFxZFzpYLygxwH2RJCbVVOyzUZW/ix8VVyvNlN8AocgADIgN+ZgQbBBYiAsQEGgQXIgFIBBkEGACHpMUIgAAAAAAAAAAAAAAAAg17MoqXPxWRf8H/iL2oDp6t29QAAAAAAAAAAAAAAAABTr4lWwoUTeQUj994SurmO1AeUUAoSAEBqaWkk7ecaQjbfbwn10Txjue7OhNKM29OK7PCK9Kkzx8AAyhIAQFshDSWqUzb7KoVMWgS6gYcf6t4hd7CLaXAhYfuxQCWggAMIgFYBB0EHChIAQH+nX6AxgmUOP0PO34sSp3XBbJrYtcEf4sUea+2TkWOlgARIgEgBB8EHihIAQFD/HJ7KCfQIHfsr/XzCN7CFv1qwNYU4dLPx7bRA/oUhAALIgFuBCEEIChIAQGmsjryjqfbBK9o8MX1sIwXlf3lgA6FXjKWWlz5qFKEawAIIgFYBCUEIiIBIAQkBCMoSAEBUeJ0I3QrQwTDmoANrXwiIo1QAPJX2Kt5awe1UhHiikgABihIAQGIvUfJkF7dQHwPjUpToVD/NcOpGg8ySrvbCCWorj2zbAADAIajOqcAAAAAAAAAAAAAAAACpsXdd9q8dSfof6pGFcrOA00F7gAAAAAAAAAAAAAAAAIHlKsZB2nxteuJR7XMNRQJj/3TKEgBAf8voAi+vXmmn9tArteDGw88PHqB5By1JsByYPwS1T6PAAgoSAEBZLPbwQxrVWun00sG+UVlmJVpiaGybZ8lUQ51+EjQkhQAHChIAQF/Hp9XtETgfDrTnUYhiHhCfRUA4e4pxhgiZFSddqAA2QAXKEgBAdD4vaVhX0veTicv12+8EOcFAaCUBqfMryY5TuW1Vu//ABsoSAEBUP8Sl+viRCww75DhHWZP2+/W5vU7r/W32dPPqF5QymoAHShIAQGEH53zFa5nICzRPl7VKRlOqNsbOSAnQNq3VqYK/fWSHgAeKEgBARJZ6DxFW0udkp3RHcNtEEYJ28bbQqaiIJ8l00fQA8CGADYoSAEBvEEScv37f/nrjOQU+n7bh7ulDGE2CSSej0geFvFgGXIAaihIAQEIYA8Cq+Nj7IVILGe8qHURzTD3OuX0CuWqZQ27mGLtIAB/IhMBAC9ifJtSj6EIBDEEMChIAQGwGuKgOizqExjp3uWCypzSj1aCzHSYPfw07fOU4LRaJgGjIhEA4ggwiuR5YEgEMwQyKEgBAf9Fbwot0DfRoEFffxYIHjfGbDLSVy8TBlU1A7Xfmoz/AJIiEQDg1lxCfonNyAQ1BDQoSAEBtmTvjLQSfLaT6ueY1/sEOCYmx1/jPMUw1z1T9pq6wEAAaCIRAOBpqUcjZq6IBDcENihIAQHUaK7EFQmGwyDHqVq93WZsL2V2UImK9N4zKQ4WUjoFfgAtIhEA4Fj6XI8kmQgEUgQ4Ig8A1bTJAGCJqAQ6BDkoSAEBeCuQdnA12QaWEigcwiHE0UxLOndG4A7rygbronm7qxAAKiIPAMFKCms1sWgEPAQ7KEgBAdJQJVlUq+6xa4AVlTi9uH2WsX+bWR9yoHRJfTlt6BdgACAiDwDAPKkab39oBD4EPShIAQHlAXNJl3yVw4dC1jA38DuH8Z5kTAa4Eu7g5pM5zvw8VAAgIg8AwDYX2V64CARABD8oSAEBV4cPfAf5P66iBpX6xkVj8J2YBaW0pkDwP6nVtZFm8ukAJSIPAMAyebovr+gEUQRBIg8AwDBupkl8SARDBEIoSAEBdM6uH2Zv1iEt1NdRE7GC7QO0YYhXYGyM/bIWBvW0z/4AGCINAKBFY4jGaARFBEQoSAEBgfu3RDLgCz1+AXZie4flxn10s/BtluqP7bDpbVHRvfcAESILAITVW83IBFAERiILAIO39RhIBEgERyhIAQErSz5TCEgOuepgecnaq/xlVBBFnMyOfTOPhZiUyIOY9gAKIgsAgQJBCYgESgRJKEgBAZZ+1ISkIod0AZPKl8JwF2rWrKSz1EcnnbjvsEVxoKvYAAshmbts5815d2CTQ/eFNTUk1KopYb6TrYCAjHAn/z1Qjf4EBfXhADpBmpwwY2JJIuTZhkpeKYFhibFEQDaqWb9bZS5d/e6rAAAWKad9pvFABEsic8ACCElnPmvLuwSaH7wpqakmpVFLDfSdbAQEY4E/+eqEb/QCnsBWOsMw/YbIAACxTTvtN5EBfXhAE0AETwRMIZMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwApJzU4VipoVVV5iR1ni5Odm0iYAt4ANiR5G+SkfBEqT2ARNIWuAE6SNTGGErx4B/60W5OISlmVKhcLkdqJn83lHJXqf/mLgAAAAAAAAAAAAACBtN14TwAAAADAETihIAQEaUIwSn8duXAQC8Y61Q7EC91Vx9biQMlMEv3ADmYbuOwAIKEgBAT9mAqobqiCuRoWXQcwjOPhm/6VN2Oc3rzkDWqyQsrfZAAooSAEBGBNPqba2ITKn/AlbttbrsjKKeUqztJPCOF/idLc8BTMAEyhIAQE+KsRyB0VBLweA94SbLT++ik7THyAM4pQtEG8iVc6eigAhKEgBAam5o5Jz90yzAs2ezrmAAmma/HrzJzS33GmyR7KdOJP9AI8oSAEBE3Yc5PibbzD1vbyfZ2wK3AUNZK/kolj65DsPE/VtM0kB8ihIAQGJKdUVHhCMIlcnSS68uFXtaDlupTHaNU8yck/bj6aR9AABAhG45I37Re3WRaQEVwRWAA0AEO5rKAAIACWBBH6NRXNVQ5QII/RqGflc74AIAqCbx6mHAAAAAIQBArZbyAAAAAAAAAAAAAAAAAAAAAAAZh+xtgAALFNT7ciAAAAsU1PtyKf5uYAGAAeg6gI9C/kCPNAtxAAAADIAAAAOq+c3rgRaBFkAmAAALFNT3oZBArZbx9zZeDbZrQ1KTcwuw17XKue00bAsoNqnbv6Wylch1B20Ret6rx7T3C+a9b/eVwjJMSs6yFjtUQpr96ZLt5mR22gAmAAALFNTz0QFAj0L+fvuGT59sYQC5HYO8qAuHzjdxy/6vZ7wEBwekl15lqokV5P+e090kpJKeBsIgPm5eFH/nsrcdCd6flr2QHkpMP4=").unwrap();
        let boc = Boc::decode_base64("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").unwrap();
        let aug_dict = boc.parse::<AugDict<HashBytes, CurrencyCollection, AccountBlock>>().unwrap();
        //let block = boc.parse::<Block>().unwrap();
        //let extra = block.extra.load().unwrap();
        //let block_accounts = extra.account_blocks.load().unwrap();
        //let data = BocRepr::encode_base64(block_accounts).unwrap();
        let mut data = Vec::new();
        for i in aug_dict.iter() {
            if let Ok(entry) = i {
                data.push(entry);
            }
        }

        let mut new_aug: AugDict<HashBytes, CurrencyCollection, HashBytes> = AugDict::new();
        //let mut new: Dict<HashBytes, HashBytes> = Dict::new();
        data.reverse();

        for (index, (key, aug, value)) in data.iter().enumerate() {

            new_aug.add(key, aug, key, |l, r, bldr, ctx| {
                let right = CurrencyCollection::load_from(&mut r.clone())?;
                let mut left = CurrencyCollection::load_from(&mut l.clone())?;
                left.tokens.checked_add(right.tokens);
                left.store_into(bldr, ctx)?;
                Ok(())

            }).unwrap();
        }

    }
}
