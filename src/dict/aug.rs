use std::borrow::Borrow;
use std::marker::PhantomData;

use super::{aug_dict_insert, aug_dict_remove_owned, SetMode};
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

    /// Removes the value associated with key in aug dictionary.
    /// Returns an optional removed value as cell slice parts.
    ///
    /// Use [`remove_ext`] if you need to use a custom cell context.
    ///
    /// [`remove_ext`]: RawDict::remove_ext
    pub fn remove<Q>(
        &mut self,
        key: Q,
        extra_comparator: fn(
            left: &CellSlice,
            right: &CellSlice,
            builder: &mut CellBuilder,
            context: &mut dyn CellContext,
        ) -> Result<(), Error>,
    ) -> Result<Option<CellSliceParts>, Error> where Q: Borrow<K>,
    {
        self.remove_ext(key.borrow(), extra_comparator, &mut Cell::empty_context())
    }

    /// Removes the value associated with key in dictionary.
    /// Returns an optional removed value as cell slice parts.
    pub fn remove_ext(
        &mut self,
        key: &K,
        extra_comparator: fn(
            left: &CellSlice,
            right: &CellSlice,
            builder: &mut CellBuilder,
            context: &mut dyn CellContext,
        ) -> Result<(), Error>,
        context: &mut dyn CellContext,
    ) -> Result<Option<CellSliceParts>, Error> where K: Store + DictKey
    {
        let mut key_builder = CellBuilder::new();
        ok!(key.store_into(&mut key_builder, &mut Cell::empty_context()));
        aug_dict_remove_owned(
            &mut self.dict.root, &mut key_builder.as_data_slice(), K::BITS, false, context, extra_comparator)
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
    use super::*;
    use crate::models::{AccountBlock, CurrencyCollection};
    use crate::prelude::Boc;
    use std::str::FromStr;

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
        let boc = Boc::decode_base64("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").unwrap();
        let aug_dict = boc
            .parse::<AugDict<HashBytes, CurrencyCollection, AccountBlock>>()
            .unwrap();
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
            println!("\n added key {} ", key );
            new_aug
                .add(key, aug, key, |l, r, bldr, ctx| {
                    let right = CurrencyCollection::load_from(&mut r.clone())?;
                    let mut left = CurrencyCollection::load_from(&mut l.clone())?;
                    left.tokens.checked_add(right.tokens);
                    left.store_into(bldr, ctx)?;
                    Ok(())
                })
                .unwrap();
        }

        for i in new_aug.iter() {
            match i {
                Ok((key,aug, value)) => {
                    println!("{}", key);
                }
                Err(e) => {
                    println!("{e:?}");
                }
            }
        }

        let mut builder = CellBuilder::new();

        for (index, (key, aug, value)) in data.iter().enumerate() {
            new_aug.remove(key, |l, r, bldr, ctx| {
                let right = CurrencyCollection::load_from(&mut r.clone())?;
                let mut left = CurrencyCollection::load_from(&mut l.clone())?;
                left.tokens.checked_add(right.tokens);
                left.store_into(bldr, ctx)?;
                Ok(())
            }).unwrap();
        }

        println!(" -- AFTER REMOVE --");

        for i in new_aug.iter() {
            match i {
                Ok((key,aug, value)) => {
                    println!("{}", key);
                }
                Err(e) => {
                    println!("{e:?}");
                }
            }
        }

    }


}
