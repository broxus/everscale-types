use crate::cell::*;
use crate::error::Error;
use crate::util::{unlikely, IterStatus};

use super::{
    dict_find_bound, dict_find_bound_owned, dict_find_owned, dict_get, dict_get_owned, dict_insert,
    dict_load_from_root, dict_remove_bound_owned, dict_remove_owned, read_label, DictBound,
    DictOwnedEntry, SetMode,
};

/// Dictionary with fixed length keys (where `N` is a number of bits in each key).
///
/// # TLB scheme
///
/// ```text
/// // ordinary Hashmap / HashmapE, with fixed length keys
///
/// hm_edge#_ {n:#} {X:Type} {l:#} {m:#} label:(HmLabel ~l n)
///           {n = (~m) + l} node:(HashmapNode m X) = Hashmap n X;
///
/// hmn_leaf#_ {X:Type} value:X = HashmapNode 0 X;
/// hmn_fork#_ {n:#} {X:Type} left:^(Hashmap n X)
///            right:^(Hashmap n X) = HashmapNode (n + 1) X;
///
/// hml_short$0 {m:#} {n:#} len:(Unary ~n) {n <= m} s:(n * Bit) = HmLabel ~n m;
/// hml_long$10 {m:#} n:(#<= m) s:(n * Bit) = HmLabel ~n m;
/// hml_same$11 {m:#} v:Bit n:(#<= m) = HmLabel ~n m;
///
/// hme_empty$0 {n:#} {X:Type} = HashmapE n X;
/// hme_root$1 {n:#} {X:Type} root:^(Hashmap n X) = HashmapE n X;
///
/// unary_zero$0 = Unary ~0;
/// unary_succ$1 {n:#} x:(Unary ~n) = Unary ~(n + 1);
///
/// bit$_ (## 1) = Bit;
/// ```
pub struct RawDict<const N: u16>(pub(crate) Option<Cell>);

impl<const N: u16> ExactSize for RawDict<N> {
    #[inline]
    fn exact_size(&self) -> CellSliceSize {
        CellSliceSize {
            bits: 1,
            refs: self.0.is_some() as u8,
        }
    }
}

impl<'a, const N: u16> Load<'a> for RawDict<N> {
    #[inline]
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        match <_>::load_from(slice) {
            Ok(dict) => Ok(Self(dict)),
            Err(e) => Err(e),
        }
    }
}

impl<const N: u16> Store for RawDict<N> {
    #[inline]
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        self.0.store_into(builder, context)
    }
}

impl<const N: u16> Default for RawDict<N> {
    #[inline]
    fn default() -> Self {
        Self(None)
    }
}

impl<const N: u16> Clone for RawDict<N> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<const N: u16> Eq for RawDict<N> {}
impl<const N: u16> PartialEq for RawDict<N> {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Some(this), Some(other)) => this.as_ref() == other.as_ref(),
            (None, None) => true,
            _ => false,
        }
    }
}

impl<const N: u16> From<Option<Cell>> for RawDict<N> {
    #[inline]
    fn from(value: Option<Cell>) -> Self {
        Self(value)
    }
}

impl<const N: u16> std::fmt::Debug for RawDict<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RawDict")
            .field("key_bit_len", &N)
            .field("root", &self.0)
            .finish()
    }
}

impl<const N: u16> RawDict<N> {
    const _ASSERT: () = assert!(N > 0, "Dict with 0-bit key is invalid");

    /// Creates an empty dictionary.
    pub const fn new() -> Self {
        Self(None)
    }

    /// Returns `true` if the dictionary contains no elements.
    pub const fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    /// Returns the underlying root cell of the dictionary.
    #[inline]
    pub const fn root(&self) -> &Option<Cell> {
        &self.0
    }

    /// Loads a non-empty dictionary from a root cell.
    #[inline]
    pub fn load_from_root_ext(
        slice: &mut CellSlice<'_>,
        context: &mut dyn CellContext,
    ) -> Result<Self, Error> {
        match dict_load_from_root(slice, N, context) {
            Ok(root) => Ok(Self(Some(root))),
            Err(e) => Err(e),
        }
    }

    /// Returns a `CellSlice` of the value corresponding to the key.
    ///
    /// NOTE: Uses the default cell context.
    pub fn get<'a>(&'a self, key: CellSlice<'_>) -> Result<Option<CellSlice<'a>>, Error> {
        dict_get(self.0.as_ref(), N, key, &mut Cell::empty_context())
    }

    /// Returns a `CellSlice` of the value corresponding to the key.
    pub fn get_ext<'a>(
        &'a self,
        key: CellSlice<'_>,
        context: &mut dyn CellContext,
    ) -> Result<Option<CellSlice<'a>>, Error> {
        dict_get(self.0.as_ref(), N, key, context)
    }

    /// Computes the minimal key in dictionary that is lexicographically greater than `key`,
    /// and returns it along with associated value as cell slice parts.
    pub fn get_next_owned(
        &self,
        key: CellSlice<'_>,
        signed: bool,
    ) -> Result<Option<(CellBuilder, CellSliceParts)>, Error> {
        dict_find_owned(
            self.0.clone(),
            N,
            key,
            DictBound::Max,
            false,
            signed,
            &mut Cell::empty_context(),
        )
    }

    /// Computes the maximal key in dictionary that is lexicographically smaller than `key`,
    /// and returns it along with associated value as cell slice parts.
    pub fn get_prev_owned(
        &self,
        key: CellSlice<'_>,
        signed: bool,
    ) -> Result<Option<(CellBuilder, CellSliceParts)>, Error> {
        dict_find_owned(
            self.0.clone(),
            N,
            key,
            DictBound::Min,
            false,
            signed,
            &mut Cell::empty_context(),
        )
    }

    /// Computes the minimal key in dictionary that is lexicographically greater than `key`,
    /// and returns it along with associated value as cell slice parts.
    pub fn get_or_next_owned(
        &self,
        key: CellSlice<'_>,
        signed: bool,
    ) -> Result<Option<(CellBuilder, CellSliceParts)>, Error> {
        dict_find_owned(
            self.0.clone(),
            N,
            key,
            DictBound::Max,
            true,
            signed,
            &mut Cell::empty_context(),
        )
    }

    /// Computes the maximal key in dictionary that is lexicographically smaller than `key`,
    /// and returns it along with associated value as cell slice parts.
    pub fn get_or_prev_owned(
        &self,
        key: CellSlice<'_>,
        signed: bool,
    ) -> Result<Option<(CellBuilder, CellSliceParts)>, Error> {
        dict_find_owned(
            self.0.clone(),
            N,
            key,
            DictBound::Min,
            true,
            signed,
            &mut Cell::empty_context(),
        )
    }

    /// Returns cell slice parts of the value corresponding to the key.
    ///
    /// NOTE: Uses the default cell context.
    pub fn get_owned(&self, key: CellSlice<'_>) -> Result<Option<CellSliceParts>, Error> {
        dict_get_owned(self.0.clone(), N, key, &mut Cell::empty_context())
    }

    /// Returns cell slice parts of the value corresponding to the key.
    pub fn get_owned_ext(
        &self,
        key: CellSlice<'_>,
        context: &mut dyn CellContext,
    ) -> Result<Option<CellSliceParts>, Error> {
        dict_get_owned(self.0.clone(), N, key, context)
    }

    /// Returns the lowest key and a value corresponding to the key.
    pub fn get_min(&self, signed: bool) -> Result<Option<(CellBuilder, CellSlice<'_>)>, Error> {
        dict_find_bound(
            self.0.as_ref(),
            N,
            DictBound::Min,
            signed,
            &mut Cell::empty_context(),
        )
    }

    /// Returns the largest key and a value corresponding to the key.
    pub fn get_max(&self, signed: bool) -> Result<Option<(CellBuilder, CellSlice<'_>)>, Error> {
        dict_find_bound(
            self.0.as_ref(),
            N,
            DictBound::Max,
            signed,
            &mut Cell::empty_context(),
        )
    }

    /// Finds the specified dict bound and returns a key and a value corresponding to the key.
    pub fn get_bound(
        &self,
        bound: DictBound,
        signed: bool,
    ) -> Result<Option<(CellBuilder, CellSlice<'_>)>, Error> {
        dict_find_bound(
            self.0.as_ref(),
            N,
            bound,
            signed,
            &mut Cell::empty_context(),
        )
    }

    /// Finds the specified dict bound and returns a key and a value corresponding to the key.
    pub fn get_bound_ext(
        &self,
        bound: DictBound,
        signed: bool,
        context: &mut dyn CellContext,
    ) -> Result<Option<(CellBuilder, CellSlice<'_>)>, Error> {
        dict_find_bound(self.0.as_ref(), N, bound, signed, context)
    }

    /// Returns the lowest key and cell slice parts corresponding to the key.
    pub fn get_min_owned(
        &self,
        signed: bool,
    ) -> Result<Option<(CellBuilder, CellSliceParts)>, Error> {
        dict_find_bound_owned(
            self.0.clone(),
            N,
            DictBound::Min,
            signed,
            &mut Cell::empty_context(),
        )
    }

    /// Returns the largest key and cell slice parts corresponding to the key.
    pub fn get_max_owned(
        &self,
        signed: bool,
    ) -> Result<Option<(CellBuilder, CellSliceParts)>, Error> {
        dict_find_bound_owned(
            self.0.clone(),
            N,
            DictBound::Max,
            signed,
            &mut Cell::empty_context(),
        )
    }

    /// Finds the specified dict bound and returns a key and cell slice parts corresponding to the key.
    pub fn get_bound_owned(
        &self,
        bound: DictBound,
        signed: bool,
    ) -> Result<Option<(CellBuilder, CellSliceParts)>, Error> {
        dict_find_bound_owned(self.0.clone(), N, bound, signed, &mut Cell::empty_context())
    }

    /// Finds the specified dict bound and returns a key and cell slice parts corresponding to the key.
    pub fn get_bound_owned_ext(
        &self,
        bound: DictBound,
        signed: bool,
        context: &mut dyn CellContext,
    ) -> Result<Option<(CellBuilder, CellSliceParts)>, Error> {
        dict_find_bound_owned(self.0.clone(), N, bound, signed, context)
    }

    /// Returns `true` if the dictionary contains a value for the specified key.
    pub fn contains_key(&self, key: CellSlice<'_>) -> Result<bool, Error> {
        Ok(ok!(dict_get(
            self.0.as_ref(),
            N,
            key,
            &mut Cell::empty_context()
        ))
        .is_some())
    }

    /// Sets the value associated with the key in the dictionary.
    pub fn set_ext(
        &mut self,
        mut key: CellSlice<'_>,
        value: &dyn Store,
        context: &mut dyn CellContext,
    ) -> Result<bool, Error> {
        let (new_root, changed) = ok!(dict_insert(
            self.0.as_ref(),
            &mut key,
            N,
            &value,
            SetMode::Set,
            context
        ));
        self.0 = new_root;
        Ok(changed)
    }

    /// Sets the value associated with the key in the dictionary
    /// only if the key was already present in it.
    pub fn replace_ext(
        &mut self,
        mut key: CellSlice<'_>,
        value: &dyn Store,
        context: &mut dyn CellContext,
    ) -> Result<bool, Error> {
        let (new_root, changed) = ok!(dict_insert(
            self.0.as_ref(),
            &mut key,
            N,
            value,
            SetMode::Replace,
            context
        ));
        self.0 = new_root;
        Ok(changed)
    }

    /// Sets the value associated with key in dictionary,
    /// but only if it is not already present.
    pub fn add_ext(
        &mut self,
        mut key: CellSlice<'_>,
        value: &dyn Store,
        context: &mut dyn CellContext,
    ) -> Result<bool, Error> {
        let (new_root, changed) = ok!(dict_insert(
            self.0.as_ref(),
            &mut key,
            N,
            value,
            SetMode::Add,
            context
        ));
        self.0 = new_root;
        Ok(changed)
    }

    /// Removes the value associated with key in dictionary.
    /// Returns an optional removed value as cell slice parts.
    pub fn remove_ext(
        &mut self,
        mut key: CellSlice<'_>,
        context: &mut dyn CellContext,
    ) -> Result<Option<CellSliceParts>, Error> {
        let (dict, removed) = ok!(dict_remove_owned(
            self.0.as_ref(),
            &mut key,
            N,
            false,
            context
        ));
        self.0 = dict;
        Ok(removed)
    }

    /// Removes the specified dict bound.
    /// Returns an optional removed key and value as cell slice parts.
    pub fn remove_bound_ext(
        &mut self,
        bound: DictBound,
        signed: bool,
        context: &mut dyn CellContext,
    ) -> Result<Option<DictOwnedEntry>, Error> {
        let (dict, removed) = ok!(dict_remove_bound_owned(
            self.0.clone(),
            N,
            bound,
            signed,
            context
        ));
        self.0 = dict;
        Ok(removed)
    }

    /// Gets an iterator over the entries of the dictionary, sorted by key.
    /// The iterator element type is `Result<(CellBuilder, CellSlice)>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    ///
    /// # Performance
    ///
    /// In the current implementation, iterating over dictionary builds a key
    /// for each element. Use [`values`] if you don't need keys from an iterator.
    ///
    /// [`values`]: RawDict::values
    pub fn iter(&'_ self) -> RawIter<'_> {
        RawIter::new(&self.0, N)
    }

    /// Gets an iterator over the owned entries of the dictionary, sorted by key.
    /// The iterator element type is `Result<(CellBuilder, CellSliceParts)>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    ///
    /// # Performance
    ///
    /// In the current implementation, iterating over dictionary builds a key
    /// for each element. Use [`values_owned`] if you don't need keys from an iterator.
    ///
    /// [`values_owned`]: RawDict::values_owned
    pub fn iter_owned(&'_ self) -> RawOwnedIter<'_> {
        RawOwnedIter::new(&self.0, N)
    }

    /// Gets an iterator over the keys of the dictionary, in sorted order.
    /// The iterator element type is `Result<CellBuilder>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    ///
    /// # Performance
    ///
    /// In the current implementation, iterating over dictionary builds a key
    /// for each element. Use [`values`] if you don't need keys from an iterator.
    ///
    /// [`values`]: RawDict::values
    pub fn keys(&'_ self) -> RawKeys<'_> {
        RawKeys::new(&self.0, N)
    }

    /// Gets an iterator over the values of the dictionary, in order by key.
    /// The iterator element type is `Result<CellSlice>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn values(&'_ self) -> RawValues<'_> {
        RawValues::new(&self.0, N)
    }

    /// Gets an iterator over the owned values of the dictionary, in order by key.
    /// The iterator element type is `Result<CellSliceParts>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn values_owned(&'_ self) -> RawOwnedValues<'_> {
        RawOwnedValues::new(&self.0, N)
    }

    /// Sets the value associated with the key in the dictionary.
    ///
    /// Use [`set_ext`] if you need to use a custom cell context.
    ///
    /// [`set_ext`]: RawDict::set_ext
    pub fn set<T: Store>(&mut self, key: CellSlice<'_>, value: T) -> Result<bool, Error> {
        self.set_ext(key, &value, &mut Cell::empty_context())
    }

    /// Sets the value associated with the key in the dictionary
    /// only if the key was already present in it.
    ///
    /// Use [`replace_ext`] if you need to use a custom cell context.
    ///
    /// [`replace_ext`]: RawDict::replace_ext
    pub fn replace<T: Store>(&mut self, key: CellSlice<'_>, value: T) -> Result<bool, Error> {
        self.replace_ext(key, &value, &mut Cell::empty_context())
    }

    /// Sets the value associated with key in dictionary,
    /// but only if it is not already present.
    ///
    /// Use [`add_ext`] if you need to use a custom cell context.
    ///
    /// [`add_ext`]: RawDict::add_ext
    pub fn add<T: Store>(&mut self, key: CellSlice<'_>, value: T) -> Result<bool, Error> {
        self.add_ext(key, &value, &mut Cell::empty_context())
    }

    /// Removes the value associated with key in dictionary.
    /// Returns an optional removed value as cell slice parts.
    ///
    /// Use [`remove_ext`] if you need to use a custom cell context.
    ///
    /// [`remove_ext`]: RawDict::remove_ext
    pub fn remove(&mut self, key: CellSlice<'_>) -> Result<Option<CellSliceParts>, Error> {
        self.remove_ext(key, &mut Cell::empty_context())
    }

    /// Removes the lowest key from the dict.
    /// Returns an optional removed key and value as cell slice parts.
    ///
    /// Use [`remove_bound_ext`] if you need to use a custom context.
    ///
    /// [`remove_bound_ext`]: RawDict::remove_bound_ext
    pub fn remove_min(&mut self, signed: bool) -> Result<Option<DictOwnedEntry>, Error> {
        self.remove_bound_ext(DictBound::Min, signed, &mut Cell::empty_context())
    }

    /// Removes the largest key from the dict.
    /// Returns an optional removed key and value as cell slice parts.
    ///
    /// Use [`remove_bound_ext`] if you need to use a custom cell context.
    ///
    /// [`remove_bound_ext`]: RawDict::remove_bound_ext
    pub fn remove_max(&mut self, signed: bool) -> Result<Option<DictOwnedEntry>, Error> {
        self.remove_bound_ext(DictBound::Max, signed, &mut Cell::empty_context())
    }

    /// Removes the specified dict bound.
    /// Returns an optional removed key and value as cell slice parts.
    ///
    /// Use [`remove_bound_ext`] if you need to use a custom cell context.
    ///
    /// [`remove_bound_ext`]: RawDict::remove_bound_ext
    pub fn remove_bound(
        &mut self,
        bound: DictBound,
        signed: bool,
    ) -> Result<Option<DictOwnedEntry>, Error> {
        self.remove_bound_ext(bound, signed, &mut Cell::empty_context())
    }
}

/// An iterator over the owned entries of a [`RawDict`].
///
/// This struct is created by the [`iter_owned`] method on [`RawDict`].
/// See its documentation for more.
///
/// [`iter_owned`]: RawDict::iter_owned
#[derive(Clone)]
pub struct RawOwnedIter<'a> {
    root: &'a Option<Cell>,
    inner: RawIter<'a>,
}

impl<'a> RawOwnedIter<'a> {
    /// Creates an iterator over the owned entries of a dictionary.
    pub fn new(root: &'a Option<Cell>, bit_len: u16) -> Self {
        Self {
            inner: RawIter::new(root, bit_len),
            root,
        }
    }

    /// Creates an iterator over the entries of a dictionary with explicit
    /// direction and behavior.
    pub fn new_ext(root: &'a Option<Cell>, bit_len: u16, reversed: bool, signed: bool) -> Self {
        Self {
            inner: RawIter::new_ext(root, bit_len, reversed, signed),
            root,
        }
    }

    /// Changes the direction of the iterator to descending.
    #[inline]
    pub fn reversed(mut self) -> Self {
        self.inner.reversed = true;
        self
    }

    /// Changes the behavior of the iterator to reverse the high bit.
    #[inline]
    pub fn signed(mut self) -> Self {
        self.inner.signed = true;
        self
    }

    /// Returns whether the iterator direction was reversed.
    #[inline]
    pub fn is_reversed(&self) -> bool {
        self.inner.reversed
    }

    /// Returns whether the iterator treats keys as signed integers.
    #[inline]
    pub fn is_signed(&self) -> bool {
        self.inner.signed
    }
}

impl<'a> Iterator for RawOwnedIter<'a> {
    type Item = Result<(CellBuilder, CellSliceParts), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next_owned(self.root)
    }
}

/// An iterator over the entries of a [`RawDict`] or a [`Dict`].
///
/// This struct is created by the [`iter`] method on [`RawDict`] or the [`raw_iter`] method on [`Dict`].
/// See their documentation for more.
///
/// [`Dict`]: crate::dict::Dict
/// [`iter`]: RawDict::iter
/// [`raw_iter`]: crate::dict::Dict::raw_iter
#[derive(Clone)]
pub struct RawIter<'a> {
    segments: Vec<IterSegment<'a>>,
    status: IterStatus,
    builder: Box<CellBuilder>,
    reversed: bool,
    signed: bool,
}

impl<'a> RawIter<'a> {
    /// Creates an iterator over the entries of a dictionary.
    pub fn new(root: &'a Option<Cell>, bit_len: u16) -> Self {
        Self::new_ext(root, bit_len, false, false)
    }

    /// Creates an iterator over the entries of a dictionary with explicit
    /// direction and behavior.
    pub fn new_ext(root: &'a Option<Cell>, bit_len: u16, reversed: bool, signed: bool) -> Self {
        let mut segments = Vec::new();

        // Push root segment if any
        if let Some(root) = root {
            let Ok(data) = root.as_slice() else {
                return Self {
                    segments: Vec::new(),
                    status: IterStatus::Pruned,
                    builder: Box::default(),
                    reversed,
                    signed,
                };
            };

            segments.push(IterSegment {
                data,
                remaining_bit_len: bit_len,
                prefix: None,
            });
        }

        Self {
            segments,
            status: IterStatus::Valid,
            builder: Default::default(),
            reversed,
            signed,
        }
    }

    /// Changes the direction of the iterator to descending.
    #[inline]
    pub fn reversed(mut self) -> Self {
        self.reversed = true;
        self
    }

    /// Changes the behavior of the iterator to reverse the high bit.
    #[inline]
    pub fn signed(mut self) -> Self {
        self.signed = true;
        self
    }

    /// Returns whether the iterator direction was reversed.
    #[inline]
    pub fn is_reversed(&self) -> bool {
        self.reversed
    }

    /// Returns whether the iterator treats keys as signed integers.
    #[inline]
    pub fn is_signed(&self) -> bool {
        self.signed
    }

    /// Advances the iterator and returns the next value as owned cell slice parts.
    pub fn next_owned(
        &mut self,
        root: &Option<Cell>,
    ) -> Option<Result<(CellBuilder, CellSliceParts), Error>> {
        Some(match self.next()? {
            Ok((key, slice)) => {
                let parent = match self.segments.last() {
                    Some(segment) => {
                        let refs_offset = segment.data.refs_offset();
                        debug_assert!(
                            segment.prefix.is_some() && (refs_offset == 1 || refs_offset == 2)
                        );

                        let next_bit = (refs_offset != 1)
                            ^ self.reversed
                            ^ (self.signed
                                && self.segments.len() == 1
                                && segment.prefix.unwrap().is_data_empty());

                        match segment.data.cell().reference_cloned(next_bit as u8) {
                            Some(cell) => cell,
                            None => return Some(Err(self.finish(Error::CellUnderflow))),
                        }
                    }
                    None => match root {
                        Some(root) => root.clone(),
                        None => {
                            debug_assert!(false, "Non-empty iterator for empty dict");
                            unsafe { std::hint::unreachable_unchecked() };
                        }
                    },
                };
                Ok((key, (parent, slice.range())))
            }
            Err(e) => Err(e),
        })
    }

    #[inline]
    pub(crate) fn finish(&mut self, err: Error) -> Error {
        self.status = IterStatus::Broken;
        err
    }
}

impl<'a> Iterator for RawIter<'a> {
    type Item = Result<(CellBuilder, CellSlice<'a>), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if unlikely(!self.status.is_valid()) {
            return if self.status.is_pruned() {
                self.status = IterStatus::Broken;
                Some(Err(Error::PrunedBranchAccess))
            } else {
                None
            };
        }

        fn next_impl<'a>(
            reverse: bool,
            signed: bool,
            segments: &mut Vec<IterSegment<'a>>,
            builder: &mut CellBuilder,
        ) -> Result<Option<(CellBuilder, CellSlice<'a>)>, Error> {
            #[allow(clippy::never_loop)]
            loop {
                let mut to_rewind = 0;
                let segment = loop {
                    let is_root = segments.len() == 1;
                    let Some(segment) = segments.last_mut() else {
                        return Ok(None);
                    };

                    // Handle root case
                    let Some(prefix) = &segment.prefix else {
                        break segment;
                    };

                    let refs_offset = segment.data.refs_offset();
                    if refs_offset < 2 {
                        // Found the latest unprocessed slice
                        let remaining_bit_len = segment.remaining_bit_len;
                        let next_bit = (refs_offset != 0)
                            ^ reverse
                            ^ (signed && is_root && prefix.is_data_empty());

                        let data = ok!(segment.data.cell().get_reference_as_slice(next_bit as u8));
                        segment.data.try_advance(0, 1);

                        ok!(builder.rewind(to_rewind));
                        ok!(builder.store_bit(next_bit));
                        segments.push(IterSegment {
                            data,
                            prefix: None,
                            remaining_bit_len,
                        });
                        // SAFETY: we have just added a new element
                        break (unsafe { segments.last_mut().unwrap_unchecked() });
                    } else {
                        // Rewind prefix
                        to_rewind += prefix.remaining_bits();
                        // Pop processed segments
                        segments.pop();
                        // Rewind reference bit (if any)
                        to_rewind += !segments.is_empty() as u16;
                    }
                };

                // Read the next key part from the latest segment
                let prefix = ok!(read_label(&mut segment.data, segment.remaining_bit_len));

                // Check remaining bits
                return match segment
                    .remaining_bit_len
                    .checked_sub(prefix.remaining_bits())
                {
                    // Return value if there are no remaining bits to read
                    Some(0) => {
                        // Try to store the last prefix into the result key
                        let mut key = builder.clone();
                        ok!(key.store_slice_data(prefix));

                        let data = segment.data;

                        // Pop the current segment from the stack
                        segments.pop();
                        ok!(builder.rewind(!segments.is_empty() as u16));

                        Ok(Some((key, data)))
                    }
                    // Append prefix to builder and proceed to the next segment
                    Some(remaining) => {
                        if segment.data.remaining_refs() < 2 {
                            return Err(Error::CellUnderflow);
                        }

                        // Try to store the next prefix into the buffer
                        ok!(builder.store_slice_data(prefix));

                        // Update segment prefix
                        segment.prefix = Some(prefix);
                        segment.remaining_bit_len = remaining - 1;

                        // Handle next segment
                        continue;
                    }
                    None => Err(Error::CellUnderflow),
                };
            }
        }

        match next_impl(
            self.reversed,
            self.signed,
            &mut self.segments,
            &mut self.builder,
        ) {
            Ok(res) => res.map(Ok),
            Err(e) => Some(Err(self.finish(e))),
        }
    }
}

#[derive(Clone)]
struct IterSegment<'a> {
    data: CellSlice<'a>,
    remaining_bit_len: u16,
    prefix: Option<CellSlice<'a>>,
}

/// An iterator over the keys of a [`RawDict`] or a [`Dict`].
///
/// This struct is created by the [`keys`] method on [`RawDict`] or the [`raw_keys`] method on [`Dict`].
/// See their documentation for more.
///
/// [`Dict`]: crate::dict::Dict
/// [`keys`]: RawDict::keys
/// [`raw_keys`]: crate::dict::Dict::raw_keys
#[derive(Clone)]
pub struct RawKeys<'a> {
    inner: RawIter<'a>,
}

impl<'a> RawKeys<'a> {
    /// Creates an iterator over the keys of a dictionary.
    pub fn new(root: &'a Option<Cell>, bit_len: u16) -> Self {
        Self {
            inner: RawIter::new(root, bit_len),
        }
    }

    /// Creates an iterator over the keys of a dictionary with explicit
    /// direction and behavior.
    pub fn new_ext(root: &'a Option<Cell>, bit_len: u16, reversed: bool, signed: bool) -> Self {
        Self {
            inner: RawIter::new_ext(root, bit_len, reversed, signed),
        }
    }

    /// Changes the direction of the iterator to descending.
    #[inline]
    pub fn reversed(mut self) -> Self {
        self.inner.reversed = true;
        self
    }

    /// Changes the behavior of the iterator to reverse the high bit.
    #[inline]
    pub fn signed(mut self) -> Self {
        self.inner.signed = true;
        self
    }

    /// Returns whether the iterator direction was reversed.
    #[inline]
    pub fn is_reversed(&self) -> bool {
        self.inner.reversed
    }

    /// Returns whether the iterator treats keys as signed integers.
    #[inline]
    pub fn is_signed(&self) -> bool {
        self.inner.signed
    }
}

impl<'a> Iterator for RawKeys<'a> {
    type Item = Result<CellBuilder, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next()? {
            Ok((key, _)) => Some(Ok(key)),
            Err(e) => Some(Err(e)),
        }
    }
}

/// An iterator over the owned values of a [`RawDict`].
///
/// This struct is created by the [`values_owned`] method on [`RawDict`].
/// See its documentation for more.
///
/// [`values_owned`]: RawDict::values_owned
#[derive(Clone)]
pub struct RawOwnedValues<'a> {
    root: &'a Option<Cell>,
    inner: RawValues<'a>,
}

impl<'a> RawOwnedValues<'a> {
    /// Creates an iterator over the owned entries of a dictionary.
    pub fn new(root: &'a Option<Cell>, bit_len: u16) -> Self {
        Self {
            inner: RawValues::new(root, bit_len),
            root,
        }
    }

    /// Creates an iterator over the values of a dictionary with explicit
    /// direction and behavior.
    pub fn new_ext(root: &'a Option<Cell>, bit_len: u16, reversed: bool, signed: bool) -> Self {
        Self {
            inner: RawValues::new_ext(root, bit_len, reversed, signed),
            root,
        }
    }

    /// Changes the direction of the iterator to descending.
    #[inline]
    pub fn reversed(mut self) -> Self {
        self.inner.reversed = true;
        self
    }

    /// Changes the behavior of the iterator to reverse the high bit.
    #[inline]
    pub fn signed(mut self) -> Self {
        self.inner.signed = true;
        self
    }

    /// Returns whether the iterator direction was reversed.
    #[inline]
    pub fn is_reversed(&self) -> bool {
        self.inner.reversed
    }

    /// Returns whether the iterator treats keys as signed integers.
    #[inline]
    pub fn is_signed(&self) -> bool {
        self.inner.signed
    }
}

impl<'a> Iterator for RawOwnedValues<'a> {
    type Item = Result<CellSliceParts, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.inner.next()? {
            Ok(slice) => {
                let parent = match self.inner.segments.last() {
                    Some(segment) => {
                        let refs_offset = segment.data.refs_offset();
                        debug_assert!(refs_offset > 0);
                        match segment.data.cell().reference_cloned(refs_offset - 1) {
                            Some(cell) => cell,
                            None => return Some(Err(self.inner.finish(Error::CellUnderflow))),
                        }
                    }
                    None => match self.root {
                        Some(root) => root.clone(),
                        None => {
                            debug_assert!(false, "Non-empty iterator for empty dict");
                            unsafe { std::hint::unreachable_unchecked() };
                        }
                    },
                };
                Ok((parent, slice.range()))
            }
            Err(e) => Err(e),
        })
    }
}

/// An iterator over the values of a [`RawDict`] or a [`Dict`].
///
/// This struct is created by the [`values`] method on [`RawDict`] or the [`raw_values`] method on [`Dict`].
/// See their documentation for more.
///
/// [`Dict`]: crate::dict::Dict
/// [`values`]: RawDict::values
/// [`raw_values`]: crate::dict::Dict::raw_values
#[derive(Clone)]
pub struct RawValues<'a> {
    segments: Vec<ValuesSegment<'a>>,
    status: IterStatus,
    reversed: bool,
    signed: bool,
}

impl<'a> RawValues<'a> {
    /// Creates an iterator over the values of a dictionary.
    pub fn new(root: &'a Option<Cell>, bit_len: u16) -> Self {
        Self::new_ext(root, bit_len, false, false)
    }

    /// Creates an iterator over the values of a dictionary with explicit
    /// direction and behavior.
    pub fn new_ext(root: &'a Option<Cell>, bit_len: u16, reversed: bool, signed: bool) -> Self {
        let mut segments = Vec::new();
        if let Some(root) = root {
            let Ok(data) = root.as_slice() else {
                return Self {
                    segments: Vec::new(),
                    status: IterStatus::Pruned,
                    reversed,
                    signed,
                };
            };

            segments.push(ValuesSegment {
                data,
                remaining_bit_len: bit_len,
            });
        }
        Self {
            segments,
            status: IterStatus::Valid,
            reversed,
            signed,
        }
    }

    /// Changes the direction of the iterator to descending.
    #[inline]
    pub fn reversed(mut self) -> Self {
        self.reversed = true;
        self
    }

    /// Changes the behavior of the iterator to reverse the high bit.
    #[inline]
    pub fn signed(mut self) -> Self {
        self.signed = true;
        self
    }

    /// Returns whether the iterator direction was reversed.
    #[inline]
    pub fn is_reversed(&self) -> bool {
        self.reversed
    }

    /// Returns whether the iterator treats keys as signed integers.
    #[inline]
    pub fn is_signed(&self) -> bool {
        self.signed
    }

    #[inline]
    pub(crate) fn finish(&mut self, err: Error) -> Error {
        self.status = IterStatus::Broken;
        err
    }
}

impl<'a> Iterator for RawValues<'a> {
    type Item = Result<CellSlice<'a>, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if unlikely(!self.status.is_valid()) {
            return if self.status.is_pruned() {
                self.status = IterStatus::Broken;
                Some(Err(Error::PrunedBranchAccess))
            } else {
                None
            };
        }

        fn next_impl<'a>(
            reverse: bool,
            signed: bool,
            segments: &mut Vec<ValuesSegment<'a>>,
        ) -> Result<Option<CellSlice<'a>>, Error> {
            #[allow(clippy::never_loop)]
            loop {
                // Find the latest slice which has not been loaded yet
                let segment = loop {
                    let is_root = segments.len() == 1;
                    let Some(segment) = segments.last_mut() else {
                        return Ok(None);
                    };

                    if segment.data.bits_offset() == 0 {
                        break segment;
                    }

                    let refs_offset = segment.data.refs_offset();
                    if refs_offset < 2 {
                        // Found the latest unprocessed slice
                        let remaining_bit_len = segment.remaining_bit_len;
                        let next_bit = (refs_offset != 0)
                            ^ reverse
                            ^ (signed && is_root && segment.data.is_data_empty());
                        let data = ok!(segment.data.cell().get_reference_as_slice(next_bit as u8));
                        segment.data.try_advance(0, 1);

                        segments.push(ValuesSegment {
                            data,
                            remaining_bit_len,
                        });
                        // SAFETY: we have just added a new element
                        break (unsafe { segments.last_mut().unwrap_unchecked() });
                    } else {
                        segments.pop();
                    }
                };

                // Read the next key part from the latest segment
                let prefix = ok!(read_label(&mut segment.data, segment.remaining_bit_len));

                // Check remaining bits
                return match segment
                    .remaining_bit_len
                    .checked_sub(prefix.remaining_bits())
                {
                    // Return value if there are no remaining bits to read
                    Some(0) => {
                        let data = segment.data;
                        // Pop the current segment from the stack
                        segments.pop();
                        Ok(Some(data))
                    }
                    // Append prefix to builder and proceed to the next segment
                    Some(remaining) => {
                        if segment.data.remaining_refs() < 2 {
                            return Err(Error::CellUnderflow);
                        }
                        segment.remaining_bit_len = remaining - 1;
                        // Handle next segment
                        continue;
                    }
                    None => Err(Error::CellUnderflow),
                };
            }
        }

        match next_impl(self.reversed, self.signed, &mut self.segments) {
            Ok(res) => res.map(Ok),
            Err(e) => Some(Err(self.finish(e))),
        }
    }
}

#[derive(Copy, Clone)]
struct ValuesSegment<'a> {
    data: CellSlice<'a>,
    remaining_bit_len: u16,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prelude::*;

    fn build_cell<F: FnOnce(&mut CellBuilder) -> Result<(), Error>>(f: F) -> Cell {
        let mut builder = CellBuilder::new();
        f(&mut builder).unwrap();
        builder.build().unwrap()
    }

    #[test]
    fn dict_set() -> anyhow::Result<()> {
        let mut dict = RawDict::<32>::new();

        let key = CellBuilder::build_from(123u32)?;

        dict.set(key.as_slice()?, ())?;
        {
            let mut values = dict.values();
            let value = values.next().unwrap().unwrap();
            assert!(value.is_data_empty() && value.is_refs_empty());
            assert!(values.next().is_none());
        }

        dict.set(key.as_slice()?, 0xffffu16)?;
        {
            let mut values = dict.values();
            let mut value = values.next().unwrap()?;
            assert_eq!(value.load_u16(), Ok(0xffff));
            assert!(value.is_data_empty() && value.is_refs_empty());
            assert!(values.next().is_none());
        }

        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)] // takes too long to execute on miri
    fn dict_set_complex() -> anyhow::Result<()> {
        let mut dict = RawDict::<32>::new();
        for i in 0..520 {
            let key = build_cell(|b| b.store_u32(i));
            dict.set(key.as_slice()?, true)?;

            let mut total = 0;
            for (i, item) in dict.iter().enumerate() {
                total += 1;
                let (key, value) = item?;
                let key = key.build()?;
                assert_eq!(value.remaining_bits(), 1);
                assert_eq!(key.bit_len(), 32);
                let key = key.as_slice()?.load_u32()?;
                assert_eq!(key, i as u32);
            }
            assert_eq!(total, i + 1);
        }

        Ok(())
    }

    #[test]
    fn dict_replace() -> anyhow::Result<()> {
        let mut dict = RawDict::<32>::new();

        //
        dict.replace(build_cell(|b| b.store_u32(123)).as_slice()?, false)
            .unwrap();
        assert!(!dict
            .contains_key(build_cell(|b| b.store_u32(123)).as_slice()?)
            .unwrap());

        //
        dict.set(build_cell(|b| b.store_u32(123)).as_slice()?, false)
            .unwrap();
        dict.replace(build_cell(|b| b.store_u32(123)).as_slice()?, true)
            .unwrap();

        let mut value = dict
            .get(build_cell(|b| b.store_u32(123)).as_slice()?)
            .unwrap()
            .unwrap();
        assert_eq!(value.remaining_bits(), 1);
        assert_eq!(value.load_bit(), Ok(true));

        Ok(())
    }

    #[test]
    fn dict_add() -> anyhow::Result<()> {
        let mut dict = RawDict::<32>::new();

        let key = build_cell(|b| b.store_u32(123));

        //
        dict.add(key.as_slice()?, false)?;
        let mut value = dict.get(key.as_slice()?)?.unwrap();
        assert_eq!(value.remaining_bits(), 1);
        assert_eq!(value.load_bit(), Ok(false));

        //
        dict.add(key.as_slice()?, true)?;
        let mut value = dict.get(key.as_slice()?)?.unwrap();
        assert_eq!(value.remaining_bits(), 1);
        assert_eq!(value.load_bit(), Ok(false));

        Ok(())
    }

    #[test]
    fn dict_get() -> anyhow::Result<()> {
        let boc =
            Boc::decode_base64("te6ccgECOwEAASoAAQHAAQIBIBACAgEgAwMCASAEBAIBIAUFAgEgBgYCASAHBwIBIAgIAgEgCQkCASAoCgIBIAsZAgEgDBsCASArDQIBIA4fAgEgLQ8CASAuIQIBIBERAgEgEhICASATEwIBIBQUAgEgFRUCASAWFgIBIBcXAgEgKBgCASAaGQIBIBsbAgEgHRsCASAcHAIBIB8fAgEgKx4CASAiHwIBICAgAgEgISECASAlJQIBIC0jAgEgLiQCASAvJQIBIDMmAgFiNicCAUg4OAIBICkpAgEgKioCASArKwIBICwsAgEgLS0CASAuLgIBIC8vAgEgMzACAWI2MQIBIDcyAAnWAAAmbwIBIDQ0AgEgNTUCASA2NgIBIDc3AgEgODgCASA5OQIBIDo6AAnQAAAmbw==")?;

        let dict = boc.parse::<RawDict<32>>()?;

        let key = CellBuilder::build_from(u32::from_be_bytes(123u32.to_le_bytes()))?;
        let value = dict.get(key.as_slice()?)?.unwrap();

        {
            let (cell, range) = dict.get_owned(key.as_slice()?)?.unwrap();
            assert_eq!(range.apply(&cell).unwrap(), value);
        }

        let value = {
            let mut builder = CellBuilder::new();
            builder.store_slice(value)?;
            builder.build()?
        };
        println!("{}", value.display_tree());

        Ok(())
    }

    #[test]
    fn dict_iter() -> anyhow::Result<()> {
        let boc = Boc::decode_base64("te6ccgEBFAEAeAABAcABAgPOQAUCAgHUBAMACQAAAI3gAAkAAACjoAIBIA0GAgEgCgcCASAJCAAJAAAAciAACQAAAIfgAgEgDAsACQAAAFZgAAkAAABsIAIBIBEOAgEgEA8ACQAAADqgAAkAAABQYAIBIBMSAAkAAAAe4AAJAAAAv2A=")?;
        let dict = boc.parse::<RawDict<32>>()?;

        let size = dict.values().count();
        assert_eq!(size, 10);

        let mut rev_iter_items = dict.iter().reversed().collect::<Vec<_>>();
        rev_iter_items.reverse();
        let mut rev_iter_items = rev_iter_items.into_iter();

        for (i, entry) in dict.iter().enumerate() {
            let (key, value) = entry?;

            let (rev_key, rev_value) = rev_iter_items.next().unwrap().unwrap();
            assert_eq!(key, rev_key);
            assert_eq!(
                value.cmp_by_content(&rev_value),
                Ok(std::cmp::Ordering::Equal)
            );

            let key = {
                let key_cell = key.build()?;
                key_cell.as_slice()?.load_u32()?
            };
            assert_eq!(key, i as u32);
        }
        assert!(rev_iter_items.next().is_none());

        let mut last = None;
        for (i, entry) in dict.iter_owned().enumerate() {
            let (key, (cell, range)) = entry?;

            {
                let mut slice = range.apply(&cell).unwrap();
                assert_eq!(slice.remaining_bits(), 32);
                u32::load_from(&mut slice).unwrap();
            }

            let key = {
                let key_cell = key.build()?;
                key_cell.as_slice()?.load_u32()?
            };
            assert_eq!(key, i as u32);
            last = Some(key);
        }
        assert_eq!(last, Some(9));

        let mut values_ref = dict.values();
        let mut values_owned = dict.values_owned();
        for (value_ref, value_owned) in (&mut values_ref).zip(&mut values_owned) {
            let value_ref = value_ref.unwrap();
            let (cell, range) = value_owned.unwrap();
            let value_owned = range.apply(&cell).unwrap();
            assert_eq!(
                value_ref.cmp_by_content(&value_owned),
                Ok(std::cmp::Ordering::Equal)
            );
        }
        assert!(values_ref.next().is_none());
        assert!(values_owned.next().is_none());

        Ok(())
    }

    #[derive(Debug, Default)]
    struct SimpleContext {
        used_gas: u64,
        loaded_cells: ahash::HashSet<HashBytes>,
        empty_context: <Cell as CellFamily>::EmptyCellContext,
    }

    impl SimpleContext {
        const BUILD_CELL_GAS: u64 = 500;
        const NEW_CELL_GAS: u64 = 100;
        const OLD_CELL_GAS: u64 = 25;

        fn consume_gas(&mut self, cell: &DynCell, mode: LoadMode) {
            if mode.use_gas() {
                self.used_gas += if self.loaded_cells.insert(*cell.repr_hash()) {
                    println!("LOAD NEW");
                    Self::NEW_CELL_GAS
                } else {
                    println!("LOAD OLD");
                    Self::OLD_CELL_GAS
                };
            }
        }
    }

    impl CellContext for SimpleContext {
        #[inline]
        fn finalize_cell(&mut self, cell: CellParts<'_>) -> Result<Cell, Error> {
            println!("FINALIZE");
            self.used_gas += Self::BUILD_CELL_GAS;
            self.empty_context.finalize_cell(cell)
        }

        #[inline]
        fn load_cell(&mut self, cell: Cell, mode: LoadMode) -> Result<Cell, Error> {
            self.consume_gas(cell.as_ref(), mode);
            Ok(cell)
        }

        #[inline]
        fn load_dyn_cell<'a>(
            &mut self,
            cell: &'a DynCell,
            mode: LoadMode,
        ) -> Result<&'a DynCell, Error> {
            self.consume_gas(cell, mode);
            Ok(cell)
        }
    }

    #[test]
    fn dict_get_gas_usage() -> anyhow::Result<()> {
        // Prepare dict
        let mut dict = RawDict::<32>::new();
        for i in 0..10 {
            let mut key = CellBuilder::new();
            key.store_u32(i)?;
            dict.set(key.as_data_slice(), i)?;
        }

        // First get
        let context = &mut SimpleContext::default();

        let mut key = CellBuilder::new();
        key.store_u32(5)?;

        dict.get_ext(key.as_data_slice(), context)?.unwrap();
        assert_eq!(context.used_gas, SimpleContext::NEW_CELL_GAS * 5);

        context.used_gas = 0;
        dict.get_ext(key.as_data_slice(), context)?.unwrap();
        assert_eq!(context.used_gas, SimpleContext::OLD_CELL_GAS * 5);

        // Second get
        context.used_gas = 0;
        let mut key = CellBuilder::new();
        key.store_u32(9)?;

        dict.get_ext(key.as_data_slice(), context)?.unwrap();
        assert_eq!(
            context.used_gas,
            SimpleContext::OLD_CELL_GAS + SimpleContext::NEW_CELL_GAS * 2
        );

        context.used_gas = 0;
        dict.get_ext(key.as_data_slice(), context)?.unwrap();
        assert_eq!(context.used_gas, SimpleContext::OLD_CELL_GAS * 3);

        Ok(())
    }

    #[test]
    fn dict_get_owned_gas_usage() -> anyhow::Result<()> {
        // Prepare dict
        let mut dict = RawDict::<32>::new();
        for i in 0..10 {
            let mut key = CellBuilder::new();
            key.store_u32(i)?;
            dict.set(key.as_data_slice(), i)?;
        }

        // First get
        let context = &mut SimpleContext::default();

        let mut key = CellBuilder::new();
        key.store_u32(5)?;

        dict.get_owned_ext(key.as_data_slice(), context)?.unwrap();
        assert_eq!(context.used_gas, SimpleContext::NEW_CELL_GAS * 5);

        context.used_gas = 0;
        dict.get_owned_ext(key.as_data_slice(), context)?.unwrap();
        assert_eq!(context.used_gas, SimpleContext::OLD_CELL_GAS * 5);

        // Second get
        context.used_gas = 0;
        let mut key = CellBuilder::new();
        key.store_u32(9)?;

        dict.get_owned_ext(key.as_data_slice(), context)?.unwrap();
        assert_eq!(
            context.used_gas,
            SimpleContext::OLD_CELL_GAS + SimpleContext::NEW_CELL_GAS * 2
        );

        context.used_gas = 0;
        dict.get_owned_ext(key.as_data_slice(), context)?.unwrap();
        assert_eq!(context.used_gas, SimpleContext::OLD_CELL_GAS * 3);

        Ok(())
    }

    #[test]
    fn dict_set_gas_usage() -> anyhow::Result<()> {
        let target_gas = [
            SimpleContext::BUILD_CELL_GAS,
            SimpleContext::NEW_CELL_GAS + SimpleContext::BUILD_CELL_GAS * 3,
            SimpleContext::NEW_CELL_GAS + SimpleContext::BUILD_CELL_GAS * 3,
            SimpleContext::NEW_CELL_GAS * 2 + SimpleContext::BUILD_CELL_GAS * 4,
            SimpleContext::NEW_CELL_GAS + SimpleContext::BUILD_CELL_GAS * 3,
            SimpleContext::NEW_CELL_GAS * 2 + SimpleContext::BUILD_CELL_GAS * 4,
            SimpleContext::NEW_CELL_GAS * 2 + SimpleContext::BUILD_CELL_GAS * 4,
            SimpleContext::NEW_CELL_GAS * 3 + SimpleContext::BUILD_CELL_GAS * 5,
            SimpleContext::NEW_CELL_GAS + SimpleContext::BUILD_CELL_GAS * 3,
            SimpleContext::NEW_CELL_GAS * 2 + SimpleContext::BUILD_CELL_GAS * 4,
        ];

        // RawDict
        let mut dict = RawDict::<32>::new();
        for i in 0..10 {
            let context = &mut SimpleContext::default();

            let mut key = CellBuilder::new();
            key.store_u32(i)?;

            dict.set_ext(key.as_data_slice(), &i, context)?;

            assert_eq!(context.used_gas, target_gas[i as usize]);

            println!("===");
        }

        // Compare `dict_insert` and `dict_insert_owned`
        let mut dict = None::<Cell>;
        for i in 0..10 {
            let mut key = CellBuilder::new();
            key.store_u32(i)?;

            let context = &mut SimpleContext::default();
            let (expected_new_root, _) = crate::dict::dict_insert(
                dict.as_ref(),
                &mut key.as_data_slice(),
                32,
                &i,
                SetMode::Set,
                context,
            )?;
            assert_eq!(context.used_gas, target_gas[i as usize]);

            println!("===");

            let context = &mut SimpleContext::default();
            let (new_root, _, _) = crate::dict::dict_insert_owned(
                dict,
                &mut key.as_data_slice(),
                32,
                &i,
                SetMode::Set,
                context,
            )?;
            assert_eq!(new_root, expected_new_root);
            dict = new_root;

            assert_eq!(context.used_gas, target_gas[i as usize]);

            println!("===");
        }

        // Check `add` as noop
        let mut key = CellBuilder::new();
        key.store_u32(5)?;

        let context = &mut SimpleContext::default();
        crate::dict::dict_insert(
            dict.as_ref(),
            &mut key.as_data_slice(),
            32,
            &5u32,
            SetMode::Add,
            context,
        )?;
        assert_eq!(context.used_gas, SimpleContext::NEW_CELL_GAS * 5); // Equivalent to simple get

        println!("===");

        let context = &mut SimpleContext::default();
        crate::dict::dict_insert_owned(
            dict,
            &mut key.as_data_slice(),
            32,
            &5u32,
            SetMode::Add,
            context,
        )?;
        assert_eq!(context.used_gas, SimpleContext::NEW_CELL_GAS * 5); // Equivalent to simple get

        Ok(())
    }
}
