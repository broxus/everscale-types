use crate::cell::*;
use crate::error::Error;
use crate::util::{unlikely, IterStatus};

use super::{dict_get, dict_insert, dict_load_from_root, read_label, SetMode};

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
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        self.0.store_into(builder, finalizer)
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
        finalizer: &mut dyn Finalizer,
    ) -> Result<Self, Error> {
        match dict_load_from_root(slice, N, finalizer) {
            Ok(root) => Ok(Self(Some(root))),
            Err(e) => Err(e),
        }
    }

    /// Returns a `CellSlice` of the value corresponding to the key.
    pub fn get<'a: 'b, 'b>(&'a self, key: CellSlice<'b>) -> Result<Option<CellSlice<'a>>, Error> {
        dict_get(&self.0, N, key)
    }

    /// Returns `true` if the dictionary contains a value for the specified key.
    pub fn contains_key(&self, key: CellSlice<'_>) -> Result<bool, Error> {
        Ok(ok!(dict_get(&self.0, N, key)).is_some())
    }

    /// Sets the value associated with the key in the dictionary.
    pub fn set_ext(
        &mut self,
        mut key: CellSlice<'_>,
        value: CellSlice<'_>,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        self.0 = ok!(dict_insert(
            &self.0,
            &mut key,
            N,
            &value,
            SetMode::Set,
            finalizer
        ));
        Ok(())
    }

    /// Sets the value associated with the key in the dictionary
    /// only if the key was already present in it.
    pub fn replace_ext(
        &mut self,
        mut key: CellSlice<'_>,
        value: CellSlice<'_>,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        self.0 = ok!(dict_insert(
            &self.0,
            &mut key,
            N,
            &value,
            SetMode::Replace,
            finalizer
        ));
        Ok(())
    }

    /// Sets the value associated with key in dictionary,
    /// but only if it is not already present.
    pub fn add_ext(
        &mut self,
        mut key: CellSlice<'_>,
        value: CellSlice<'_>,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        self.0 = ok!(dict_insert(
            &self.0,
            &mut key,
            N,
            &value,
            SetMode::Add,
            finalizer
        ));
        Ok(())
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

    /// Sets the value associated with the key in the dictionary.
    ///
    /// Use [`set_ext`] if you need to use a custom finalizer.
    ///
    /// [`set_ext`]: RawDict::set_ext
    pub fn set(&mut self, key: CellSlice<'_>, value: CellSlice<'_>) -> Result<(), Error> {
        self.set_ext(key, value, &mut Cell::default_finalizer())
    }

    /// Sets the value associated with the key in the dictionary
    /// only if the key was already present in it.
    ///
    /// Use [`replace_ext`] if you need to use a custom finalizer.
    ///
    /// [`replace_ext`]: RawDict::replace_ext
    pub fn replace(&mut self, key: CellSlice<'_>, value: CellSlice<'_>) -> Result<(), Error> {
        self.replace_ext(key, value, &mut Cell::default_finalizer())
    }

    /// Sets the value associated with key in dictionary,
    /// but only if it is not already present.
    ///
    /// Use [`add_ext`] if you need to use a custom finalizer.
    ///
    /// [`add_ext`]: RawDict::add_ext
    pub fn add(&mut self, key: CellSlice<'_>, value: CellSlice<'_>) -> Result<(), Error> {
        self.add_ext(key, value, &mut Cell::default_finalizer())
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
    // TODO: replace `Vec` with on-stack stuff
    segments: Vec<IterSegment<'a>>,
    status: IterStatus,
}

impl<'a> RawIter<'a> {
    /// Creates an iterator over the entries of a dictionary.
    pub fn new(root: &'a Option<Cell>, bit_len: u16) -> Self {
        let mut segments = Vec::new();

        // Push root segment if any
        if let Some(root) = root {
            let data = root.as_ref();
            if unlikely(data.descriptor().is_pruned_branch()) {
                return Self {
                    segments: Vec::new(),
                    status: IterStatus::Pruned,
                };
            }

            segments.push(IterSegment {
                data,
                remaining_bit_len: bit_len,
                key: CellBuilder::new(),
            });
        }

        Self {
            segments,
            status: IterStatus::Valid,
        }
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

        while let Some(mut segment) = self.segments.pop() {
            // Load segment data
            let mut data = match segment.data.as_slice() {
                Ok(data) => data,
                Err(e) => return Some(Err(self.finish(e))),
            };

            // Read the next key part from the latest segment
            let prefix = match read_label(&mut data, segment.remaining_bit_len) {
                Ok(prefix) => prefix,
                Err(e) => return Some(Err(self.finish(e))),
            };

            // Check remaining bits
            segment.remaining_bit_len = match segment
                .remaining_bit_len
                .checked_sub(prefix.remaining_bits())
            {
                // Well-formed `Dict` should have the required number of bits
                // for each value
                Some(remaining) => {
                    // Try to store the next prefix into the segment key
                    if let Err(e) = segment.key.store_slice_data(prefix) {
                        return Some(Err(self.finish(e)));
                    } else if remaining == 0 {
                        // Return the next entry if there are no remaining bits to read
                        return Some(Ok((segment.key, data)));
                    } else {
                        // Continue reading
                        remaining
                    }
                }
                None => return Some(Err(self.finish(Error::CellUnderflow))),
            };

            // Trying to load the left child cell
            let left_child = match data.cell().reference(0) {
                Some(child) => {
                    // Handle pruned branch access
                    if unlikely(child.descriptor().is_pruned_branch()) {
                        return Some(Err(self.finish(Error::PrunedBranchAccess)));
                    }
                    child
                }
                None => return Some(Err(self.finish(Error::CellUnderflow))),
            };

            // Trying to load the right child cell
            let right_child = match data.cell().reference(1) {
                Some(child) => {
                    // Handle pruned branch access
                    if unlikely(child.descriptor().is_pruned_branch()) {
                        return Some(Err(self.finish(Error::PrunedBranchAccess)));
                    }
                    child
                }
                None => return Some(Err(self.finish(Error::CellUnderflow))),
            };

            // Push cells in reverse order
            self.segments.reserve(2);
            self.segments.push(IterSegment {
                data: right_child,
                remaining_bit_len: segment.remaining_bit_len - 1,
                key: {
                    let mut key = segment.key.clone();
                    _ = key.store_bit_one();
                    key
                },
            });
            self.segments.push(IterSegment {
                data: left_child,
                remaining_bit_len: segment.remaining_bit_len - 1,
                key: {
                    _ = segment.key.store_bit_zero();
                    segment.key
                },
            });
        }

        // No segments left
        None
    }
}

#[derive(Clone)]
struct IterSegment<'a> {
    data: &'a DynCell,
    remaining_bit_len: u16,
    key: CellBuilder,
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
    // TODO: replace `Vec` with on-stack stuff
    segments: Vec<ValuesSegment<'a>>,
    status: IterStatus,
}

impl<'a> RawValues<'a> {
    /// Creates an iterator over the values of a dictionary.
    pub fn new(root: &'a Option<Cell>, bit_len: u16) -> Self {
        let mut segments = Vec::new();
        if let Some(root) = root {
            let data = root.as_ref();
            if unlikely(data.descriptor().is_pruned_branch()) {
                return Self {
                    segments: Vec::new(),
                    status: IterStatus::Pruned,
                };
            }

            segments.push(ValuesSegment {
                data,
                remaining_bit_len: bit_len,
            });
        }
        Self {
            segments,
            status: IterStatus::Valid,
        }
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

        while let Some(mut segment) = self.segments.pop() {
            // Load segment data
            let mut data = match segment.data.as_slice() {
                Ok(data) => data,
                Err(e) => return Some(Err(self.finish(e))),
            };

            // Read the next key part from the latest segment
            let prefix = match read_label(&mut data, segment.remaining_bit_len) {
                Ok(prefix) => prefix,
                Err(e) => return Some(Err(self.finish(e))),
            };

            // Check remaining bits
            segment.remaining_bit_len = match segment
                .remaining_bit_len
                .checked_sub(prefix.remaining_bits())
            {
                // Return the next value if there are no remaining bits to read
                Some(0) => return Some(Ok(data)),
                // Continue reading
                Some(bit_len) => bit_len,
                // Well-formed `Dict` should have the required number of bits
                // for each value
                None => return Some(Err(self.finish(Error::CellUnderflow))),
            };

            // Trying to load the left child cell
            let left_child = match data.cell().reference(0) {
                Some(child) => {
                    // Handle pruned branch access
                    if unlikely(child.descriptor().is_pruned_branch()) {
                        return Some(Err(self.finish(Error::PrunedBranchAccess)));
                    }
                    child
                }
                None => return Some(Err(self.finish(Error::CellUnderflow))),
            };

            // Trying to load the right child cell
            let right_child = match data.cell().reference(1) {
                Some(child) => {
                    // Handle pruned branch access
                    if unlikely(child.descriptor().is_pruned_branch()) {
                        return Some(Err(self.finish(Error::PrunedBranchAccess)));
                    }
                    child
                }
                None => return Some(Err(self.finish(Error::CellUnderflow))),
            };

            // Push cells in reverse order
            self.segments.reserve(2);
            self.segments.push(ValuesSegment {
                data: right_child,
                remaining_bit_len: segment.remaining_bit_len - 1,
            });
            self.segments.push(ValuesSegment {
                data: left_child,
                remaining_bit_len: segment.remaining_bit_len - 1,
            });
        }

        None
    }
}

#[derive(Copy, Clone)]
struct ValuesSegment<'a> {
    data: &'a DynCell,
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

        let empty_value = Cell::empty_cell();
        let not_empty_value = CellBuilder::build_from(0xffffu16)?;

        dict.set(key.as_slice()?, empty_value.as_slice()?)?;
        {
            let mut values = dict.values();
            let value = values.next().unwrap().unwrap();
            assert!(value.is_data_empty() && value.is_refs_empty());
            assert!(values.next().is_none());
        }

        dict.set(key.as_slice()?, not_empty_value.as_slice()?)?;
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
        let value = build_cell(|b| b.store_bit_one());

        let mut dict = RawDict::<32>::new();
        for i in 0..520 {
            let key = build_cell(|b| b.store_u32(i));
            dict.set(key.as_slice()?, value.as_slice()?)?;

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
        dict.replace(
            build_cell(|b| b.store_u32(123)).as_slice()?,
            build_cell(|b| b.store_bit_zero()).as_slice()?,
        )
        .unwrap();
        assert!(!dict
            .contains_key(build_cell(|b| b.store_u32(123)).as_slice()?)
            .unwrap());

        //
        dict.set(
            build_cell(|b| b.store_u32(123)).as_slice()?,
            build_cell(|b| b.store_bit_zero()).as_slice()?,
        )
        .unwrap();
        dict.replace(
            build_cell(|b| b.store_u32(123)).as_slice()?,
            build_cell(|b| b.store_bit_one()).as_slice()?,
        )
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
        dict.add(
            key.as_slice()?,
            build_cell(|b| b.store_bit_zero()).as_slice()?,
        )?;
        let mut value = dict.get(key.as_slice()?)?.unwrap();
        assert_eq!(value.remaining_bits(), 1);
        assert_eq!(value.load_bit(), Ok(false));

        //
        dict.add(
            key.as_slice()?,
            build_cell(|b| b.store_bit_one()).as_slice()?,
        )?;
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

        for (i, entry) in dict.iter().enumerate() {
            let (key, _) = entry?;

            let key = {
                let key_cell = key.build()?;
                key_cell.as_slice()?.load_u32()?
            };
            assert_eq!(key, i as u32);
        }

        Ok(())
    }
}
