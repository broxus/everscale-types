use crate::cell::*;
use crate::util::{unlikely, IterStatus};
use crate::Error;

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
pub struct RawDict<C: CellFamily, const N: u16>(pub(crate) Option<CellContainer<C>>);

impl<'a, C: CellFamily, const N: u16> Load<'a, C> for RawDict<C, N> {
    #[inline]
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self(<_>::load_from(slice)?))
    }
}

impl<C: CellFamily, const N: u16> Store<C> for RawDict<C, N> {
    #[inline]
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.0.store_into(builder, finalizer)
    }
}

impl<C: CellFamily, const N: u16> Default for RawDict<C, N> {
    #[inline]
    fn default() -> Self {
        Self(None)
    }
}

impl<C: CellFamily, const N: u16> Clone for RawDict<C, N> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<C: CellFamily, const N: u16> Eq for RawDict<C, N> {}
impl<C: CellFamily, const N: u16> PartialEq for RawDict<C, N> {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Some(this), Some(other)) => this.as_ref() == other.as_ref(),
            (None, None) => true,
            _ => false,
        }
    }
}

impl<C: CellFamily, const N: u16> From<Option<CellContainer<C>>> for RawDict<C, N> {
    #[inline]
    fn from(value: Option<CellContainer<C>>) -> Self {
        Self(value)
    }
}

impl<C: CellFamily, const N: u16> std::fmt::Debug for RawDict<C, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RawDict")
            .field("key_bit_len", &N)
            .field("root", &self.0)
            .finish()
    }
}

impl<C: CellFamily, const N: u16> RawDict<C, N> {
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
    pub const fn root(&self) -> &Option<CellContainer<C>> {
        &self.0
    }
}

impl<C, const N: u16> RawDict<C, N>
where
    for<'c> C: CellFamily + 'c,
{
    /// Loads a non-empty dictionary from a root cell.
    #[inline]
    pub fn load_from_root_ext(
        slice: &mut CellSlice<'_, C>,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Option<Self> {
        Some(Self(Some(dict_load_from_root(slice, N, finalizer)?)))
    }
}

impl<C, const N: u16> RawDict<C, N>
where
    for<'c> C: CellFamily + 'c,
{
    /// Returns a `CellSlice` of the value corresponding to the key.
    pub fn get<'a: 'b, 'b>(
        &'a self,
        key: CellSlice<'b, C>,
    ) -> Result<Option<CellSlice<'a, C>>, Error> {
        dict_get(&self.0, N, key)
    }

    /// Returns `true` if the dictionary contains a value for the specified key.
    pub fn contains_key(&self, key: CellSlice<'_, C>) -> Result<bool, Error> {
        Ok(ok!(dict_get(&self.0, N, key)).is_some())
    }

    /// Sets the value associated with the key in the dictionary.
    pub fn set_ext(
        &mut self,
        mut key: CellSlice<'_, C>,
        value: CellSlice<'_, C>,
        finalizer: &mut dyn Finalizer<C>,
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
        mut key: CellSlice<'_, C>,
        value: CellSlice<'_, C>,
        finalizer: &mut dyn Finalizer<C>,
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
        mut key: CellSlice<'_, C>,
        value: CellSlice<'_, C>,
        finalizer: &mut dyn Finalizer<C>,
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
    /// The iterator element type is `Result<(CellBuilder<C>, CellSlice<C>)>`.
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
    pub fn iter(&'_ self) -> RawIter<'_, C> {
        RawIter::new(&self.0, N)
    }

    /// Gets an iterator over the keys of the dictionary, in sorted order.
    /// The iterator element type is `Result<CellBuilder<C>>`.
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
    pub fn keys(&'_ self) -> RawKeys<'_, C> {
        RawKeys::new(&self.0, N)
    }

    /// Gets an iterator over the values of the dictionary, in order by key.
    /// The iterator element type is `Result<CellSlice<C>>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn values(&'_ self) -> RawValues<'_, C> {
        RawValues::new(&self.0, N)
    }
}

impl<C, const N: u16> RawDict<C, N>
where
    for<'c> C: DefaultFinalizer + 'c,
{
    /// Sets the value associated with the key in the dictionary.
    ///
    /// Use [`set_ext`] if you need to use a custom finalizer.
    ///
    /// [`set_ext`]: RawDict::set_ext
    pub fn set(&mut self, key: CellSlice<'_, C>, value: CellSlice<'_, C>) -> Result<(), Error> {
        self.set_ext(key, value, &mut C::default_finalizer())
    }

    /// Sets the value associated with the key in the dictionary
    /// only if the key was already present in it.
    ///
    /// Use [`replace_ext`] if you need to use a custom finalizer.
    ///
    /// [`replace_ext`]: RawDict::replace_ext
    pub fn replace(&mut self, key: CellSlice<'_, C>, value: CellSlice<'_, C>) -> Result<(), Error> {
        self.replace_ext(key, value, &mut C::default_finalizer())
    }

    /// Sets the value associated with key in dictionary,
    /// but only if it is not already present.
    ///
    /// Use [`add_ext`] if you need to use a custom finalizer.
    ///
    /// [`add_ext`]: RawDict::add_ext
    pub fn add(&mut self, key: CellSlice<'_, C>, value: CellSlice<'_, C>) -> Result<(), Error> {
        self.add_ext(key, value, &mut C::default_finalizer())
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
pub struct RawIter<'a, C: CellFamily> {
    // TODO: replace `Vec` with on-stack stuff
    segments: Vec<IterSegment<'a, C>>,
    status: IterStatus,
}

impl<C: CellFamily> Clone for RawIter<'_, C> {
    fn clone(&self) -> Self {
        Self {
            segments: self.segments.clone(),
            status: self.status,
        }
    }
}

impl<'a, C: CellFamily> RawIter<'a, C> {
    /// Creates an iterator over the entries of a dictionary.
    pub fn new(root: &'a Option<CellContainer<C>>, bit_len: u16) -> Self {
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
                key: CellBuilder::<C>::new(),
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

impl<'a, C> Iterator for RawIter<'a, C>
where
    for<'c> C: CellFamily + 'c,
{
    type Item = Result<(CellBuilder<C>, CellSlice<'a, C>), Error>;

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
            let mut data = segment.data.as_slice();

            // Read the next key part from the latest segment
            let prefix = match read_label(&mut data, segment.remaining_bit_len) {
                Some(prefix) => prefix,
                None => return Some(Err(self.finish(Error::CellUnderflow))),
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
                    if unlikely(!segment.key.store_slice_data(prefix)) {
                        return Some(Err(self.finish(Error::CellOverflow)));
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
                    key.store_bit_one();
                    key
                },
            });
            self.segments.push(IterSegment {
                data: left_child,
                remaining_bit_len: segment.remaining_bit_len - 1,
                key: {
                    segment.key.store_bit_zero();
                    segment.key
                },
            });
        }

        // No segments left
        None
    }
}

struct IterSegment<'a, C: CellFamily> {
    data: &'a dyn Cell<C>,
    remaining_bit_len: u16,
    key: CellBuilder<C>,
}

impl<C: CellFamily> Clone for IterSegment<'_, C> {
    fn clone(&self) -> Self {
        Self {
            data: self.data,
            remaining_bit_len: self.remaining_bit_len,
            key: self.key.clone(),
        }
    }
}

/// An iterator over the keys of a [`RawDict`] or a [`Dict`].
///
/// This struct is created by the [`keys`] method on [`RawDict`] or the [`raw_keys`] method on [`Dict`].
/// See their documentation for more.
///
/// [`Dict`]: crate::dict::Dict
/// [`keys`]: RawDict::keys
/// [`raw_keys`]: crate::dict::Dict::raw_keys
pub struct RawKeys<'a, C: CellFamily> {
    inner: RawIter<'a, C>,
}

impl<'a, C: CellFamily> RawKeys<'a, C> {
    /// Creates an iterator over the keys of a dictionary.
    pub fn new(root: &'a Option<CellContainer<C>>, bit_len: u16) -> Self {
        Self {
            inner: RawIter::new(root, bit_len),
        }
    }
}

impl<C: CellFamily> Clone for RawKeys<'_, C> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, C> Iterator for RawKeys<'a, C>
where
    for<'c> C: CellFamily + 'c,
{
    type Item = Result<CellBuilder<C>, Error>;

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
/// [`raw_values`]: crate::Dict::values
pub struct RawValues<'a, C: CellFamily> {
    // TODO: replace `Vec` with on-stack stuff
    segments: Vec<ValuesSegment<'a, C>>,
    status: IterStatus,
}

impl<C: CellFamily> Clone for RawValues<'_, C> {
    fn clone(&self) -> Self {
        Self {
            segments: self.segments.clone(),
            status: self.status,
        }
    }
}

impl<'a, C: CellFamily> RawValues<'a, C> {
    /// Creates an iterator over the values of a dictionary.
    pub fn new(root: &'a Option<CellContainer<C>>, bit_len: u16) -> Self {
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

impl<'a, C> Iterator for RawValues<'a, C>
where
    for<'c> C: CellFamily + 'c,
{
    type Item = Result<CellSlice<'a, C>, Error>;

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
            let mut data = segment.data.as_slice();

            // Read the next key part from the latest segment
            let prefix = match read_label(&mut data, segment.remaining_bit_len) {
                Some(prefix) => prefix,
                None => return Some(Err(self.finish(Error::CellUnderflow))),
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

struct ValuesSegment<'a, C: CellFamily> {
    data: &'a dyn Cell<C>,
    remaining_bit_len: u16,
}

impl<C: CellFamily> Copy for ValuesSegment<'_, C> {}
impl<C: CellFamily> Clone for ValuesSegment<'_, C> {
    fn clone(&self) -> Self {
        Self {
            data: self.data,
            remaining_bit_len: self.remaining_bit_len,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{RcBoc, RcCell, RcCellBuilder, RcCellFamily};

    fn build_cell<F: FnOnce(&mut RcCellBuilder) -> bool>(f: F) -> RcCell {
        let mut builder = RcCellBuilder::new();
        assert!(f(&mut builder));
        builder.build().unwrap()
    }

    #[test]
    fn dict_set() {
        let mut dict = RawDict::<RcCellFamily, 32>::new();

        let key = {
            let mut builder = RcCellBuilder::new();
            builder.store_u32(123);
            builder.build().unwrap()
        };

        let empty_value = RcCellFamily::empty_cell();
        let not_empty_value = {
            let mut builder = RcCellBuilder::new();
            builder.store_u16(0xffff);
            builder.build().unwrap()
        };

        dict.set(key.as_slice(), empty_value.as_slice()).unwrap();
        {
            let mut values = dict.values();
            let value = values.next().unwrap().unwrap();
            assert!(value.is_data_empty() && value.is_refs_empty());
            assert!(values.next().is_none());
        }

        dict.set(key.as_slice(), not_empty_value.as_slice())
            .unwrap();
        {
            let mut values = dict.values();
            let mut value = values.next().unwrap().unwrap();
            assert_eq!(value.load_u16(), Some(0xffff));
            assert!(value.is_data_empty() && value.is_refs_empty());
            assert!(values.next().is_none());
        }
    }

    #[test]
    fn dict_set_complex() {
        let value = build_cell(|b| b.store_bit_one());

        let mut dict = RawDict::<RcCellFamily, 32>::new();
        for i in 0..520 {
            let key = build_cell(|b| b.store_u32(i));
            dict.set(key.as_slice(), value.as_slice()).unwrap();

            let mut total = 0;
            for (i, item) in dict.iter().enumerate() {
                total += 1;
                let (key, value) = item.unwrap();
                let key = key.build().unwrap();
                assert_eq!(value.remaining_bits(), 1);
                assert_eq!(key.bit_len(), 32);
                let key = key.as_slice().load_u32().unwrap();
                assert_eq!(key, i as u32);
            }
            assert_eq!(total, i + 1);
        }
    }

    #[test]
    fn dict_replace() {
        let mut dict = RawDict::<RcCellFamily, 32>::new();

        //
        dict.replace(
            build_cell(|b| b.store_u32(123)).as_slice(),
            build_cell(|b| b.store_bit_zero()).as_slice(),
        )
        .unwrap();
        assert!(!dict
            .contains_key(build_cell(|b| b.store_u32(123)).as_slice())
            .unwrap());

        //
        dict.set(
            build_cell(|b| b.store_u32(123)).as_slice(),
            build_cell(|b| b.store_bit_zero()).as_slice(),
        )
        .unwrap();
        dict.replace(
            build_cell(|b| b.store_u32(123)).as_slice(),
            build_cell(|b| b.store_bit_one()).as_slice(),
        )
        .unwrap();

        let mut value = dict
            .get(build_cell(|b| b.store_u32(123)).as_slice())
            .unwrap()
            .unwrap();
        assert_eq!(value.remaining_bits(), 1);
        assert_eq!(value.load_bit(), Some(true));
    }

    #[test]
    fn dict_add() {
        let mut dict = RawDict::<RcCellFamily, 32>::new();

        let key = build_cell(|b| b.store_u32(123));

        //
        dict.add(
            key.as_slice(),
            build_cell(|b| b.store_bit_zero()).as_slice(),
        )
        .unwrap();
        let mut value = dict.get(key.as_slice()).unwrap().unwrap();
        assert_eq!(value.remaining_bits(), 1);
        assert_eq!(value.load_bit(), Some(false));

        //
        dict.add(key.as_slice(), build_cell(|b| b.store_bit_one()).as_slice())
            .unwrap();
        let mut value = dict.get(key.as_slice()).unwrap().unwrap();
        assert_eq!(value.remaining_bits(), 1);
        assert_eq!(value.load_bit(), Some(false));
    }

    #[test]
    fn dict_get() {
        let boc =
            RcBoc::decode_base64("te6ccgECOwEAASoAAQHAAQIBIBACAgEgAwMCASAEBAIBIAUFAgEgBgYCASAHBwIBIAgIAgEgCQkCASAoCgIBIAsZAgEgDBsCASArDQIBIA4fAgEgLQ8CASAuIQIBIBERAgEgEhICASATEwIBIBQUAgEgFRUCASAWFgIBIBcXAgEgKBgCASAaGQIBIBsbAgEgHRsCASAcHAIBIB8fAgEgKx4CASAiHwIBICAgAgEgISECASAlJQIBIC0jAgEgLiQCASAvJQIBIDMmAgFiNicCAUg4OAIBICkpAgEgKioCASArKwIBICwsAgEgLS0CASAuLgIBIC8vAgEgMzACAWI2MQIBIDcyAAnWAAAmbwIBIDQ0AgEgNTUCASA2NgIBIDc3AgEgODgCASA5OQIBIDo6AAnQAAAmbw==").unwrap();

        let dict = RawDict::<RcCellFamily, 32>::load_from(&mut boc.as_slice()).unwrap();

        let key = {
            let mut builder = RcCellBuilder::new();
            builder.store_u32(u32::from_be_bytes(123u32.to_le_bytes()));
            builder.build().unwrap()
        };
        let value = dict.get(key.as_slice()).unwrap().unwrap();

        let value = {
            let mut builder = RcCellBuilder::new();
            builder.store_slice(value);
            builder.build().unwrap()
        };
        println!("{}", value.display_tree());
    }

    #[test]
    fn dict_iter() {
        let boc = RcBoc::decode_base64("te6ccgEBFAEAeAABAcABAgPOQAUCAgHUBAMACQAAAI3gAAkAAACjoAIBIA0GAgEgCgcCASAJCAAJAAAAciAACQAAAIfgAgEgDAsACQAAAFZgAAkAAABsIAIBIBEOAgEgEA8ACQAAADqgAAkAAABQYAIBIBMSAAkAAAAe4AAJAAAAv2A=").unwrap();
        let dict = RawDict::<RcCellFamily, 32>::load_from(&mut boc.as_slice()).unwrap();

        let size = dict.values().count();
        assert_eq!(size, 10);

        for (i, entry) in dict.iter().enumerate() {
            let (key, _) = entry.unwrap();

            let key = {
                let key_cell = key.build().unwrap();
                key_cell.as_slice().load_u32().unwrap()
            };
            assert_eq!(key, i as u32);
        }
    }
}
