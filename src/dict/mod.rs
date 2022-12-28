use crate::cell::*;
use crate::util::unlikely;

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
pub struct Dict<C: CellFamily, const N: u16>(Option<CellContainer<C>>);

impl<'a, C: CellFamily, const N: u16> Load<'a, C> for Dict<C, N> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if slice.load_bit()? {
            let root = slice.load_reference_cloned()?;
            Some(Self(Some(root)))
        } else {
            Some(Self(None))
        }
    }
}

impl<C: CellFamily, const N: u16> Store<C> for Dict<C, N> {
    fn store_into(&self, b: &mut CellBuilder<C>) -> bool {
        match &self.0 {
            None => b.store_bit_zero(),
            Some(cell) => b.store_bit_one() && b.store_reference(cell.clone()),
        }
    }
}

impl<C: CellFamily, const N: u16> Default for Dict<C, N> {
    #[inline]
    fn default() -> Self {
        Self(None)
    }
}

impl<C: CellFamily, const N: u16> Clone for Dict<C, N> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<C: CellFamily, const N: u16> Eq for Dict<C, N> {}
impl<C: CellFamily, const N: u16> PartialEq for Dict<C, N> {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Some(this), Some(other)) => this.as_ref() == other.as_ref(),
            (None, None) => true,
            _ => false,
        }
    }
}

impl<C: CellFamily, const N: u16> From<Option<CellContainer<C>>> for Dict<C, N> {
    #[inline]
    fn from(value: Option<CellContainer<C>>) -> Self {
        Self(value)
    }
}

impl<C: CellFamily, const N: u16> Dict<C, N> {
    const _ASSERT: () = assert!(N > 0, "Dict with 0-bit key is invalid");

    /// Creates an empty dictionary.
    pub fn new() -> Self {
        Self(None)
    }

    /// Returns `true` if the dictionary contains no elements.
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }
}

impl<C, const N: u16> Dict<C, N>
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
    /// [`values`]: Dict::values
    pub fn iter(&'_ self) -> Iter<'_, C> {
        Iter::new(&self.0, N)
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
    /// [`values`]: Dict::values
    pub fn keys(&'_ self) -> Keys<'_, C> {
        Keys {
            inner: Iter::new(&self.0, N),
        }
    }

    /// Gets an iterator over the values of the dictionary, in order by key.
    /// The iterator element type is `Result<CellSlice<C>>`.
    ///
    /// If the dictionary is invalid, finishes after the first invalid element,
    /// returning an error.
    pub fn values(&'_ self) -> Values<'_, C> {
        Values::new(&self.0, N)
    }
}

impl<C, const N: u16> Dict<C, N>
where
    for<'c> C: DefaultFinalizer + 'c,
{
    /// Sets the value associated with the key in the dictionary.
    ///
    /// Use [`set_ext`] if you need to use a custom finalizer.
    ///
    /// [`set_ext`]: Dict::set_ext
    pub fn set(&mut self, key: CellSlice<'_, C>, value: CellSlice<'_, C>) -> Result<(), Error> {
        self.set_ext(key, value, &mut C::default_finalizer())
    }

    /// Sets the value associated with the key in the dictionary
    /// only if the key was already present in it.
    ///
    /// Use [`replace_ext`] if you need to use a custom finalizer.
    ///
    /// [`replace_ext`]: Dict::replace_ext
    pub fn replace(&mut self, key: CellSlice<'_, C>, value: CellSlice<'_, C>) -> Result<(), Error> {
        self.replace_ext(key, value, &mut C::default_finalizer())
    }

    /// Sets the value associated with key in dictionary,
    /// but only if it is not already present.
    ///
    /// Use [`add_ext`] if you need to use a custom finalizer.
    ///
    /// [`add_ext`]: Dict::add_ext
    pub fn add(&mut self, key: CellSlice<'_, C>, value: CellSlice<'_, C>) -> Result<(), Error> {
        self.add_ext(key, value, &mut C::default_finalizer())
    }
}

/// An iterator over the entries of a `Dict`.
///
/// This struct is created by the [`iter`] method on `Dict`. See its documentation for more.
///
/// [`iter`]: fn@crate::dict::Dict::iter
pub struct Iter<'a, C: CellFamily> {
    // TODO: replace `Vec` with on-stack stuff
    segments: Vec<IterSegment<'a, C>>,
    status: IterStatus,
}

impl<C: CellFamily> Clone for Iter<'_, C> {
    fn clone(&self) -> Self {
        Self {
            segments: self.segments.clone(),
            status: self.status,
        }
    }
}

impl<'a, C: CellFamily> Iter<'a, C> {
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
    fn finish(&mut self, err: Error) -> Error {
        self.status = IterStatus::Broken;
        err
    }
}

impl<'a, C> Iterator for Iter<'a, C>
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
                    if unlikely(!segment.key.store_slice_data(&prefix)) {
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

/// An iterator over the keys of a `Dict`.
///
/// This struct is created by the [`keys`] method on [`Dict`]. See its
/// documentation for more.
///
/// [`keys`]: Dict::keys
pub struct Keys<'a, C: CellFamily> {
    inner: Iter<'a, C>,
}

impl<C: CellFamily> Clone for Keys<'_, C> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, C> Iterator for Keys<'a, C>
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

/// An iterator over the values of a `Dict`.
///
/// This struct is created by the [`values`] method on [`Dict`]. See its documentation for more.
///
/// [`values`]: Dict::values
pub struct Values<'a, C: CellFamily> {
    // TODO: replace `Vec` with on-stack stuff
    segments: Vec<ValuesSegment<'a, C>>,
    status: IterStatus,
}

impl<C: CellFamily> Clone for Values<'_, C> {
    fn clone(&self) -> Self {
        Self {
            segments: self.segments.clone(),
            status: self.status,
        }
    }
}

impl<'a, C: CellFamily> Values<'a, C> {
    fn new(root: &'a Option<CellContainer<C>>, bit_len: u16) -> Self {
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
    fn finish(&mut self, err: Error) -> Error {
        self.status = IterStatus::Broken;
        err
    }
}

impl<'a, C> Iterator for Values<'a, C>
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

#[derive(Clone, Copy)]
enum IterStatus {
    /// Iterator is still valid.
    Valid,
    /// Iterator started with a pruned branch cell.
    Pruned,
    /// `Dict` has invalid structure.
    Broken,
}

impl IterStatus {
    #[inline]
    pub const fn is_valid(self) -> bool {
        matches!(self, Self::Valid)
    }

    #[inline]
    pub const fn is_pruned(self) -> bool {
        matches!(self, Self::Pruned)
    }
}

/// Dictionary insection mode.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum SetMode {
    /// Sets the value associated with the key in the dictionary.
    Set = 0b11,
    /// Sets the value associated with the key in the dictionary
    /// only if the key was already present in it.
    Replace = 0b01,
    /// Sets the value associated with key in dictionary,
    /// but only if it is not already present.
    Add = 0b10,
}

impl SetMode {
    #[inline]
    pub const fn can_replace(self) -> bool {
        self as u8 & 0b01 != 0
    }

    #[inline]
    pub const fn can_add(self) -> bool {
        self as u8 & 0b10 != 0
    }
}

pub fn dict_insert<'a, C>(
    root: &'a Option<CellContainer<C>>,
    key: &mut CellSlice<C>,
    key_bit_len: u16,
    value: &CellSlice<C>,
    mode: SetMode,
    finalizer: &mut dyn Finalizer<C>,
) -> Result<Option<CellContainer<C>>, Error>
where
    for<'c> C: CellFamily + 'c,
{
    // Creates a leaf node
    fn make_leaf<C: CellFamily>(
        key: &CellSlice<C>,
        key_bit_len: u16,
        value: &CellSlice<C>,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Result<CellContainer<C>, Error> {
        let mut builder = CellBuilder::<C>::new();
        if write_label(key, key_bit_len, &mut builder) && builder.store_slice(value) {
            match builder.build_ext(finalizer) {
                Some(data) => Ok(data),
                None => Err(Error::CellOverflow), // TODO: use errors in finalizer
            }
        } else {
            Err(Error::CellOverflow)
        }
    }

    // Splits an edge or leaf
    fn split<C: CellFamily>(
        data: &CellSlice<C>,
        prefix: &mut CellSlice<C>,
        lcp: &CellSlice<C>,
        key: &mut CellSlice<C>,
        value: &CellSlice<C>,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Result<CellContainer<C>, Error> {
        // Advance the key
        let prev_key_bit_len = key.remaining_bits();
        if !key.try_advance(lcp.remaining_bits() + 1, 0) {
            return Err(Error::CellUnderflow);
        }

        // Read the next bit from the data
        prefix.try_advance(lcp.remaining_bits(), 0);
        let old_to_right = match prefix.load_bit() {
            Some(bit) => bit,
            None => return Err(Error::CellUnderflow),
        };

        // Create a leaf for the old value
        let mut left = ok!(make_leaf(prefix, key.remaining_bits(), data, finalizer));
        // Create a leaf for the right value
        let mut right = ok!(make_leaf(key, key.remaining_bits(), value, finalizer));

        // The part that starts with 1 goes to the right cell
        if old_to_right {
            std::mem::swap(&mut left, &mut right);
        }

        // Create fork
        let mut builder = CellBuilder::<C>::new();
        if write_label(lcp, prev_key_bit_len, &mut builder)
            && builder.store_reference(left)
            && builder.store_reference(right)
        {
            match builder.build_ext(finalizer) {
                Some(data) => Ok(data),
                None => Err(Error::CellOverflow), // TODO: use errors in finalizer
            }
        } else {
            Err(Error::CellOverflow)
        }
    }

    #[derive(Clone, Copy, Eq, PartialEq)]
    enum Branch {
        // Branch for a key part that starts with bit 0
        Left = 0,
        // Branch for a key part that starts with bit 1
        Right = 1,
    }

    #[derive(Clone, Copy)]
    struct Segment<'a, C: CellFamily> {
        data: CellSlice<'a, C>,
        next_branch: Branch,
    }

    if key.remaining_bits() != key_bit_len {
        return Err(Error::CellUnderflow);
    }

    let data = match root.as_ref() {
        Some(data) => data.as_ref(),
        None if mode.can_add() => {
            let data = ok!(make_leaf(key, key_bit_len, value, finalizer));
            return Ok(Some(data));
        }
        None => return Ok(None),
    };
    // Handle pruned branch access
    if unlikely(data.descriptor().is_pruned_branch()) {
        return Err(Error::PrunedBranchAccess);
    }
    let mut data = data.as_slice();

    let mut stack = Vec::<Segment<C>>::new();

    let mut leaf = loop {
        let mut remaining_data = data;

        // Read the next part of the key from the current data
        let prefix = &mut match read_label(&mut remaining_data, key.remaining_bits()) {
            Some(prefix) => prefix,
            None => return Err(Error::CellUnderflow),
        };

        // Match the prefix with the key
        let lcp = key.longest_common_data_prefix(prefix);
        match lcp.remaining_bits().cmp(&key.remaining_bits()) {
            // If all bits match, an existing value was found
            std::cmp::Ordering::Equal => {
                // Check if we can replace the value
                if !mode.can_replace() {
                    return Ok(root.clone());
                }
                // Replace the existing value
                break ok!(make_leaf(prefix, key.remaining_bits(), value, finalizer));
            }
            // LCP is less than prefix, an edge to slice was found
            std::cmp::Ordering::Less if lcp.remaining_bits() < prefix.remaining_bits() => {
                // Check if we can add a new value
                if !mode.can_add() {
                    return Ok(root.clone());
                }
                break ok!(split(&remaining_data, prefix, &lcp, key, value, finalizer));
            }
            // The key contains the entire prefix, but there are still some bits left
            std::cmp::Ordering::Less => {
                // Fail fast if there are not enough references in the fork
                let cell = data.cell();
                if cell.reference_count() != 2 {
                    return Err(Error::CellUnderflow);
                }

                // Remove the LCP from the key
                key.try_advance(lcp.remaining_bits(), 0);

                // Load the next branch
                let next_branch = match key.load_bit() {
                    Some(false) => Branch::Left,
                    Some(true) => Branch::Right,
                    None => return Err(Error::CellUnderflow),
                };

                match data.cell().reference(next_branch as u8) {
                    Some(child) => {
                        // Handle pruned branch access
                        if unlikely(child.descriptor().is_pruned_branch()) {
                            return Err(Error::PrunedBranchAccess);
                        }
                        // Push an intermediate edge to the stack
                        stack.push(Segment { data, next_branch });
                        data = child.as_slice()
                    }
                    None => return Err(Error::CellUnderflow),
                }
            }
            std::cmp::Ordering::Greater => {
                debug_assert!(false, "LCP of prefix and key can't be greater than key");
                unsafe { std::hint::unreachable_unchecked() };
            }
        }
    };

    // Rebuild the tree starting from leaves
    while let Some(last) = stack.pop() {
        // Load the opposite branch
        let (left, right) = match last.next_branch {
            Branch::Left => match last.data.cell().reference_cloned(1) {
                Some(cell) => (leaf, cell),
                None => return Err(Error::CellUnderflow),
            },
            Branch::Right => match last.data.cell().reference_cloned(0) {
                Some(cell) => (cell, leaf),
                None => return Err(Error::CellUnderflow),
            },
        };

        let mut builder = CellBuilder::<C>::new();
        if builder.store_slice_data(&last.data)
            && builder.store_reference(left)
            && builder.store_reference(right)
        {
            leaf = match builder.build_ext(finalizer) {
                Some(data) => data,
                None => return Err(Error::CellOverflow), // TODO: use errors in finalizer
            };
        } else {
            return Err(Error::CellOverflow);
        }
    }

    Ok(Some(leaf))
}

pub fn dict_get<'a: 'b, 'b, C>(
    root: &'a Option<CellContainer<C>>,
    key_bit_len: u16,
    mut key: CellSlice<'b, C>,
) -> Result<Option<CellSlice<'a, C>>, Error>
where
    for<'c> C: CellFamily + 'c,
{
    if key.remaining_bits() != key_bit_len {
        return Err(Error::CellUnderflow);
    }

    let data = match root.as_ref() {
        Some(data) => data.as_ref(),
        None => return Ok(None),
    };
    // Handle pruned branch acces
    if unlikely(data.descriptor().is_pruned_branch()) {
        return Err(Error::PrunedBranchAccess);
    }
    let mut data = data.as_slice();

    // Try to find the required leaf
    let is_key_empty = loop {
        // Read the key part written in the current edge
        let prefix = match read_label(&mut data, key.remaining_bits()) {
            Some(prefix) => prefix,
            None => return Err(Error::CellUnderflow),
        };

        // Remove this prefix from the key
        match key.strip_data_prefix(&prefix) {
            Some(stripped_key) => {
                if stripped_key.is_data_empty() {
                    // All key parts were collected <=> value found
                    break true;
                } else if data.remaining_refs() < 2 {
                    // Reached leaf while key was not fully constructed
                    return Ok(None);
                } else {
                    key = stripped_key;
                }
            }
            None => break key.is_data_empty(),
        }

        // Load next child based on the next bit
        let child_index = match key.load_bit() {
            Some(index) => index as u8,
            None => return Err(Error::CellUnderflow),
        };
        data = match data.cell().reference(child_index) {
            Some(child) if unlikely(child.descriptor().is_pruned_branch()) => {
                return Err(Error::PrunedBranchAccess)
            }
            Some(child) => child.as_slice(),
            None => return Err(Error::CellUnderflow),
        };
    };

    // Return the last slice as data
    Ok(if is_key_empty { Some(data) } else { None })
}

fn write_label<C: CellFamily>(
    key: &CellSlice<C>,
    key_bit_len: u16,
    label: &mut CellBuilder<C>,
) -> bool {
    if key_bit_len == 0 || key.is_data_empty() {
        return write_hml_empty(label);
    }

    let bits_for_len = (16 - key_bit_len.leading_zeros()) as u16;

    let remaining_bits = key.remaining_bits();

    let hml_short_len = 2 + 2 * remaining_bits;
    let hml_long_len = 2 + bits_for_len + remaining_bits;
    let hml_same_len = 3 + bits_for_len;

    if hml_same_len < hml_long_len && hml_same_len < hml_short_len {
        if let Some(bit) = key.test_uniform() {
            return write_hml_same(bit, remaining_bits, bits_for_len, label);
        }
    }

    if hml_short_len <= MAX_BIT_LEN && hml_short_len <= hml_long_len {
        write_hml_short(key, label)
    } else if hml_long_len <= MAX_BIT_LEN {
        write_hml_long(key, bits_for_len, label)
    } else {
        false
    }
}

fn read_label<'a, C>(label: &mut CellSlice<'a, C>, key_bit_len: u16) -> Option<CellSlice<'a, C>>
where
    for<'c> C: CellFamily + 'c,
{
    let bits_for_len = (16 - key_bit_len.leading_zeros()) as u16;

    if label.is_data_empty() && bits_for_len == 0 {
        Some(label.get_prefix(0, 0))
    } else if !label.load_bit()? {
        read_hml_short(label)
    } else if !label.load_bit()? {
        read_hml_long(label, bits_for_len)
    } else {
        read_hml_same(label, bits_for_len)
    }
}

fn write_hml_empty<C: CellFamily>(label: &mut CellBuilder<C>) -> bool {
    label.store_zeros(2)
}

fn write_hml_short<C: CellFamily>(key: &CellSlice<C>, label: &mut CellBuilder<C>) -> bool {
    if !label.store_bit_zero() {
        return false;
    }

    let len = key.remaining_bits();
    for _ in 0..len / 32 {
        if !label.store_u32(u32::MAX) {
            return false;
        }
    }

    let rem = len % 32;
    if rem != 0 && !label.store_uint(u64::MAX, rem) {
        return false;
    }
    label.store_bit_zero() && label.store_slice_data(key)
}

fn read_hml_short<'a, C: CellFamily>(label: &mut CellSlice<'a, C>) -> Option<CellSlice<'a, C>> {
    let mut len = 0;
    while label.load_bit()? {
        len += 1;
    }
    let result = *label;
    if label.try_advance(len, 0) {
        Some(result.get_prefix(len, 0))
    } else {
        None
    }
}

fn write_hml_long<C: CellFamily>(
    key: &CellSlice<C>,
    bits_for_len: u16,
    label: &mut CellBuilder<C>,
) -> bool {
    label.store_bit_one()
        && label.store_bit_zero()
        && label.store_uint(key.remaining_bits() as u64, bits_for_len)
        && label.store_slice_data(key)
}

fn read_hml_long<'a, C: CellFamily>(
    label: &mut CellSlice<'a, C>,
    bits_for_len: u16,
) -> Option<CellSlice<'a, C>> {
    let len = label.load_uint(bits_for_len)? as u16;
    let result = *label;
    if label.try_advance(len, 0) {
        Some(result.get_prefix(len, 0))
    } else {
        None
    }
}

fn write_hml_same<C: CellFamily>(
    bit: bool,
    len: u16,
    bits_for_len: u16,
    label: &mut CellBuilder<C>,
) -> bool {
    label.store_small_uint(0b110 | bit as u8, 3) && label.store_uint(len as u64, bits_for_len)
}

fn read_hml_same<'a, C>(label: &mut CellSlice<'a, C>, bits_for_len: u16) -> Option<CellSlice<'a, C>>
where
    for<'c> C: CellFamily + 'c,
{
    let cell = match label.load_bit()? {
        false => C::all_zeros_ref(),
        true => C::all_ones_ref(),
    };
    let len = label.load_uint(bits_for_len)? as u16;
    Some(cell.as_slice().get_prefix(len, 0))
}

#[derive(Debug, Copy, Clone, thiserror::Error)]
pub enum Error {
    #[error("cell underflow")]
    CellUnderflow,
    #[error("cell overflow")]
    CellOverflow,
    #[error("pruned branch access")]
    PrunedBranchAccess,
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
    fn labels() {
        let key_bit_len = 6;

        // Build key
        let key = {
            let mut builder = RcCellBuilder::new();
            builder.store_zeros(5);
            builder.store_bit_one();
            builder.build().unwrap()
        };

        // Build label
        let label = {
            let mut builder = RcCellBuilder::new();
            assert!(write_label(&key.as_slice(), key_bit_len, &mut builder));
            builder.build().unwrap()
        };

        // Parse label
        let parsed_key = read_label(&mut label.as_slice(), key_bit_len).unwrap();
        let parsed_key = {
            let mut builder = RcCellBuilder::new();
            builder.store_slice(&parsed_key);
            builder.build().unwrap()
        };

        // Parsed key should be equal to the original
        assert_eq!(key.as_ref(), parsed_key.as_ref());

        let label = RcCellBuilder::from_raw_data(&[0xcc, 0x40], 9)
            .unwrap()
            .build()
            .unwrap();
        let prefix = read_label(&mut label.as_slice(), 32).unwrap();

        println!("{}", build_cell(|b| b.store_slice(&prefix)).display_tree());
        assert_eq!(prefix.test_uniform(), Some(false));
    }

    #[test]
    fn dict_set() {
        let mut dict = Dict::<RcCellFamily, 32>::new();

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

        let mut dict = Dict::<RcCellFamily, 32>::new();
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
        let mut dict = Dict::<RcCellFamily, 32>::new();

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
        let mut dict = Dict::<RcCellFamily, 32>::new();

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

        let dict = Dict::<RcCellFamily, 32>::load_from(&mut boc.as_slice()).unwrap();

        let key = {
            let mut builder = RcCellBuilder::new();
            builder.store_u32(u32::from_be_bytes(123u32.to_le_bytes()));
            builder.build().unwrap()
        };
        let value = dict.get(key.as_slice()).unwrap().unwrap();

        let value = {
            let mut builder = RcCellBuilder::new();
            builder.store_slice(&value);
            builder.build().unwrap()
        };
        println!("{}", value.display_tree());
    }

    #[test]
    fn dict_iter() {
        let boc = RcBoc::decode_base64("te6ccgEBFAEAeAABAcABAgPOQAUCAgHUBAMACQAAAI3gAAkAAACjoAIBIA0GAgEgCgcCASAJCAAJAAAAciAACQAAAIfgAgEgDAsACQAAAFZgAAkAAABsIAIBIBEOAgEgEA8ACQAAADqgAAkAAABQYAIBIBMSAAkAAAAe4AAJAAAAv2A=").unwrap();
        let dict = Dict::<RcCellFamily, 32>::load_from(&mut boc.as_slice()).unwrap();

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
