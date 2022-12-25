use crate::cell::*;

pub struct HashmapE<C: CellFamily, const N: u16>(Option<CellContainer<C>>);

impl<'a, C: CellFamily, const N: u16> Load<'a, C> for HashmapE<C, N> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if slice.load_bit()? {
            let root = slice.load_reference_cloned()?;
            Some(Self(Some(root)))
        } else {
            Some(Self(None))
        }
    }
}

impl<C: CellFamily, const N: u16> Store<C> for HashmapE<C, N> {
    fn store_into(&self, b: &mut CellBuilder<C>) -> bool {
        match &self.0 {
            None => b.store_bit_zero(),
            Some(cell) => b.store_bit_true() && b.store_reference(cell.clone()),
        }
    }
}

impl<C: CellFamily, const N: u16> Default for HashmapE<C, N> {
    #[inline]
    fn default() -> Self {
        Self(None)
    }
}

impl<C: CellFamily, const N: u16> Clone for HashmapE<C, N> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<C: CellFamily, const N: u16> Eq for HashmapE<C, N> {}
impl<C: CellFamily, const N: u16> PartialEq for HashmapE<C, N> {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Some(this), Some(other)) => this.as_ref() == other.as_ref(),
            (None, None) => true,
            _ => false,
        }
    }
}

impl<C, const N: u16> HashmapE<C, N>
where
    for<'c> C: CellFamily + 'c,
{
    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    /// Returns a `CellSlice` of the value corresponding to the key.
    pub fn get<'a: 'b, 'b>(&'a self, key: CellSlice<'b, C>) -> Option<CellSlice<'a, C>> {
        hashmap_get(&self.0, N, key)
    }

    /// Gets an iterator over the entries of the map, sorted by key.
    /// The iterator element type is `(CellBuilder<C>, CellSlice<C>)`.
    ///
    /// # Performance
    ///
    /// In the current implementation, iterating over map builds a key
    /// for each element. Use [`values`] if you don't need keys from an iterator.
    ///
    /// [`values`]: HashmapE::values
    pub fn iter<'a>(&'a self) -> Iter<'a, C> {
        Iter::new(&self.0, N)
    }

    /// Gets an iterator over the keys of the map, in sorted order.
    /// The iterator element type is `CellBuilder<C>`.
    ///
    /// # Performance
    ///
    /// In the current implementation, iterating over map builds a key
    /// for each element. Use [`values`] if you don't need keys from an iterator.
    ///
    /// [`values`]: HashmapE::values
    pub fn keys<'a>(&'a self) -> Keys<'a, C> {
        Keys {
            inner: Iter::new(&self.0, N),
        }
    }

    /// Gets an iterator over the values of the map, in order by key.
    /// The iterator element type is `CellSlice<C>`.
    pub fn values<'a>(&'a self) -> Values<'a, C> {
        Values::new(&self.0, N)
    }
}

/// An iterator over the entries of a `HashmapE`.
///
/// This struct is created by the [`iter`] method on `HashmapE`. See its documentation for more.
///
/// [`iter`]: fn@crate::dict::HashmapE::iter
pub struct Iter<'a, C: CellFamily> {
    // TODO: replace `Vec` with on-stack stuff
    segments: Vec<IterSegment<'a, C>>,
}

impl<C: CellFamily> Clone for Iter<'_, C> {
    fn clone(&self) -> Self {
        Self {
            segments: self.segments.clone(),
        }
    }
}

impl<'a, C: CellFamily> Iter<'a, C> {
    pub fn new(root: &'a Option<CellContainer<C>>, bit_len: u16) -> Self {
        let mut segments = Vec::new();
        if let Some(root) = root {
            segments.push(IterSegment {
                data: root.as_ref(),
                remaining_bit_len: bit_len,
                key: CellBuilder::<C>::new(),
            });
        }
        Self { segments }
    }
}

impl<'a, C> Iterator for Iter<'a, C>
where
    for<'c> C: CellFamily + 'c,
{
    type Item = (CellBuilder<C>, CellSlice<'a, C>);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(mut segment) = self.segments.pop() {
            let mut data = segment.data.as_slice();
            let prefix = read_label(&mut data, count_bits(segment.remaining_bit_len))?;
            segment.remaining_bit_len -= prefix.remaining_bits();
            if segment.remaining_bit_len == 0 {
                return Some((segment.key, data));
            }

            let left_child = data.cell().reference(0)?;
            let right_child = data.cell().reference(1)?;

            self.segments.reserve(2);

            self.segments.push(IterSegment {
                data: right_child,
                remaining_bit_len: segment.remaining_bit_len - 1,
                key: {
                    let mut key = segment.key.clone();
                    key.store_bit_true();
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

/// An iterator over the keys of a `HashmapE`.
///
/// This struct is created by the [`keys`] method on [`HashmapE`]. See its
/// documentation for more.
///
/// [`keys`]: BTreeMap::keys
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
    type Item = CellBuilder<C>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.inner.next()?.0)
    }
}

/// An iterator over the values of a `HashmapE`.
///
/// This struct is created by the [`values`] method on [`HashmapE`]. See its documentation for more.
///
/// [`values`]: HashmapE::values
pub struct Values<'a, C: CellFamily> {
    // TODO: replace `Vec` with on-stack stuff
    segments: Vec<ValuesSegment<'a, C>>,
}

impl<C: CellFamily> Clone for Values<'_, C> {
    fn clone(&self) -> Self {
        Self {
            segments: self.segments.clone(),
        }
    }
}

impl<'a, C: CellFamily> Values<'a, C> {
    fn new(root: &'a Option<CellContainer<C>>, bit_len: u16) -> Self {
        let mut segments = Vec::new();
        if let Some(root) = root {
            segments.push(ValuesSegment {
                data: root.as_ref(),
                remaining_bit_len: bit_len,
            });
        }
        Self { segments }
    }
}

impl<'a, C> Iterator for Values<'a, C>
where
    for<'c> C: CellFamily + 'c,
{
    type Item = CellSlice<'a, C>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(mut segment) = self.segments.pop() {
            let mut data = segment.data.as_slice();
            let prefix = read_label(&mut data, count_bits(segment.remaining_bit_len))?;
            segment.remaining_bit_len -= prefix.remaining_bits();
            if segment.remaining_bit_len == 0 {
                return Some(data);
            }

            let left_child = data.cell().reference(0)?;
            let right_child = data.cell().reference(1)?;

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

pub fn hashmap_get<'a: 'b, 'b, C>(
    root: &'a Option<CellContainer<C>>,
    mut key_bit_len: u16,
    mut key: CellSlice<'b, C>,
) -> Option<CellSlice<'a, C>>
where
    for<'c> C: CellFamily + 'c,
{
    let data = root.as_ref()?;
    let mut data = data.as_ref().as_slice();

    // Read the key part written in the root cell
    let mut prefix = read_label(&mut data, count_bits(key_bit_len))?;

    // Strip the key part from the specified key
    while let Some(stripped_key) = key.strip_data_prefix(&prefix) {
        if stripped_key.is_data_empty() {
            break; // break if all parts were collected
        } else if data.remaining_refs() < 2 {
            return None; // break on leaf
        } else {
            key = stripped_key;
        }

        // Load next child based on the next bit
        let child_index = key.load_bit()? as u8;
        data = data.cell().reference(child_index)?.as_slice();

        // Reduce the remaining key bit len
        key_bit_len = key_bit_len.checked_sub(prefix.remaining_bits() + 1)?;

        // Read the key part written in the child cell
        prefix = read_label(&mut data, count_bits(key_bit_len))?;
    }

    // Return the last slice as data
    Some(data)
}

fn count_bits(key_len: u16) -> u16 {
    (16 - key_len.leading_zeros()) as u16
}

pub fn write_label<C: CellFamily>(
    key: &CellSlice<C>,
    bits_for_len: u16,
    label: &mut CellBuilder<C>,
) -> bool {
    if bits_for_len == 0 || key.is_data_empty() {
        return write_hml_empty(label);
    }

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

pub fn read_label<'a, C>(
    label: &mut CellSlice<'a, C>,
    bits_for_len: u16,
) -> Option<CellSlice<'a, C>>
where
    for<'c> C: CellFamily + 'c,
{
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

/// ```ignore
/// hml_short$0 {m:#} {n:#} len:(Unary ~n) {n <= m} s:(n * Bit) = HmLabel ~n m;
/// where n = 0
/// ```
fn write_hml_empty<C: CellFamily>(label: &mut CellBuilder<C>) -> bool {
    label.store_zeros(2)
}

/// ```ignore
/// hml_short$0 {m:#} {n:#} len:(Unary ~n) {n <= m} s:(n * Bit) = HmLabel ~n m;
/// unary_zero$0 = Unary ~0;
/// unary_succ$1 {n:#} x:(Unary ~n) = Unary ~(n + 1);
/// ```
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

/// ```ignore
/// hml_long$10 {m:#} n:(#<= m) s:(n * Bit) = HmLabel ~n m;
/// ```
fn write_hml_long<C: CellFamily>(
    key: &CellSlice<C>,
    bits_for_len: u16,
    label: &mut CellBuilder<C>,
) -> bool {
    label.store_bit_true()
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

/// ```ignore
/// hml_same$11 {m:#} v:Bit n:(#<= m) = HmLabel ~n m;
/// ```
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{RcBoc, RcCellBuilder, RcCellFamily};

    #[test]
    fn labels() {
        let bits_for_len = 3;

        // Build key
        let key = {
            let mut builder = RcCellBuilder::new();
            builder.store_zeros(5);
            builder.store_bit_true();
            builder.build().unwrap()
        };

        // Build label
        let label = {
            let mut builder = RcCellBuilder::new();
            assert!(write_label(&key.as_slice(), bits_for_len, &mut builder));
            builder.build().unwrap()
        };

        // Parse label
        let parsed_key = read_label(&mut label.as_slice(), bits_for_len).unwrap();
        let parsed_key = {
            let mut builder = RcCellBuilder::new();
            builder.store_slice(&parsed_key);
            builder.build().unwrap()
        };

        // Parsed key should be equal to the original
        assert_eq!(key.as_ref(), parsed_key.as_ref());
    }

    #[test]
    fn hashmap_get() {
        let boc =
            RcBoc::decode_base64("te6ccgECOwEAASoAAQHAAQIBIBACAgEgAwMCASAEBAIBIAUFAgEgBgYCASAHBwIBIAgIAgEgCQkCASAoCgIBIAsZAgEgDBsCASArDQIBIA4fAgEgLQ8CASAuIQIBIBERAgEgEhICASATEwIBIBQUAgEgFRUCASAWFgIBIBcXAgEgKBgCASAaGQIBIBsbAgEgHRsCASAcHAIBIB8fAgEgKx4CASAiHwIBICAgAgEgISECASAlJQIBIC0jAgEgLiQCASAvJQIBIDMmAgFiNicCAUg4OAIBICkpAgEgKioCASArKwIBICwsAgEgLS0CASAuLgIBIC8vAgEgMzACAWI2MQIBIDcyAAnWAAAmbwIBIDQ0AgEgNTUCASA2NgIBIDc3AgEgODgCASA5OQIBIDo6AAnQAAAmbw==").unwrap();
        println!("{}", boc.reference(0).unwrap().display_root());

        let map = HashmapE::<RcCellFamily, 32>::load_from(&mut boc.as_slice()).unwrap();

        let key = {
            let mut builder = RcCellBuilder::new();
            builder.store_u32(0x123);
            builder.build().unwrap()
        };
        let value = map.get(key.as_slice()).unwrap();

        let value = {
            let mut builder = RcCellBuilder::new();
            builder.store_slice(&value);
            builder.build().unwrap()
        };
        println!("{}", value.display_tree());

        let size = map.values().count();
        println!("SIZE: {size}");
    }
}
