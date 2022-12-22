use crate::cell::*;

pub struct HashmapE<C: CellFamily> {
    pub key_bit_len: u16,
    pub data: Option<CellContainer<C>>,
}

impl<C: CellFamily> Default for HashmapE<C> {
    #[inline]
    fn default() -> Self {
        Self {
            key_bit_len: 0,
            data: None,
        }
    }
}

impl<C: CellFamily> Clone for HashmapE<C> {
    fn clone(&self) -> Self {
        Self {
            key_bit_len: self.key_bit_len,
            data: self.data.clone(),
        }
    }
}

impl<C: CellFamily> Eq for HashmapE<C> {}
impl<C: CellFamily> PartialEq for HashmapE<C> {
    fn eq(&self, other: &Self) -> bool {
        self.key_bit_len == other.key_bit_len
            && match (&self.data, &other.data) {
                (Some(this), Some(other)) => this.as_ref() == other.as_ref(),
                (None, None) => true,
                _ => false,
            }
    }
}

impl<C: CellFamily> HashmapE<C> {
    pub fn is_empty(&self) -> bool {
        self.data.is_none()
    }
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
    use crate::RcCellBuilder;

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
}
