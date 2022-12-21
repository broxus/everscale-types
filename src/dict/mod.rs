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
    if rem != 0 && !label.store_uint(rem as u64, rem) {
        return false;
    }
    label.store_bit_zero() && label.store_slice_data(key)
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::RcCellBuilder;

    #[test]
    fn labels() {
        let mut key = RcCellBuilder::new();
        key.store_zeros(5);
        key.store_bit_true();
        let key = key.build().unwrap();

        let mut label = RcCellBuilder::new();
        assert!(write_label(&key.as_slice(), 40, &mut label));
        let label = label.build().unwrap();

        println!("{}", label.display_tree());
    }
}
