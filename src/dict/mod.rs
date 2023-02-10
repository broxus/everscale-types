//! Dictionary implementation.

use crate::cell::*;
use crate::util::unlikely;
use crate::Error;

pub use aug::*;
pub use raw::*;
pub use typed::*;

mod aug;
mod raw;
mod typed;

/// Type which can be used as a dictionary key.
pub trait DictKey {
    /// Length in bits for a dictionary key.
    const BITS: u16;
}

macro_rules! impl_dict_key {
    ($($ty:ty => $bits:literal),*,) => {
        $(impl DictKey for $ty {
            const BITS: u16 = $bits;
        })*
    };
}

impl_dict_key! {
    bool => 1,
    u8 => 8,
    i8 => 8,
    u16 => 16,
    i16 => 16,
    u32 => 32,
    i32 => 32,
    u64 => 64,
    i64 => 64,
    u128 => 128,
    i128 => 128,
    [u8; 16] => 128,
    [u8; 20] => 160,
    [u8; 32] => 256,
}

/// Dictionary insertion mode.
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
    /// Returns `true` if the new value can replace the old value for the same key.
    #[inline]
    pub const fn can_replace(self) -> bool {
        self as u8 & 0b01 != 0
    }

    /// Returns `true` if inserting a value can add a new key to the dictionary.
    #[inline]
    pub const fn can_add(self) -> bool {
        self as u8 & 0b10 != 0
    }
}

/// Inserts the value associated with key in dictionary
/// in accordance with the logic of the specified [`SetMode`].
pub fn dict_insert<C>(
    root: &Option<CellContainer<C>>,
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
        if builder.store_slice_data(last.data)
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

/// Returns a `CellSlice` of the value corresponding to the key.
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
    // Handle pruned branch access
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
                return Err(Error::PrunedBranchAccess);
            }
            Some(child) => child.as_slice(),
            None => return Err(Error::CellUnderflow),
        };
    };

    // Return the last slice as data
    Ok(if is_key_empty { Some(data) } else { None })
}

/// Loads a non-empty dictionary from the root cell.
pub fn dict_load_from_root<C>(
    slice: &mut CellSlice<'_, C>,
    key_bit_len: u16,
    finalizer: &mut dyn Finalizer<C>,
) -> Option<CellContainer<C>>
where
    for<'c> C: CellFamily + 'c,
{
    let mut root = *slice;

    let label = read_label(slice, key_bit_len)?;
    if label.remaining_bits() != key_bit_len {
        if !slice.try_advance(0, 2) {
            return None;
        }
        let root_bits = root.remaining_bits() - slice.remaining_bits();
        let root_refs = root.remaining_refs() - slice.remaining_refs();
        root = root.get_prefix(root_bits, root_refs)
    } else {
        slice.load_remaining();
    }

    let mut builder = CellBuilder::<C>::new();
    if builder.store_slice(root) {
        Some(builder.build_ext(finalizer)?)
    } else {
        None
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

fn serialize_entry<C: CellFamily, T: Store<C>>(
    entry: &T,
    finalizer: &mut dyn Finalizer<C>,
) -> Result<CellContainer<C>, Error> {
    let mut builder = CellBuilder::<C>::new();
    if entry.store_into(&mut builder, finalizer) {
        if let Some(key) = builder.build_ext(finalizer) {
            return Ok(key);
        }
    }
    Err(Error::CellOverflow)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{RcCell, RcCellBuilder};

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
            builder.store_slice(parsed_key);
            builder.build().unwrap()
        };

        // Parsed key should be equal to the original
        assert_eq!(key.as_ref(), parsed_key.as_ref());

        let label = RcCellBuilder::from_raw_data(&[0xcc, 0x40], 9)
            .unwrap()
            .build()
            .unwrap();
        let prefix = read_label(&mut label.as_slice(), 32).unwrap();

        println!("{}", build_cell(|b| b.store_slice(prefix)).display_tree());
        assert_eq!(prefix.test_uniform(), Some(false));
    }
}
