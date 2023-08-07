//! Dictionary implementation.

use crate::cell::*;
use crate::error::Error;
use crate::util::unlikely;

pub use aug::*;
pub use raw::*;
pub use typed::*;

mod aug;
mod raw;
mod typed;

/// Type which can be used as a dictionary key.
pub trait DictKey: Sized {
    /// Length in bits for a dictionary key.
    const BITS: u16;

    /// Creates a key from a raw builder data.
    fn from_raw_data(raw_data: &[u8; 128]) -> Option<Self>;
}

macro_rules! impl_dict_key {
    ($($ty:ty => $bits:literal => |$raw_data:ident| $expr:expr),*,) => {
        $(impl DictKey for $ty {
            const BITS: u16 = $bits;

            #[inline]
            fn from_raw_data($raw_data: &[u8; 128]) -> Option<Self> {
                Some($expr)
            }
        })*
    };
}

impl_dict_key! {
    bool => 1 => |d| d[0] & 0x80 != 0,
    u8 => 8 => |d| d[0],
    i8 => 8 => |d| d[0] as i8,
    u16 => 16 => |d| u16::from_be_bytes([d[0], d[1]]),
    i16 => 16 => |d| i16::from_be_bytes([d[0], d[1]]),
    u32 => 32 => |d| u32::from_be_bytes(d[..4].try_into().unwrap()),
    i32 => 32 => |d| i32::from_be_bytes(d[..4].try_into().unwrap()),
    u64 => 64 => |d| u64::from_be_bytes(d[..8].try_into().unwrap()),
    i64 => 64 => |d| i64::from_be_bytes(d[..8].try_into().unwrap()),
    u128 => 128 => |d| u128::from_be_bytes(d[..16].try_into().unwrap()),
    i128 => 128 => |d| i128::from_be_bytes(d[..16].try_into().unwrap()),
    [u8; 16] => 128 => |d| d[..16].try_into().unwrap(),
    [u8; 20] => 160 => |d| d[..20].try_into().unwrap(),
    [u8; 32] => 256 => |d| d[..32].try_into().unwrap(),
    HashBytes => 256 => |d| HashBytes(d[..32].try_into().unwrap()),
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

/// Removes the value associated with key in dictionary.
/// Returns a tuple with a new dictionary cell and an optional removed value.
pub fn dict_remove_owned(
    root: &Option<Cell>,
    key: &mut CellSlice,
    key_bit_len: u16,
    allow_subtree: bool,
    finalizer: &mut dyn Finalizer,
) -> Result<(Option<Cell>, Option<CellSliceParts>), Error> {
    if !allow_subtree && key.remaining_bits() != key_bit_len {
        return Err(Error::CellUnderflow);
    }

    let Some(root) = root else {
        return Ok((None, None));
    };
    let mut data = root.as_ref();

    let mut stack = Vec::<Segment>::new();

    // Find the node with value
    let mut prev_key_bit_len = key.remaining_bits();
    let removed = loop {
        let mut remaining_data = ok!(data.as_slice());

        // Read the next part of the key from the current data
        let prefix = &mut ok!(read_label(&mut remaining_data, key.remaining_bits()));

        // Match the prefix with the key
        let lcp = key.longest_common_data_prefix(prefix);
        match lcp.remaining_bits().cmp(&key.remaining_bits()) {
            // If all bits match, an existing value was found
            std::cmp::Ordering::Equal => break remaining_data.range(),
            // LCP is less than prefix, an edge to slice was found
            std::cmp::Ordering::Less if lcp.remaining_bits() < prefix.remaining_bits() => {
                return Ok((Some(root.clone()), None))
            }
            // The key contains the entire prefix, but there are still some bits left
            std::cmp::Ordering::Less => {
                // Fail fast if there are not enough references in the fork
                if data.reference_count() != 2 {
                    return Err(Error::CellUnderflow);
                }

                // Remove the LCP from the key
                prev_key_bit_len = key.remaining_bits();
                key.try_advance(lcp.remaining_bits(), 0);

                // Load the next branch
                let next_branch = match key.load_bit() {
                    Ok(false) => Branch::Left,
                    Ok(true) => Branch::Right,
                    Err(e) => return Err(e),
                };

                let child = match data.reference(next_branch as u8) {
                    Some(child) => {
                        // Handle pruned branch access
                        if unlikely(child.descriptor().is_pruned_branch()) {
                            return Err(Error::PrunedBranchAccess);
                        }
                        child
                    }
                    None => return Err(Error::CellUnderflow),
                };

                // Push an intermediate edge to the stack
                stack.push(Segment { data, next_branch });
                data = child;
            }
            std::cmp::Ordering::Greater => {
                debug_assert!(false, "LCP of prefix and key can't be greater than key");
                unsafe { std::hint::unreachable_unchecked() };
            }
        }
    };

    // Rebuild the leaf node
    let (mut leaf, removed) = if let Some(last) = stack.pop() {
        let index = last.next_branch as u8;

        // Load value branch
        let Some(value) = last.data.reference_cloned(index) else {
            return Err(Error::CellUnderflow);
        };

        // Load parent label
        let pfx = {
            // SAFETY: `last.data` was already checked for pruned branch access.
            let mut parent = unsafe { last.data.as_slice_unchecked() };
            ok!(read_label(&mut parent, prev_key_bit_len))
        };

        // Load the opposite branch
        let mut opposite = ok!(last.data.get_reference_as_slice(1 - index));
        let rem = ok!(read_label(&mut opposite, key.remaining_bits()));

        // Build an edge cell
        let mut builder = CellBuilder::new();
        ok!(write_label_parts(
            &pfx,
            index == 0,
            &rem,
            prev_key_bit_len,
            &mut builder
        ));
        ok!(builder.store_slice(opposite));
        let leaf = ok!(builder.build_ext(finalizer));

        // Return the new cell and the removed one
        (leaf, (value, removed))
    } else {
        return Ok((None, Some((root.clone(), removed))));
    };

    // Rebuild the tree starting from leaves
    while let Some(last) = stack.pop() {
        // Load the opposite branch
        let (left, right) = match last.next_branch {
            Branch::Left => match last.data.reference_cloned(1) {
                Some(cell) => (leaf, cell),
                None => return Err(Error::CellUnderflow),
            },
            Branch::Right => match last.data.reference_cloned(0) {
                Some(cell) => (cell, leaf),
                None => return Err(Error::CellUnderflow),
            },
        };

        let mut builder = CellBuilder::new();
        ok!(builder.store_cell_data(last.data));
        ok!(builder.store_reference(left));
        ok!(builder.store_reference(right));
        leaf = ok!(builder.build_ext(finalizer));
    }

    Ok((Some(leaf), Some(removed)))
}

/// Inserts the value associated with key in dictionary
/// in accordance with the logic of the specified [`SetMode`].
pub fn dict_insert(
    root: &Option<Cell>,
    key: &mut CellSlice,
    key_bit_len: u16,
    value: &CellSlice,
    mode: SetMode,
    finalizer: &mut dyn Finalizer,
) -> Result<Option<Cell>, Error> {
    // Creates a leaf node
    fn make_leaf(
        key: &CellSlice,
        key_bit_len: u16,
        value: &CellSlice,
        finalizer: &mut dyn Finalizer,
    ) -> Result<Cell, Error> {
        let mut builder = CellBuilder::new();
        ok!(write_label(key, key_bit_len, &mut builder));
        ok!(builder.store_slice(value));
        builder.build_ext(finalizer)
    }

    // Splits an edge or leaf
    fn split(
        data: &CellSlice,
        prefix: &mut CellSlice,
        lcp: &CellSlice,
        key: &mut CellSlice,
        value: &CellSlice,
        finalizer: &mut dyn Finalizer,
    ) -> Result<Cell, Error> {
        // Advance the key
        let prev_key_bit_len = key.remaining_bits();
        if !key.try_advance(lcp.remaining_bits() + 1, 0) {
            return Err(Error::CellUnderflow);
        }

        // Read the next bit from the data
        prefix.try_advance(lcp.remaining_bits(), 0);
        let old_to_right = ok!(prefix.load_bit());

        // Create a leaf for the old value
        let mut left = ok!(make_leaf(prefix, key.remaining_bits(), data, finalizer));
        // Create a leaf for the right value
        let mut right = ok!(make_leaf(key, key.remaining_bits(), value, finalizer));

        // The part that starts with 1 goes to the right cell
        if old_to_right {
            std::mem::swap(&mut left, &mut right);
        }

        // Create fork
        let mut builder = CellBuilder::new();
        ok!(write_label(lcp, prev_key_bit_len, &mut builder));
        ok!(builder.store_reference(left));
        ok!(builder.store_reference(right));
        builder.build_ext(finalizer)
    }

    if key.remaining_bits() != key_bit_len {
        return Err(Error::CellUnderflow);
    }

    let mut data = match root.as_ref() {
        Some(data) => data.as_ref(),
        None if mode.can_add() => {
            let data = ok!(make_leaf(key, key_bit_len, value, finalizer));
            return Ok(Some(data));
        }
        None => return Ok(None),
    };

    let mut stack = Vec::<Segment>::new();

    let mut leaf = loop {
        let mut remaining_data = ok!(data.as_slice());

        // Read the next part of the key from the current data
        let prefix = &mut ok!(read_label(&mut remaining_data, key.remaining_bits()));

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
                if data.reference_count() != 2 {
                    return Err(Error::CellUnderflow);
                }

                // Remove the LCP from the key
                key.try_advance(lcp.remaining_bits(), 0);

                // Load the next branch
                let next_branch = match key.load_bit() {
                    Ok(false) => Branch::Left,
                    Ok(true) => Branch::Right,
                    Err(e) => return Err(e),
                };

                let child = match data.reference(next_branch as u8) {
                    Some(child) => {
                        // Handle pruned branch access
                        if unlikely(child.descriptor().is_pruned_branch()) {
                            return Err(Error::PrunedBranchAccess);
                        }
                        child
                    }
                    None => return Err(Error::CellUnderflow),
                };

                // Push an intermediate edge to the stack
                stack.push(Segment { data, next_branch });
                data = child;
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
            Branch::Left => match last.data.reference_cloned(1) {
                Some(cell) => (leaf, cell),
                None => return Err(Error::CellUnderflow),
            },
            Branch::Right => match last.data.reference_cloned(0) {
                Some(cell) => (cell, leaf),
                None => return Err(Error::CellUnderflow),
            },
        };

        let mut builder = CellBuilder::new();
        ok!(builder.store_cell_data(last.data));
        ok!(builder.store_reference(left));
        ok!(builder.store_reference(right));
        leaf = ok!(builder.build_ext(finalizer));
    }

    Ok(Some(leaf))
}

/// Returns a `CellSlice` of the value corresponding to the key.
pub fn dict_get<'a: 'b, 'b>(
    root: &'a Option<Cell>,
    key_bit_len: u16,
    mut key: CellSlice<'b>,
) -> Result<Option<CellSlice<'a>>, Error> {
    if key.remaining_bits() != key_bit_len {
        return Err(Error::CellUnderflow);
    }

    let mut data = match root.as_ref() {
        Some(data) => ok!(data.as_slice()),
        None => return Ok(None),
    };

    // Try to find the required leaf
    let is_key_empty = loop {
        // Read the key part written in the current edge
        let prefix = ok!(read_label(&mut data, key.remaining_bits()));

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
        let child_index = ok!(key.load_bit()) as u8;
        data = ok!(data.cell().get_reference_as_slice(child_index));
    };

    // Return the last slice as data
    Ok(if is_key_empty { Some(data) } else { None })
}

/// Returns cell slice parts of the value corresponding to the key.
pub fn dict_get_owned(
    root: &Option<Cell>,
    key_bit_len: u16,
    mut key: CellSlice<'_>,
) -> Result<Option<CellSliceParts>, Error> {
    if key.remaining_bits() != key_bit_len {
        return Err(Error::CellUnderflow);
    }

    let Some(root) = root else {
        return Ok(None);
    };
    let mut data = ok!(root.as_slice());
    let mut prev = None;

    // Try to find the required leaf
    let is_key_empty = loop {
        // Read the key part written in the current edge
        let prefix = ok!(read_label(&mut data, key.remaining_bits()));

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
        let child_index = ok!(key.load_bit()) as u8;
        prev = Some((data.cell(), child_index));
        data = ok!(data.cell().get_reference_as_slice(child_index));
    };

    // Return the last slice as data
    Ok(if is_key_empty {
        Some(match prev {
            Some((prev, child_index)) => {
                let cell = match prev.reference_cloned(child_index) {
                    Some(cell) => cell,
                    None => return Err(Error::CellUnderflow),
                };
                (cell, data.range())
            }
            None => (root.clone(), data.range()),
        })
    } else {
        None
    })
}

/// Loads a non-empty dictionary from the root cell.
pub fn dict_load_from_root(
    slice: &mut CellSlice<'_>,
    key_bit_len: u16,
    finalizer: &mut dyn Finalizer,
) -> Result<Cell, Error> {
    let mut root = *slice;

    let label = ok!(read_label(slice, key_bit_len));
    if label.remaining_bits() != key_bit_len {
        if !slice.try_advance(0, 2) {
            return Err(Error::CellUnderflow);
        }
        let root_bits = root.remaining_bits() - slice.remaining_bits();
        let root_refs = root.remaining_refs() - slice.remaining_refs();
        root = root.get_prefix(root_bits, root_refs)
    } else {
        slice.load_remaining();
    }

    let mut builder = CellBuilder::new();
    ok!(builder.store_slice(root));
    builder.build_ext(finalizer)
}

#[derive(Clone, Copy)]
struct Segment<'a> {
    data: &'a DynCell,
    next_branch: Branch,
}

fn write_label(key: &CellSlice, key_bit_len: u16, label: &mut CellBuilder) -> Result<(), Error> {
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
        ok!(write_hml_short_tag(remaining_bits, label));
    } else if hml_long_len <= MAX_BIT_LEN {
        ok!(write_hml_long_tag(remaining_bits, bits_for_len, label));
    } else {
        return Err(Error::InvalidData);
    }
    label.store_slice_data(key)
}

fn write_label_parts(
    pfx: &CellSlice,
    bit: bool,
    rem: &CellSlice,
    key_bit_len: u16,
    label: &mut CellBuilder,
) -> Result<(), Error> {
    if key_bit_len == 0 {
        return write_hml_empty(label);
    }

    let bits_for_len = (16 - key_bit_len.leading_zeros()) as u16;

    let remaining_bits = pfx.remaining_bits() + 1 + rem.remaining_bits();

    let hml_short_len = 2 + 2 * remaining_bits;
    let hml_long_len = 2 + bits_for_len + remaining_bits;
    let hml_same_len = 3 + bits_for_len;

    if hml_same_len < hml_long_len && hml_same_len < hml_short_len {
        if let Some(pfx_bit) = pfx.test_uniform() {
            if pfx_bit == bit {
                if let Some(rem_bit) = rem.test_uniform() {
                    if rem_bit == bit {
                        return write_hml_same(bit, remaining_bits, bits_for_len, label);
                    }
                }
            }
        }
    }

    if hml_short_len <= MAX_BIT_LEN && hml_short_len <= hml_long_len {
        ok!(write_hml_short_tag(remaining_bits, label));
    } else if hml_long_len <= MAX_BIT_LEN {
        ok!(write_hml_long_tag(remaining_bits, bits_for_len, label));
    } else {
        return Err(Error::InvalidData);
    }
    ok!(label.store_slice_data(pfx));
    ok!(label.store_bit(bit));
    label.store_slice_data(rem)
}

fn read_label<'a>(label: &mut CellSlice<'a>, key_bit_len: u16) -> Result<CellSlice<'a>, Error> {
    let bits_for_len = (16 - key_bit_len.leading_zeros()) as u16;

    if label.is_data_empty() && bits_for_len == 0 {
        Ok(label.get_prefix(0, 0))
    } else if !ok!(label.load_bit()) {
        read_hml_short(label)
    } else if !ok!(label.load_bit()) {
        read_hml_long(label, bits_for_len)
    } else {
        read_hml_same(label, bits_for_len)
    }
}

fn write_hml_empty(label: &mut CellBuilder) -> Result<(), Error> {
    label.store_zeros(2)
}

fn write_hml_short_tag(len: u16, label: &mut CellBuilder) -> Result<(), Error> {
    ok!(label.store_bit_zero());

    for _ in 0..len / 32 {
        ok!(label.store_u32(u32::MAX));
    }

    let rem = len % 32;
    if rem != 0 {
        ok!(label.store_uint(u64::MAX, rem));
    }
    label.store_bit_zero()
}

fn read_hml_short<'a>(label: &mut CellSlice<'a>) -> Result<CellSlice<'a>, Error> {
    let mut len = 0;
    while ok!(label.load_bit()) {
        len += 1;
    }
    let result = *label;
    if label.try_advance(len, 0) {
        Ok(result.get_prefix(len, 0))
    } else {
        Err(Error::CellUnderflow)
    }
}

fn write_hml_long_tag(len: u16, bits_for_len: u16, label: &mut CellBuilder) -> Result<(), Error> {
    ok!(label.store_bit_one());
    ok!(label.store_bit_zero());
    label.store_uint(len as u64, bits_for_len)
}

fn read_hml_long<'a>(label: &mut CellSlice<'a>, bits_for_len: u16) -> Result<CellSlice<'a>, Error> {
    let len = ok!(label.load_uint(bits_for_len)) as u16;
    let result = *label;
    if label.try_advance(len, 0) {
        Ok(result.get_prefix(len, 0))
    } else {
        Err(Error::CellUnderflow)
    }
}

fn write_hml_same(
    bit: bool,
    len: u16,
    bits_for_len: u16,
    label: &mut CellBuilder,
) -> Result<(), Error> {
    ok!(label.store_small_uint(0b110 | bit as u8, 3));
    label.store_uint(len as u64, bits_for_len)
}

fn read_hml_same<'a>(label: &mut CellSlice<'a>, bits_for_len: u16) -> Result<CellSlice<'a>, Error> {
    let cell = match ok!(label.load_bit()) {
        false => Cell::all_zeros_ref(),
        true => Cell::all_ones_ref(),
    };
    let len = ok!(label.load_uint(bits_for_len)) as u16;

    // SAFETY: cell is a static ordinary cell
    let slice = unsafe { cell.as_slice_unchecked() };
    Ok(slice.get_prefix(len, 0))
}

fn serialize_entry<T: Store>(entry: &T, finalizer: &mut dyn Finalizer) -> Result<Cell, Error> {
    let mut builder = CellBuilder::new();
    ok!(entry.store_into(&mut builder, finalizer));
    builder.build_ext(finalizer)
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Branch {
    // Branch for a key part that starts with bit 0
    Left = 0,
    // Branch for a key part that starts with bit 1
    Right = 1,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn build_cell<F: FnOnce(&mut CellBuilder) -> Result<(), Error>>(f: F) -> Cell {
        let mut builder = CellBuilder::new();
        f(&mut builder).unwrap();
        builder.build().unwrap()
    }

    #[test]
    fn labels() -> anyhow::Result<()> {
        let key_bit_len = 6;

        // Build key
        let key = {
            let mut builder = CellBuilder::new();
            builder.store_zeros(5)?;
            builder.store_bit_one()?;
            builder.build()?
        };

        // Build label
        let label = {
            let mut builder = CellBuilder::new();
            write_label(&key.as_slice()?, key_bit_len, &mut builder)?;
            builder.build().unwrap()
        };

        // Parse label
        let parsed_key = read_label(&mut label.as_slice()?, key_bit_len)?;
        let parsed_key = {
            let mut builder = CellBuilder::new();
            builder.store_slice(parsed_key)?;
            builder.build()?
        };

        // Parsed key should be equal to the original
        assert_eq!(key.as_ref(), parsed_key.as_ref());

        let label = CellBuilder::from_raw_data(&[0xcc, 0x40], 9)
            .unwrap()
            .build()
            .unwrap();
        let prefix = read_label(&mut label.as_slice()?, 32).unwrap();

        println!("{}", build_cell(|b| b.store_slice(prefix)).display_tree());
        assert_eq!(prefix.test_uniform(), Some(false));

        Ok(())
    }
}
