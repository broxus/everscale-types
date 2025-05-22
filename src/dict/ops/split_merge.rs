use crate::cell::*;
use crate::dict::{dict_insert, make_leaf, read_label, write_label, AugDictFn, RawIter, SetMode};
use crate::error::Error;

/// Splits one dictionary by the key prefix
pub fn dict_split_by_prefix(
    dict: Option<&'_ Cell>,
    key_bit_len: u16,
    key_prefix: &CellSlice,
    context: &dyn CellContext,
) -> Result<(Option<Cell>, Option<Cell>), Error> {
    if key_bit_len == 0 {
        return Ok((None, None));
    }

    let mut remaining_data = match dict {
        Some(data) => ok!(context
            .load_dyn_cell(data.as_ref(), LoadMode::Full)
            .and_then(CellSlice::new)),
        None => return Ok((None, None)),
    };

    let root_label = ok!(read_label(&mut remaining_data, key_bit_len));
    let subdict_bit_len = match root_label.strip_data_prefix(key_prefix) {
        // Root label == key prefix
        Some(root_label_rem) if root_label_rem.is_data_empty() => {
            match key_bit_len.checked_sub(root_label.size_bits() + 1) {
                Some(bit_len) => bit_len,
                None => return Err(Error::CellUnderflow),
            }
        }
        // Root label > key prefix
        Some(root_label_rem) => {
            let mut left = dict.cloned();
            let mut right = None;
            if ok!(root_label_rem.get_bit(0)) {
                std::mem::swap(&mut left, &mut right);
            }
            return Ok((left, right));
        }
        // Root label < key prefix
        None => return Err(Error::CellUnderflow),
    };

    let mut rebuild_branch = |bit: bool| -> Result<Cell, Error> {
        let mut branch = ok!(context
            .load_dyn_cell(ok!(remaining_data.load_reference()), LoadMode::Full)
            .and_then(CellSlice::new));

        let label = ok!(read_label(&mut branch, subdict_bit_len));

        let mut key_builder = CellBuilder::new();
        ok!(key_builder.store_slice(key_prefix));
        ok!(key_builder.store_bit(bit));
        ok!(key_builder.store_slice_data(label));
        let key = key_builder.as_data_slice();

        let mut builder = CellBuilder::new();
        ok!(write_label(&key, key_bit_len, &mut builder));
        ok!(builder.store_slice(branch));
        builder.build()
    };

    let left_branch = ok!(rebuild_branch(false));
    let right_branch = ok!(rebuild_branch(true));
    Ok((Some(left_branch), Some(right_branch)))
}

/// Merges two dictionaries into one (left)
///
/// TODO: Optimize
pub fn dict_merge(
    left: &mut Option<Cell>,
    right: &Option<Cell>,
    key_bit_length: u16,
    context: &dyn CellContext,
) -> Result<(), Error> {
    match (&left, right) {
        (None, None) | (Some(_), None) => return Ok(()),
        (None, Some(right)) => {
            *left = Some(right.clone());
            return Ok(());
        }
        (Some(left_cell), Some(right_cell)) => {
            let bit_len = left_cell.bit_len();
            if bit_len != right_cell.bit_len() && bit_len != key_bit_length {
                return Err(Error::InvalidCell); // KEY LENGTH ERROR?
            }

            let mut right_dict_iter = RawIter::new(right, key_bit_length);
            while let Some(Ok((key, value))) = right_dict_iter.next() {
                let current_bit_len = key.size_bits();

                dict_insert(
                    left,
                    &mut key.as_data_slice(),
                    current_bit_len,
                    &value,
                    SetMode::Set,
                    context,
                )?;
            }
        }
    }
    Ok(())
}

/// Merges two sibling dictionaries into one and returns it
pub fn sibling_dict_merge(
    left: &Option<Cell>,
    right: &Option<Cell>,
    key_bit_length: u16,
    context: &dyn CellContext,
) -> Result<Option<Cell>, Error> {
    let dict = match (&left, right) {
        (None, None) => return Ok(None),
        (Some(left), None) => return Ok(Some(left.clone())),
        (None, Some(right)) => return Ok(Some(right.clone())),
        (Some(left_cell), Some(right_cell)) => {
            let mut left_slice = left_cell.as_slice()?;
            let mut left_label = read_label(&mut left_slice, key_bit_length)?;

            let mut right_slice = right_cell.as_slice()?;
            let mut right_label = read_label(&mut right_slice, key_bit_length)?;

            let min_label_len = std::cmp::min(left_label.size_bits(), right_label.size_bits());
            if min_label_len == 0 {
                return Err(Error::InvalidCell);
            }

            let lcp = left_label.longest_common_data_prefix(&right_label);
            if lcp.size_bits() >= min_label_len || key_bit_length < lcp.size_bits() + 1 {
                return Err(Error::InvalidCell);
            }

            left_label.skip_first(lcp.size_bits(), 0)?;
            right_label.skip_first(lcp.size_bits(), 0)?;
            let remaining_kbl = key_bit_length - 1 - lcp.size_bits();

            if left_label.load_bit()? || !right_label.load_bit()? {
                return Err(Error::InvalidData);
            }

            let left = make_leaf(&left_label, remaining_kbl, &left_slice, context)?;
            let right = make_leaf(&right_label, remaining_kbl, &right_slice, context)?;

            let mut new_root_builder = CellBuilder::new();
            write_label(&lcp, key_bit_length, &mut new_root_builder)?;

            new_root_builder.store_reference(left)?;
            new_root_builder.store_reference(right)?;

            new_root_builder.build()?
        }
    };
    Ok(Some(dict))
}

/// Merges two sibling dictionaries into one and returns it
pub fn sibling_aug_dict_merge(
    left: &Option<Cell>,
    right: &Option<Cell>,
    key_bit_length: u16,
    comparator: AugDictFn,
    context: &dyn CellContext,
) -> Result<Option<Cell>, Error> {
    let dict = match (&left, right) {
        (None, None) => return Ok(None),
        (Some(left), None) => return Ok(Some(left.clone())),
        (None, Some(right)) => return Ok(Some(right.clone())),
        (Some(left_cell), Some(right_cell)) => {
            let mut left_slice = left_cell.as_slice()?;
            let mut left_label = read_label(&mut left_slice, key_bit_length)?;

            let mut right_slice = right_cell.as_slice()?;
            let mut right_label = read_label(&mut right_slice, key_bit_length)?;

            let min_label_len = std::cmp::min(left_label.size_bits(), right_label.size_bits());
            if min_label_len == 0 {
                return Err(Error::InvalidData);
            }

            let lcp = left_label.longest_common_data_prefix(&right_label);
            if lcp.size_bits() >= min_label_len || key_bit_length < lcp.size_bits() + 1 {
                return Err(Error::InvalidData);
            }

            left_label.skip_first(lcp.size_bits(), 0)?;
            right_label.skip_first(lcp.size_bits(), 0)?;
            let remaining_kbl = key_bit_length - 1 - lcp.size_bits();

            if left_label.load_bit()? || !right_label.load_bit()? {
                return Err(Error::InvalidData);
            }

            let left = make_leaf(&left_label, remaining_kbl, &left_slice, context)?;
            let right = make_leaf(&right_label, remaining_kbl, &right_slice, context)?;

            let mut new_root_builder = CellBuilder::new();
            write_label(&lcp, key_bit_length, &mut new_root_builder)?;

            new_root_builder.store_reference(left)?;
            new_root_builder.store_reference(right)?;

            if left_label.size_bits() < remaining_kbl {
                left_slice.skip_first(0, 2)?
            }

            if right_label.size_bits() < remaining_kbl {
                right_slice.skip_first(0, 2)?
            }

            comparator(
                &mut left_slice,
                &mut right_slice,
                &mut new_root_builder,
                context,
            )?;

            new_root_builder.build_ext(context)?
        }
    };
    Ok(Some(dict))
}
