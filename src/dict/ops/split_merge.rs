use crate::cell::*;
use crate::dict::{dict_insert, read_label, write_label, RawIter, SetMode};
use crate::error::Error;

/// Splits one dictionary by the key prefix
pub fn dict_split_by_prefix(
    dict: Option<&'_ Cell>,
    key_bit_len: u16,
    key_prefix: &CellSlice,
    context: &mut dyn CellContext,
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
            match key_bit_len.checked_sub(root_label.remaining_bits() + 1) {
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
    context: &mut dyn CellContext,
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
                return Err(Error::InvalidCell); //KEY LENGTH ERROR?
            }

            let mut right_dict_iter = RawIter::new(right, key_bit_length);
            while let Some(Ok((key, value))) = right_dict_iter.next() {
                let current_bit_len = key.bit_len();

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
