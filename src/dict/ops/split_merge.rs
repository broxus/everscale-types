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
) -> Result<Cell, Error> {
    let dict = match (&left, right) {
        (None, None) => return Err(Error::InvalidData),
        (Some(left), None) => return Ok(left.clone()),
        (None, Some(right)) => return Ok(right.clone()),
        (Some(left_cell), Some(right_cell)) => {
            let bit_len = left_cell.bit_len();
            if bit_len != right_cell.bit_len() && bit_len != key_bit_length {
                return Err(Error::InvalidCell); // KEY LENGTH ERROR?
            }

            let mut left_slice = left_cell.as_slice()?;
            let mut left_label = read_label(&mut left_slice, key_bit_length)?;

            let mut right_slice = right_cell.as_slice()?;
            let mut right_label = read_label(&mut right_slice, key_bit_length)?;

            let lcp = left_label.longest_common_data_prefix(&right_label);

            let mut new_root_builder = CellBuilder::new();
            write_label(&lcp, lcp.size_bits(), &mut new_root_builder)?;

            left_label.skip_first(lcp.size_bits(), 0)?;
            right_label.skip_first(lcp.size_bits(), 0)?;

            let (left, right) = match (left_label.load_bit()?, right_label.load_bit()?) {
                (false, true) => {
                    let left_leaf =
                        make_leaf(&left_label, left_label.size_bits(), &left_slice, context)?;
                    let right_leaf =
                        make_leaf(&right_label, right_label.size_bits(), &right_slice, context)?;
                    (left_leaf, right_leaf)
                }
                (true, false) => {
                    let left_leaf =
                        make_leaf(&right_label, right_label.size_bits(), &right_slice, context)?;
                    let right_leaf =
                        make_leaf(&left_label, left_label.size_bits(), &left_slice, context)?;
                    (left_leaf, right_leaf)
                }
                _ => return Err(Error::InvalidCell),
            };
            new_root_builder.store_reference(left)?;
            new_root_builder.store_reference(right)?;

            new_root_builder.build()?
        }
    };
    Ok(dict)
}

/// Merges two sibling dictionaries into one and returns it
pub fn sibling_aug_dict_merge(
    left: &Option<Cell>,
    right: &Option<Cell>,
    key_bit_length: u16,
    comparator: AugDictFn,
    context: &dyn CellContext,
) -> Result<Cell, Error> {
    let dict = match (&left, right) {
        (None, None) => return Err(Error::InvalidData),
        (Some(left), None) => return Ok(left.clone()),
        (None, Some(right)) => return Ok(right.clone()),
        (Some(left_cell), Some(right_cell)) => {
            let bit_len = left_cell.bit_len();
            if bit_len != right_cell.bit_len() && bit_len != key_bit_length {
                return Err(Error::InvalidCell); // KEY LENGTH ERROR?
            }

            let mut left_slice = left_cell.as_slice()?;
            let mut left_label = read_label(&mut left_slice, key_bit_length)?;

            let mut right_slice = right_cell.as_slice()?;
            let mut right_label = read_label(&mut right_slice, key_bit_length)?;

            let lcp = left_label.longest_common_data_prefix(&right_label);

            left_label.skip_first(lcp.size_bits(), 0)?;
            right_label.skip_first(lcp.size_bits(), 0)?;

            let (left, right) = match (left_label.load_bit()?, right_label.load_bit()?) {
                (false, true) => {
                    let left_leaf =
                        make_leaf(&left_label, left_label.size_bits(), &left_slice, context)?;
                    let right_leaf =
                        make_leaf(&right_label, right_label.size_bits(), &right_slice, context)?;
                    (left_leaf, right_leaf)
                }
                (true, false) => {
                    let left_leaf =
                        make_leaf(&right_label, right_label.size_bits(), &right_slice, context)?;
                    let right_leaf =
                        make_leaf(&left_label, left_label.size_bits(), &left_slice, context)?;
                    (left_leaf, right_leaf)
                }
                _ => return Err(Error::InvalidCell),
            };

            let mut new_root_builder = CellBuilder::new();
            write_label(&lcp, lcp.size_bits(), &mut new_root_builder)?;

            new_root_builder.store_reference(left)?;
            new_root_builder.store_reference(right)?;

            comparator(
                &mut left_slice,
                &mut right_slice,
                &mut new_root_builder,
                context,
            )?;

            new_root_builder.build_ext(context)?
        }
    };
    Ok(dict)
}

#[cfg(test)]
pub mod test {
    use super::*;
    use crate::dict::{AugDict, AugDictExtra, Dict};
    #[test]
    fn split_merge_test() -> anyhow::Result<()> {
        let mut dict = Dict::<u32, u32>::new();

        dict.add(1, 1)?;
        dict.add(2, 2)?;
        dict.add(3, 3)?;
        dict.add(u32::MAX - 2, 4)?;
        dict.add(u32::MAX - 1, 5)?;
        dict.add(u32::MAX, 6)?;
        println!("initial {:?}", dict.root());

        let (d1, d2) = dict.split()?;
        let cell = sibling_dict_merge(d1.root(), d2.root(), 32, Cell::empty_context())?;

        let new_dict = Dict::<u32, u32>::from_raw(Some(cell));

        for i in new_dict.iter() {
            let (k, v) = i?;
            println!("{:?} {:?}", k, v);
        }

        assert_eq!(new_dict.root(), dict.root());

        Ok(())
    }

    #[derive(Debug, Default, Load, Store, Eq, PartialEq)]
    struct OrCmp(bool);

    impl AugDictExtra for OrCmp {
        fn comp_add(
            left: &mut CellSlice,
            right: &mut CellSlice,
            b: &mut CellBuilder,
            _: &dyn CellContext,
        ) -> Result<(), Error> {
            let left = left.load_bit()?;
            let right = right.load_bit()?;
            b.store_bit(left | right)
        }
    }

    #[test]
    fn split_merge_aug_test() -> anyhow::Result<()> {
        let mut dict = AugDict::<u32, OrCmp, u32>::new();
        dict.add(1, OrCmp(true), 1)?;
        dict.add(2, OrCmp(true), 1)?;
        dict.add(3, OrCmp(true), 1)?;
        dict.add(u32::MAX - 2, OrCmp(false), 4)?;
        dict.add(u32::MAX - 1, OrCmp(false), 5)?;
        dict.add(u32::MAX, OrCmp(false), 6)?;

        let (d1, d2) = dict.split()?;

        let cell = sibling_aug_dict_merge(
            d1.dict().root(),
            d2.dict().root(),
            32,
            OrCmp::comp_add,
            Cell::empty_context(),
        )?;

        let mut new = AugDict::<u32, OrCmp, u32>::load_from_root_ext(
            &mut cell.as_slice_allow_exotic(),
            Cell::empty_context(),
        )?;
        new.update_root_extra()?;

        for i in new.iter() {
            let (k, e, v) = i?;
            println!("{:?} {:?} {:?}", k, e, v);
        }
        assert_eq!(dict, new);

        Ok(())
    }
}
