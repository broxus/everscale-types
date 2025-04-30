use crate::cell::*;
use crate::dict::{build_dict_from_sorted_iter, read_label, MergeStackItem};
use crate::error::Error;

/// Modify a dict with a sorted list of inserts/removes.
pub fn dict_modify_from_sorted_iter<K, V, T, I, FK, FV>(
    dict: &mut Option<Cell>,
    key_bit_len: u16,
    entries: I,
    mut extract_key: FK,
    mut extract_value: FV,
) -> Result<bool, Error>
where
    I: IntoIterator<Item = T>,
    K: Store + Ord,
    V: Store,
    for<'a> FK: FnMut(&'a T) -> K,
    FV: FnMut(T) -> Result<Option<V>, Error>,
{
    const STATE_UNUSED: i8 = -1;
    const STATE_USED_FULL: i8 = 2;

    struct IterItem {
        prefix: CellBuilder,
        cell: Cell,
        label: Label,
        state: i8,
        flatten: bool,
        data_offset_bits: u16,
        remaining_key_bits: u16,
    }

    enum Label {
        Inline(CellSliceRange),
        Same(CellSlice<'static>),
    }

    impl<'a> IterItem {
        fn load(prefix: CellBuilder, key_bit_len: u16, cell: Cell) -> Result<Self, Error> {
            let mut data = ok!(cell.as_slice());
            let label = ok!(read_label(&mut data, key_bit_len));
            Ok(Self {
                prefix,
                data_offset_bits: data.offset_bits(),
                remaining_key_bits: key_bit_len - label.size_bits(),
                label: if std::ptr::addr_eq(label.cell(), cell.as_ref()) {
                    Label::Inline(label.range())
                } else if let Ok(bit) = label.get_bit(0) {
                    Label::Same(label.range().apply_allow_exotic(match bit {
                        false => Cell::all_zeros_ref(),
                        true => Cell::all_ones_ref(),
                    }))
                } else {
                    Label::Inline(CellSliceRange::empty())
                },
                cell,
                state: STATE_UNUSED,
                flatten: false,
            })
        }

        fn try_add_subtrees<V: Store>(
            &self,
            until: i8,
            flatten: bool,
            res_stack: &mut Vec<MergeStackItem<V>>,
        ) -> Result<(), Error> {
            if self.remaining_key_bits == 0 {
                let mut data = CellSliceRange::full(&self.cell);
                ok!(data.skip_first(self.data_offset_bits, 0));
                let data = data.apply_allow_exotic(&self.cell);

                let mut prefix = self.prefix.clone();
                ok!(prefix.store_slice_data(self.label()));

                let lcp_len = ok!(MergeStackItem::reduce(
                    res_stack,
                    prefix.as_data_slice(),
                    prefix.size_bits(),
                    Cell::empty_context()
                ));

                res_stack.push(MergeStackItem::DenormNode {
                    prefix,
                    data: data.range(),
                    cell: self.cell.clone(),
                    prev_lcp_len: lcp_len,
                });

                // Do nothing for leaves.
                return Ok(());
            }

            let remaining_key_len = self.remaining_key_bits - 1;
            let label = self.label();

            for i in (self.state + 1)..=until {
                let Some(value) = self.cell.reference_cloned(i as u8) else {
                    return Err(Error::CellUnderflow);
                };

                let mut prefix = self.prefix.clone();
                ok!(prefix.store_slice_data(label));
                ok!(prefix.store_bit(i != 0));

                ok!(add_subtree(
                    prefix,
                    remaining_key_len,
                    value,
                    flatten || self.flatten,
                    res_stack
                ));
            }
            Ok(())
        }

        fn label(&self) -> CellSlice<'_> {
            match self.label {
                Label::Inline(range) => range.apply_allow_exotic(&self.cell),
                Label::Same(label) => label,
            }
        }
    }

    enum SeekState<'k> {
        NotFound { remaining_key: CellSlice<'k> },
        Found,
    }

    fn do_seek<'k, V: Store>(
        mut key: CellSlice<'k>,
        before_remove: bool,
        iter_stack: &mut Vec<IterItem>,
        res_stack: &mut Vec<MergeStackItem<V>>,
    ) -> Result<SeekState<'k>, Error> {
        loop {
            let item = iter_stack.last_mut().unwrap();

            // Remove the prefix from the key.
            match key.strip_data_prefix(&item.label()) {
                Some(remaining_key) => {
                    if remaining_key.is_data_empty() {
                        // All key parts were collected <=> value found.
                        debug_assert_eq!(item.state, STATE_UNUSED);
                        return Ok(SeekState::Found);
                    } else {
                        key = remaining_key;
                    }
                }
                None => return Ok(SeekState::NotFound { remaining_key: key }),
            }

            // Load next child based on the next bit.
            let child_index = ok!(key.load_bit()) as i8;
            let Some(child) = item.cell.reference_cloned(child_index as u8) else {
                return Err(Error::CellUnderflow);
            };

            // Add skipped subtrees.
            ok!(item.try_add_subtrees(child_index - 1, before_remove, res_stack));

            // Update the last visited segment state.
            debug_assert!(item.state < child_index);
            item.state = child_index;

            // Load the next child.
            let mut prefix = item.prefix.clone();
            ok!(prefix.store_slice(item.label()));
            ok!(prefix.store_bit(child_index != 0));
            let item = ok!(IterItem::load(prefix, key.size_bits(), child));

            // Add item to the iterator stack.
            iter_stack.push(item);
        }
    }

    fn seek_first<'k, V: Store>(
        root: Cell,
        key: CellSlice<'k>,
        before_remove: bool,
        iter_stack: &mut Vec<IterItem>,
        res_stack: &mut Vec<MergeStackItem<V>>,
    ) -> Result<SeekState<'k>, Error> {
        debug_assert!(iter_stack.is_empty());
        iter_stack.push(ok!(IterItem::load(
            CellBuilder::new(),
            key.size_bits(),
            root
        )));
        do_seek(key, before_remove, iter_stack, res_stack)
    }

    fn seek_next<'p, 'k, V: Store>(
        prev_key: CellSlice<'p>,
        mut key: CellSlice<'k>,
        before_remove: bool,
        iter_stack: &mut Vec<IterItem>,
        res_stack: &mut Vec<MergeStackItem<V>>,
    ) -> Result<SeekState<'k>, Error> {
        debug_assert!(!iter_stack.is_empty());

        // At this point `iter_stack` contains the path to the `prev_key`.
        let lcp = prev_key.longest_common_data_prefix(&key);
        let common_bits = lcp.size_bits();

        // Unwind iter_stack until it becomes a (partial) path to the `key`.
        let mut flatten = before_remove;
        while let Some(item) = iter_stack.last_mut() {
            let prefix_len = item.prefix.size_bits();

            // Skip all segments further than the `lcp`.
            if prefix_len > common_bits {
                let item = iter_stack.pop().unwrap();
                flatten |= item.flatten;
                if item.state != STATE_USED_FULL {
                    ok!(item.try_add_subtrees(1, flatten, res_stack));
                }
                continue;
            }

            item.flatten |= flatten;

            // At some point we must reach the segment which can contain the `key`.
            key.skip_first(prefix_len, 0)?;
            break;
        }

        // Seek for the rest.
        do_seek(key, before_remove, iter_stack, res_stack)
    }

    fn seek_end<V: Store>(
        iter_stack: &mut Vec<IterItem>,
        res_stack: &mut Vec<MergeStackItem<V>>,
    ) -> Result<(), Error> {
        let mut flatten = false;
        while let Some(item) = iter_stack.pop() {
            flatten |= item.flatten;
            if item.state != STATE_USED_FULL {
                ok!(item.try_add_subtrees(1, flatten, res_stack));
            }
        }
        Ok(())
    }

    fn add_subtree<V: Store>(
        mut prefix: CellBuilder,
        key_bit_len: u16,
        value: Cell,
        flatten: bool,
        res_stack: &mut Vec<MergeStackItem<V>>,
    ) -> Result<(), Error> {
        let full_key_bit_len = prefix.size_bits() + key_bit_len;

        if flatten {
            let mut data = ok!(value.as_slice());

            let label = ok!(read_label(&mut data, key_bit_len));
            ok!(prefix.store_slice_data(label));

            let lcp_len = ok!(MergeStackItem::reduce(
                res_stack,
                prefix.as_data_slice(),
                full_key_bit_len,
                Cell::empty_context()
            ));

            res_stack.push(MergeStackItem::DenormNode {
                prefix,
                data: data.range(),
                cell: value,
                prev_lcp_len: lcp_len,
            });
        } else {
            let lcp_len = ok!(MergeStackItem::reduce(
                res_stack,
                prefix.as_data_slice(),
                prefix.size_bits() + key_bit_len,
                Cell::empty_context()
            ));

            res_stack.push(MergeStackItem::Node {
                prefix,
                value,
                prev_lcp_len: lcp_len,
            });
        }
        Ok(())
    }

    fn add_value<V: Store>(
        key: CellBuilder,
        value: V,
        res_stack: &mut Vec<MergeStackItem<V>>,
        context: &dyn CellContext,
    ) -> Result<(), Error> {
        let lcp_len = ok!(MergeStackItem::reduce(
            res_stack,
            key.as_data_slice(),
            key.size_bits(),
            context
        ));
        res_stack.push(MergeStackItem::Leaf {
            prefix: key,
            value,
            prev_lcp_len: lcp_len,
        });
        Ok(())
    }

    let ctx = Cell::empty_context();
    let Some(root) = &*dict else {
        // The simplest case when we just need to create a new dict from the sorted iter.
        let mut err = None;
        let res = build_dict_from_sorted_iter(
            entries.into_iter().flat_map(|entry| {
                if err.is_some() {
                    return None;
                }
                let key = extract_key(&entry);
                match extract_value(entry) {
                    Ok(Some(value)) => Some((key, value)),
                    Ok(None) => None,
                    Err(e) => {
                        err = Some(e);
                        None
                    }
                }
            }),
            key_bit_len,
            ctx,
        );
        if let Some(e) = err {
            return Err(e);
        }
        *dict = ok!(res);
        return Ok(dict.is_some());
    };

    // Fallback to the full merge.

    let mut prev_key_builder = CellBuilder::new();

    let mut iter_stack = Vec::<IterItem>::new();
    let mut res_stack = Vec::<MergeStackItem<V>>::new();

    let mut prev_key = None::<K>;
    for item in entries {
        let is_first = prev_key.is_none();
        let key = extract_key(&item);
        if let Some(prev_key) = &prev_key {
            match key.cmp(prev_key) {
                // Skip duplicates
                std::cmp::Ordering::Equal => continue,
                // Allow only sorted entries
                std::cmp::Ordering::Greater => {}
                // Invalid data. TODO: Panic here?
                std::cmp::Ordering::Less => return Err(Error::InvalidData),
            }
        }

        // Build key.
        let mut key_builder = CellBuilder::new();
        ok!(key.store_into(&mut key_builder, ctx));
        prev_key = Some(key);

        if key_builder.size_bits() != key_bit_len {
            return Err(Error::InvalidData);
        }

        let key = key_builder.as_data_slice();

        let value = ok!(extract_value(item));
        let before_remove = value.is_none();

        // Update stack to contain a path to the `key`.
        let seek_state = if is_first {
            ok!(seek_first(
                root.clone(),
                key,
                before_remove,
                &mut iter_stack,
                &mut res_stack
            ))
        } else {
            ok!(seek_next(
                prev_key_builder.as_data_slice(),
                key,
                before_remove,
                &mut iter_stack,
                &mut res_stack
            ))
        };

        // Update the previous key builder.
        prev_key_builder
            .rewind(prev_key_builder.size_bits())
            .unwrap();
        debug_assert_eq!(prev_key_builder.size_bits(), 0);
        prev_key_builder.store_slice_data(key).unwrap();

        //
        let iter = iter_stack.last_mut().unwrap();
        match (seek_state, value) {
            // Add or remove value at fork.
            (SeekState::NotFound { remaining_key }, value) => {
                // Check if the new key is greater than the label in the current fork.
                if ok!(remaining_key.lex_cmp(&iter.label())).is_gt()
                    && iter.state != STATE_USED_FULL
                {
                    ok!(iter.try_add_subtrees(1, false, &mut res_stack));
                    iter.state = STATE_USED_FULL;
                }

                if let Some(value) = value {
                    ok!(add_value(key_builder, value, &mut res_stack, ctx));
                }
            }
            // Add or remove value at existing.
            (SeekState::Found, value) => {
                debug_assert_eq!(iter.remaining_key_bits, 0);

                iter.state = STATE_USED_FULL;
                if let Some(value) = value {
                    ok!(add_value(key_builder, value, &mut res_stack, ctx));
                } else {
                    iter.flatten = true;
                }
            }
        }
    }

    if prev_key.is_none() {
        return Ok(false);
    }

    ok!(seek_end(&mut iter_stack, &mut res_stack));

    let Some(mut result) = res_stack.pop() else {
        *dict = None;
        return Ok(true);
    };

    while let Some(left) = res_stack.pop() {
        let key_offset = if res_stack.is_empty() {
            0
        } else {
            left.prev_lcp_len() + 1
        };

        result = ok!(left.merge(result, key_offset, key_bit_len, ctx));
    }

    *dict = Some(ok!(result.build(key_bit_len, ctx)));
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boc::Boc;
    use crate::dict::Dict;

    #[test]
    fn mix_insert_remove() -> anyhow::Result<()> {
        let mut target = Dict::<u32, u32>::new();
        target.set(1, 1)?;
        target.set(65536, 65536)?;
        target.set(3145983, 3145983)?;
        target.set(755237119, 755237119)?;

        println!(
            "TARGET: {}",
            Boc::encode_base64(target.root.as_ref().unwrap())
        );

        for item in target.iter() {
            let (key, value) = item?;
            println!("== [{key}]: {value}");
        }

        let mut dict = Dict::<u32, u32>::new();
        dict.set(0, 0)?;
        dict.set(1, 1)?;
        dict.set(65536, 65536)?;
        dict.set(755237119, 755237119)?;

        println!(
            "INITIAL: {}",
            Boc::encode_base64(dict.root.as_ref().unwrap())
        );
        for item in dict.iter() {
            let (key, value) = item?;
            println!("== [{key}]: {value}");
        }

        dict_modify_from_sorted_iter(
            &mut dict.root,
            32,
            [(0, false), (3145983, true)],
            |(key, _)| *key,
            |(key, add)| Ok(add.then_some(key)),
        )?;

        println!(
            "RESULT: {}",
            Boc::encode_base64(dict.root.as_ref().unwrap())
        );
        for item in dict.iter() {
            let (key, value) = item?;
            println!("== [{key}]: {value}");
        }

        assert_eq!(dict.root, target.root);
        Ok(())
    }
}
