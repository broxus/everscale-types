use crate::cell::*;
use crate::dict::{make_leaf, make_leaf_with_extra, write_label, AugDictFn};
use crate::error::Error;

/// Builds a new dictionary from an iterator of sorted unique entries.
///
/// It is a preferred way to build a large `Dict` as doing lots of
/// insertions is too slow.
pub fn build_dict_from_sorted_iter<K, V, I>(
    entries: I,
    key_bit_len: u16,
    context: &dyn CellContext,
) -> Result<Option<Cell>, Error>
where
    I: IntoIterator<Item = (K, V)>,
    K: Store + Ord,
    V: Store,
{
    let mut stack = Vec::<MergeStackItem<V>>::new();

    let mut prev_key = None::<K>;
    for (key, value) in entries {
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

        let mut prefix = CellBuilder::new();
        ok!(key.store_into(&mut prefix, context));
        prev_key = Some(key);

        let lcp_len = ok!(MergeStackItem::reduce(
            &mut stack,
            prefix.as_data_slice(),
            key_bit_len,
            context
        ));

        stack.push(MergeStackItem::Leaf {
            prefix,
            value,
            prev_lcp_len: lcp_len,
        });
    }

    let Some(mut result) = stack.pop() else {
        return Ok(None);
    };

    while let Some(left) = stack.pop() {
        let key_offset = if stack.is_empty() {
            0
        } else {
            left.prev_lcp_len() + 1
        };

        result = ok!(left.merge(result, key_offset, key_bit_len, context));
    }

    result.build(key_bit_len, context).map(Some)
}

pub(crate) enum MergeStackItem<V> {
    /// Leaf value to be serialized.
    Leaf {
        prefix: CellBuilder,
        value: V,
        prev_lcp_len: u16,
    },
    /// Complete node which can be used as is.
    Node {
        prefix: CellBuilder,
        value: Cell,
        prev_lcp_len: u16,
    },
    /// A subtree with a prefix.
    /// Used when we need to use the sibling of the removed branch.
    DenormNode {
        prefix: CellBuilder,
        cell: Cell,
        data: CellSliceRange,
        prev_lcp_len: u16,
    },
}

impl<V: Store> MergeStackItem<V> {
    pub fn reduce(
        res_stack: &mut Vec<Self>,
        key: CellSlice<'_>,
        key_bit_len: u16,
        context: &dyn CellContext,
    ) -> Result<u16, Error> {
        let mut lcp_len = 0;
        if let Some(last) = res_stack.last() {
            let left_prefix = last.prefix_slice();
            let right_prefix = key;

            let lcp = left_prefix.longest_common_data_prefix(&right_prefix);
            lcp_len = lcp.size_bits();

            if lcp_len <= last.prev_lcp_len() {
                // LCP decreased, we are not able to group the current item to the last one.
                // At this point we can safely reduce the stack.
                let mut right = res_stack.pop().unwrap();
                while !res_stack.is_empty() {
                    if right.prev_lcp_len() <= lcp_len {
                        break;
                    }
                    let left = res_stack.pop().unwrap();
                    let key_offset = if res_stack.is_empty() {
                        1
                    } else {
                        left.prev_lcp_len() + 1
                    }
                    .max(lcp_len + 1);

                    right = ok!(left.merge(right, key_offset, key_bit_len, context));
                }
                res_stack.push(right);
            }
        }

        Ok(lcp_len)
    }

    pub fn prefix_slice(&self) -> CellSlice<'_> {
        match self {
            Self::Leaf { prefix, .. } => prefix.as_data_slice(),
            Self::Node { prefix, .. } => prefix.as_data_slice(),
            Self::DenormNode { prefix, .. } => prefix.as_data_slice(),
        }
    }

    pub fn prev_lcp_len(&self) -> u16 {
        match self {
            Self::Leaf { prev_lcp_len, .. } => *prev_lcp_len,
            Self::Node { prev_lcp_len, .. } => *prev_lcp_len,
            Self::DenormNode { prev_lcp_len, .. } => *prev_lcp_len,
        }
    }

    pub fn build(self, key_bit_len: u16, context: &dyn CellContext) -> Result<Cell, Error> {
        match self {
            Self::Leaf { prefix, value, .. } => {
                make_leaf(&prefix.as_data_slice(), key_bit_len, &value, context)
            }
            Self::Node { value, .. } => Ok(value),
            Self::DenormNode {
                prefix, cell, data, ..
            } => {
                let data = data.apply_allow_exotic(&cell);
                make_leaf(&prefix.as_data_slice(), key_bit_len, &data, context)
            }
        }
    }

    pub fn merge(
        self,
        right: Self,
        key_offset: u16,
        key_bit_len: u16,
        context: &dyn CellContext,
    ) -> Result<Self, Error> {
        let left_offset = self.prev_lcp_len();
        let split_at = right.prev_lcp_len();

        let label_len = split_at - key_offset;
        let leaf_key_bit_len = key_bit_len - split_at - 1;
        let key_bit_len = key_bit_len - key_offset;

        let mut builder = CellBuilder::new();

        // Build the right cell and write the common prefix
        let result_prefix;
        let right_cell = match right {
            Self::Leaf { prefix, value, .. } => {
                let mut prefix_slice = prefix.as_data_slice();

                // Write the common prefix as a label
                let mut common_prefix = prefix_slice;
                ok!(common_prefix.skip_first(key_offset, 0)); // TODO: Unwrap
                ok!(write_label(
                    &common_prefix.get_prefix(label_len, 0),
                    key_bit_len,
                    &mut builder,
                ));

                // Build leaf from value
                ok!(prefix_slice.skip_first(split_at + 1, 0)); // TODO: Unwrap
                let value = ok!(make_leaf(&prefix_slice, leaf_key_bit_len, &value, context));

                result_prefix = prefix;
                value
            }
            Self::Node { prefix, value, .. } => {
                // Write the common prefix as a label
                let mut common_prefix = prefix.as_data_slice();
                ok!(common_prefix.skip_first(key_offset, 0)); // TODO: Unwrap
                ok!(write_label(
                    &common_prefix.get_prefix(label_len, 0),
                    key_bit_len,
                    &mut builder,
                ));

                // Use value as is
                result_prefix = prefix;
                value
            }
            Self::DenormNode {
                prefix, cell, data, ..
            } => {
                let mut prefix_slice = prefix.as_data_slice();

                // Write the common prefix as a label
                let mut common_prefix = prefix_slice;
                ok!(common_prefix.skip_first(key_offset, 0)); // TODO: Unwrap
                ok!(write_label(
                    &common_prefix.get_prefix(label_len, 0),
                    key_bit_len,
                    &mut builder,
                ));

                // Build leaf from value
                ok!(prefix_slice.skip_first(split_at + 1, 0)); // TODO: Unwrap
                let value = ok!(make_leaf(
                    &prefix_slice,
                    leaf_key_bit_len,
                    &data.apply_allow_exotic(&cell),
                    context
                ));

                result_prefix = prefix;
                value
            }
        };

        // Build the left cell
        let left_cell = match self {
            Self::Leaf { prefix, value, .. } => {
                let mut prefix_slice = prefix.as_data_slice();
                ok!(prefix_slice.skip_first(split_at + 1, 0)); // TODO: Unwrap
                ok!(make_leaf(&prefix_slice, leaf_key_bit_len, &value, context))
            }
            Self::Node { value, .. } => value,
            Self::DenormNode {
                prefix, cell, data, ..
            } => {
                let mut prefix_slice = prefix.as_data_slice();
                ok!(prefix_slice.skip_first(split_at + 1, 0)); // TODO: Unwrap
                ok!(make_leaf(
                    &prefix_slice,
                    leaf_key_bit_len,
                    &data.apply_allow_exotic(&cell),
                    context
                ))
            }
        };

        // Complete the node
        ok!(builder.store_reference(left_cell));
        ok!(builder.store_reference(right_cell));

        // Wrap into a new stack item
        Ok(MergeStackItem::Node {
            prefix: result_prefix,
            value: ok!(builder.build_ext(context)),
            prev_lcp_len: left_offset,
        })
    }
}

/// Builds a new augmented dictionary from an iterator of sorted unique entries.
///
/// It is a preferred way to build a large `Dict` as doing lots of
/// insertions is too slow.
///
/// TODO: Merge with `build_dict_from_sorted_iter` using some kind of `DictBuilder` trait.
pub fn build_aug_dict_from_sorted_iter<K, A, V, I>(
    entries: I,
    key_bit_len: u16,
    comparator: AugDictFn,
    context: &dyn CellContext,
) -> Result<Option<Cell>, Error>
where
    I: IntoIterator<Item = (K, A, V)>,
    K: Store + Ord,
    A: Store,
    V: Store,
{
    enum StackItem<A, V> {
        Leaf {
            prefix: CellBuilder,
            extra: A,
            value: V,
            prev_lcp_len: u16,
        },
        Node {
            prefix: CellBuilder,
            extra_offset: u16,
            value: Cell,
            prev_lcp_len: u16,
        },
    }

    impl<A: Store, V: Store> StackItem<A, V> {
        fn prefix_slice(&self) -> CellSlice<'_> {
            match self {
                Self::Leaf { prefix, .. } => prefix.as_data_slice(),
                Self::Node { prefix, .. } => prefix.as_data_slice(),
            }
        }

        fn prev_lcp_len(&self) -> u16 {
            match self {
                Self::Leaf { prev_lcp_len, .. } => *prev_lcp_len,
                Self::Node { prev_lcp_len, .. } => *prev_lcp_len,
            }
        }

        fn build(self, key_bit_len: u16, context: &dyn CellContext) -> Result<Cell, Error> {
            match self {
                Self::Leaf {
                    prefix,
                    extra,
                    value,
                    ..
                } => make_leaf_with_extra(
                    &prefix.as_data_slice(),
                    key_bit_len,
                    &extra,
                    &value,
                    context,
                ),
                Self::Node { value, .. } => Ok(value),
            }
        }

        fn merge(
            self,
            right: Self,
            key_offset: u16,
            key_bit_len: u16,
            comparator: AugDictFn,
            context: &dyn CellContext,
        ) -> Result<Self, Error> {
            let left_offset = self.prev_lcp_len();
            let split_at = right.prev_lcp_len();

            let label_len = split_at - key_offset;
            let leaf_key_bit_len = key_bit_len - split_at - 1;
            let key_bit_len = key_bit_len - key_offset;

            let mut builder = CellBuilder::new();

            // Build the right cell and write the common prefix
            let right_extra_offset;
            let result_prefix;
            let right_cell = match right {
                Self::Leaf {
                    prefix,
                    extra,
                    value,
                    ..
                } => {
                    let mut prefix_slice = prefix.as_data_slice();

                    // Write the common prefix as a label
                    let mut common_prefix = prefix_slice;
                    ok!(common_prefix.skip_first(key_offset, 0)); // TODO: Unwrap
                    ok!(write_label(
                        &common_prefix.get_prefix(label_len, 0),
                        key_bit_len,
                        &mut builder,
                    ));

                    // Build leaf from value
                    ok!(prefix_slice.skip_first(split_at + 1, 0)); // TODO: Unwrap
                    let value = {
                        let mut builder = CellBuilder::new();
                        ok!(write_label(&prefix_slice, leaf_key_bit_len, &mut builder));
                        right_extra_offset = (builder.size_bits(), 0u8);
                        ok!(extra.store_into(&mut builder, context));
                        ok!(value.store_into(&mut builder, context));
                        ok!(builder.build_ext(context))
                    };

                    result_prefix = prefix;
                    value
                }
                Self::Node {
                    prefix,
                    extra_offset,
                    value,
                    ..
                } => {
                    // Write the common prefix as a label
                    let mut common_prefix = prefix.as_data_slice();
                    ok!(common_prefix.skip_first(key_offset, 0)); // TODO: Unwrap
                    ok!(write_label(
                        &common_prefix.get_prefix(label_len, 0),
                        key_bit_len,
                        &mut builder,
                    ));

                    // Use value as is
                    right_extra_offset = (extra_offset, 2u8);
                    result_prefix = prefix;
                    value
                }
            };

            // Build the left cell
            let left_extra_offset;
            let left_cell = match self {
                Self::Leaf {
                    prefix,
                    extra,
                    value,
                    ..
                } => {
                    let mut prefix_slice = prefix.as_data_slice();
                    ok!(prefix_slice.skip_first(split_at + 1, 0)); // TODO: Unwrap

                    let mut builder = CellBuilder::new();
                    ok!(write_label(&prefix_slice, leaf_key_bit_len, &mut builder));
                    left_extra_offset = (builder.size_bits(), 0u8);
                    ok!(extra.store_into(&mut builder, context));
                    ok!(value.store_into(&mut builder, context));
                    ok!(builder.build_ext(context))
                }
                Self::Node {
                    extra_offset,
                    value,
                    ..
                } => {
                    left_extra_offset = (extra_offset, 2u8);
                    value
                }
            };

            // Complete the node
            ok!(builder.store_reference(left_cell.clone()));
            ok!(builder.store_reference(right_cell.clone()));

            let extra_offset = builder.size_bits();

            let mut left_extra_slice = ok!(left_cell.as_slice());
            left_extra_slice
                .skip_first(left_extra_offset.0, left_extra_offset.1)
                .ok();

            let mut right_extra_slice = ok!(right_cell.as_slice());
            right_extra_slice
                .skip_first(right_extra_offset.0, right_extra_offset.1)
                .ok();

            ok!(comparator(
                &mut left_extra_slice,
                &mut right_extra_slice,
                &mut builder,
                context
            ));

            // Wrap into a new stack item
            Ok(StackItem::Node {
                prefix: result_prefix,
                extra_offset,
                value: ok!(builder.build_ext(context)),
                prev_lcp_len: left_offset,
            })
        }
    }

    let mut stack = Vec::<StackItem<A, V>>::new();

    let mut prev_key = None::<K>;
    for (key, extra, value) in entries {
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

        let mut prefix = CellBuilder::new();
        ok!(key.store_into(&mut prefix, context));
        prev_key = Some(key);

        let mut lcp_len = 0;
        if let Some(last) = stack.last() {
            let left_prefix = last.prefix_slice();
            let right_prefix = prefix.as_data_slice();

            let lcp = left_prefix.longest_common_data_prefix(&right_prefix);
            lcp_len = lcp.size_bits();

            if lcp_len <= last.prev_lcp_len() {
                // LCP decreased, we are not able to group the current item to the last one.
                // At this point we can safely reduce the stack.
                let mut right = stack.pop().unwrap();
                while !stack.is_empty() {
                    if right.prev_lcp_len() <= lcp_len {
                        break;
                    }
                    let left = stack.pop().unwrap();
                    let key_offset = if stack.is_empty() {
                        1
                    } else {
                        left.prev_lcp_len() + 1
                    }
                    .max(lcp_len + 1);

                    right = ok!(left.merge(right, key_offset, key_bit_len, comparator, context));
                }
                stack.push(right);
            }
        }

        stack.push(StackItem::Leaf {
            prefix,
            extra,
            value,
            prev_lcp_len: lcp_len,
        });
    }

    let Some(mut result) = stack.pop() else {
        return Ok(None);
    };

    while let Some(left) = stack.pop() {
        let key_offset = if stack.is_empty() {
            0
        } else {
            left.prev_lcp_len() + 1
        };

        result = ok!(left.merge(result, key_offset, key_bit_len, comparator, context));
    }

    result.build(key_bit_len, context).map(Some)
}
