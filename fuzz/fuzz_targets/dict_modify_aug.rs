#![no_main]
use arbitrary::Arbitrary;
use everscale_types::dict::{self, AugDictExtra};
use everscale_types::error::Error;
use everscale_types::prelude::*;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|input: Input<1000, u32, SimpleAug, u64>| compare_manual_vs_batched(input));

fn compare_manual_vs_batched<const MAX_N: usize, K, A, V>(input: Input<MAX_N, K, A, V>)
where
    K: StoreDictKey + Ord + Copy,
    for<'a> A: AugDictExtra + Store + Load<'a>,
    V: Store,
{
    let ctx = Cell::empty_context();

    let initial =
        dict::build_aug_dict_from_sorted_iter(input.initial_items.into_iter(), A::comp_add, ctx)
            .unwrap();

    // Build manually
    let mut target = initial.clone();
    for op in &input.operations {
        let mut b = CellDataBuilder::new();
        match op {
            Operation::Remove { key } => {
                key.store_into_data(&mut b).unwrap();
                dict::aug_dict_remove_owned(
                    &mut target,
                    &mut b.as_data_slice(),
                    K::BITS,
                    false,
                    A::comp_add,
                    ctx,
                )
                .unwrap();
            }
            Operation::Insert { key, extra, value } => {
                key.store_into_data(&mut b).unwrap();
                dict::aug_dict_insert(
                    &mut target,
                    &mut b.as_data_slice(),
                    K::BITS,
                    extra,
                    value,
                    dict::SetMode::Set,
                    A::comp_add,
                    ctx,
                )
                .unwrap();
            }
        }
    }

    // Build batched
    let mut result = initial.clone();
    dict::aug_dict_modify_from_sorted_iter(
        &mut result,
        input.operations,
        |op| *op.key(),
        |op| {
            Ok(match op {
                Operation::Remove { .. } => None,
                Operation::Insert { extra, value, .. } => Some((extra, value)),
            })
        },
        A::comp_add,
        ctx,
    )
    .unwrap();

    //
    assert_eq!(result, target);
}

#[derive(Default, Debug, Store, Load, Clone, Copy, Arbitrary)]
struct SimpleAug(u32);

impl AugDictExtra for SimpleAug {
    fn comp_add(
        left: &mut CellSlice,
        right: &mut CellSlice,
        b: &mut CellBuilder,
        _: &dyn CellContext,
    ) -> Result<(), Error> {
        let left = left.load_u32()?;
        let right = right.load_u32()?;
        b.store_u32(left.saturating_add(right))
    }
}

#[derive(Debug)]
struct Input<const MAX_N: usize, K, A, V> {
    initial_items: Vec<(K, A, V)>,
    operations: Vec<Operation<K, A, V>>,
}

impl<'a, const MAX_N: usize, K, A, V> Arbitrary<'a> for Input<MAX_N, K, A, V>
where
    K: Arbitrary<'a> + PartialEq + Ord,
    A: Arbitrary<'a>,
    V: Arbitrary<'a>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let item_count = u.int_in_range(0..=MAX_N)?;
        let mut initial_items = Vec::<(K, A, V)>::with_capacity(item_count);
        for _ in 0..item_count {
            initial_items.push(u.arbitrary()?);
        }
        initial_items.sort_unstable_by(|(a, ..), (b, ..)| a.cmp(b));
        initial_items.dedup_by(|(a, ..), (b, ..)| (*a).eq(b));

        let operation_count = u.int_in_range(0..=MAX_N)?;
        let mut operations = Vec::<Operation<K, A, V>>::with_capacity(operation_count);
        for _ in 0..operation_count {
            operations.push(u.arbitrary()?);
        }
        operations.sort_unstable_by(|a, b| a.key().cmp(b.key()));
        operations.dedup_by(|a, b| a.key().eq(b.key()));

        Ok(Self {
            initial_items,
            operations,
        })
    }
}

#[derive(Debug, Arbitrary)]
enum Operation<K, A, V> {
    Remove { key: K },
    Insert { key: K, extra: A, value: V },
}

impl<K, A, V> Operation<K, A, V> {
    fn key(&self) -> &K {
        match self {
            Self::Remove { key } => key,
            Self::Insert { key, .. } => key,
        }
    }
}
