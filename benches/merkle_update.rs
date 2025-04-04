use everscale_types::cell::{Cell, CellBuilder, HashBytes, UsageTree, UsageTreeMode};
use everscale_types::dict::Dict;
use everscale_types::merkle::{MerkleUpdate, MerkleUpdateBuilder};
use iai_callgrind::{
    library_benchmark, library_benchmark_group, main, FlamegraphConfig, LibraryBenchmarkConfig,
};
use rand::prelude::{SliceRandom, StdRng};
use rand::{Rng, SeedableRng};

fn size_for_different_dicts() -> (Dict<HashBytes, Cell>, Vec<HashBytes>) {
    let value = (0..10000)
        .map(|x| (x, Dict::<u32, u32>::new()))
        .collect::<Vec<_>>();

    let value = Dict::try_from_sorted_slice(&value)
        .unwrap()
        .into_root()
        .unwrap();

    let size = 1_000_000;

    let mut rng = StdRng::seed_from_u64(1337);
    let mut keys: Vec<HashBytes> = (0..size)
        .map(|_| {
            let mut key = [0u8; 32];
            rng.fill(&mut key[..]);
            HashBytes::from(key)
        })
        .collect();
    keys.sort_unstable();

    let num_keys = 1000;

    let keys_to_check = keys
        .choose_multiple(&mut rng, num_keys)
        .copied()
        .collect::<Vec<_>>();

    let keys_inner = keys.iter().map(|k| (*k, value.clone())).collect::<Vec<_>>();
    let dict = Dict::try_from_sorted_slice(&keys_inner).unwrap();
    drop(keys);

    (dict, keys_to_check)
}

fn build_update(
    dict: &Dict<HashBytes, Cell>,
    keys_to_check: &[HashBytes],
) -> (Cell, Cell, UsageTree) {
    let old_cell = CellBuilder::build_from(dict).unwrap();
    let usage_tree = UsageTree::new(UsageTreeMode::OnLoad);
    let old_dict_cell_tracked = usage_tree.track(&old_cell);

    let mut dict = old_dict_cell_tracked
        .parse::<Dict<HashBytes, Cell>>()
        .unwrap();

    for (idx, key) in keys_to_check.iter().enumerate() {
        let mut cell = CellBuilder::new();
        cell.store_u32(idx as _).unwrap();
        let cell = cell.build().unwrap();
        dict.set(key, cell.clone()).unwrap();
    }

    let new_dict_cell = CellBuilder::build_from(dict).unwrap();

    (old_cell, new_dict_cell, usage_tree)
}

fn prepare() -> (Cell, Cell, UsageTree) {
    let (dict, keys_to_check) = size_for_different_dicts();
    build_update(&dict, &keys_to_check)
}

#[library_benchmark]
#[bench::base(setup=prepare)]
fn merkle_update((prev, new, usage_tree): (Cell, Cell, UsageTree)) {
    let mut merkle = MerkleUpdateBuilder::new(prev.as_ref(), new.as_ref(), usage_tree);
    let update = merkle.build().unwrap();

    std::mem::forget(update);
    std::mem::forget(prev);
    std::mem::forget(new);
}

library_benchmark_group!(

    name = merkle;
    benchmarks = merkle_update
);
main!(config =LibraryBenchmarkConfig::default()
                .flamegraph(FlamegraphConfig::default());
    library_benchmark_groups = merkle);
