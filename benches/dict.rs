use everscale_types::{cell::*, dict::*};
use iai_callgrind::{library_benchmark, library_benchmark_group, main};
use rand::distributions::{Distribution, Standard};
use rand::{Rng, SeedableRng};
use std::hint::black_box;

fn build_dict<K, V>(num_elements: usize) -> Dict<K, V>
where
    Standard: Distribution<K> + Distribution<V>,
    K: Store + DictKey,
    V: Store,
{
    let mut rng = rand_xorshift::XorShiftRng::from_seed([0u8; 16]);

    let mut result = Dict::<K, V>::new();
    for _ in 0..num_elements {
        let key = rng.gen::<K>();
        let value = rng.gen::<V>();
        result.set(key, value).unwrap();
    }
    result
}

#[library_benchmark]
#[bench::small(10)]
#[bench::medium(100)]
#[bench::large(1000)]
#[bench::xlarge(10000)]
fn bench_build_dict_u64_u64(num_elements: usize) -> Dict<u64, u64> {
    black_box(build_dict(num_elements))
}

library_benchmark_group!(name = build_dict; benchmarks = bench_build_dict_u64_u64);

main!(library_benchmark_groups = build_dict);
