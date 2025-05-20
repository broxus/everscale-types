use std::hint::black_box;

use criterion::{criterion_group, criterion_main, Criterion};
use everscale_types::boc::Boc;

fn encode(c: &mut Criterion) {
    let block_bytes = include_bytes!("data/fat.block").to_vec();

    let cell = Boc::decode(block_bytes.clone()).unwrap();
    c.bench_function("encode", |b| {
        b.iter(|| {
            let data = Boc::encode(black_box(&cell));
            black_box(data);
        })
    });
}

criterion_group!(benches, encode);
criterion_main!(benches);