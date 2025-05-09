#![no_main]
use arbitrary::Arbitrary;
use everscale_types::dict::AugDictExtra;
use everscale_types::error::Error;
use everscale_types::prelude::*;
use libfuzzer_sys::fuzz_target;

use self::common::AugInput;

mod common;

fuzz_target!(|input: AugInput<1000, u32, SimpleAug, u64>| input.compare_manual_vs_batched());

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
