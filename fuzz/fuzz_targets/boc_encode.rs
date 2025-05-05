#![no_main]
use everscale_types::prelude::{Boc, Cell};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|cell: Cell| {
    _ = Boc::encode(cell);
});
