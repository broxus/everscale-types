#![no_main]
use libfuzzer_sys::fuzz_target;

use everscale_types::prelude::{Boc, Cell};

fuzz_target!(|cell: Cell| {
    let bytes = Boc::encode(&cell);
    let decoded = Boc::decode(&bytes).unwrap();

    assert_eq!(cell, decoded);
});
