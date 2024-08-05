#![no_main]
use libfuzzer_sys::{fuzz_target, Corpus};

use everscale_types::prelude::{Cell, RawDict};

fuzz_target!(|data: Cell| -> Corpus {
    if let Ok(map) = data.parse::<RawDict<32>>() {
        _ = map.iter().count();
        return Corpus::Keep;
    }
    Corpus::Reject
});
