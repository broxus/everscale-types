#![no_main]
use everscale_types::prelude::Boc;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(cell) = Boc::decode(data) {
        _ = Boc::encode(cell.as_ref());
    }
});
