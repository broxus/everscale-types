#![no_main]
use libfuzzer_sys::fuzz_target;

use everscale_types::prelude::Boc;

fuzz_target!(|data: &[u8]| {
    _ = Boc::decode_pair(data);
});
