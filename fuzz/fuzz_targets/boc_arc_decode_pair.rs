#![no_main]
use libfuzzer_sys::fuzz_target;

use everscale_types::{ArcCellFamily, Boc};

fuzz_target!(|data: &[u8]| {
    _ = Boc::<ArcCellFamily>::decode_pair(data);
});
