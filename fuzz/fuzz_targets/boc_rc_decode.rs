#![no_main]
use libfuzzer_sys::fuzz_target;

use everscale_types::{Boc, RcCellFamily};

fuzz_target!(|data: &[u8]| {
    _ = Boc::<RcCellFamily>::decode_pair(data);
});
