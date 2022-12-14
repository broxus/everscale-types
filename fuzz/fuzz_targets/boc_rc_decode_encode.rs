#![no_main]
use libfuzzer_sys::fuzz_target;

use everscale_types::{Boc, RcCellFamily};

fuzz_target!(|data: &[u8]| {
    if let Ok(cell) = Boc::<RcCellFamily>::decode(data) {
        _ = Boc::<RcCellFamily>::encode(cell.as_ref());
    }
});
