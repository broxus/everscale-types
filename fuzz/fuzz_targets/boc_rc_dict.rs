#![no_main]
use libfuzzer_sys::{fuzz_target, Corpus};

use everscale_types::cell::Load;
use everscale_types::dict::HashmapE;
use everscale_types::{Boc, RcCellFamily};

fuzz_target!(|data: &[u8]| -> Corpus {
    if let Ok(cell) = Boc::<RcCellFamily>::decode(data) {
        if let Some(map) = HashmapE::<RcCellFamily, 32>::load_from(&mut cell.as_slice()) {
            _ = map.iter().count();
            return Corpus::Keep;
        }
    }
    Corpus::Reject
});
