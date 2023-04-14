#![no_main]
use libfuzzer_sys::{fuzz_target, Corpus};

use everscale_types::prelude::{Boc, Load, RawDict, RcCellFamily};

fuzz_target!(|data: &[u8]| -> Corpus {
    if let Ok(cell) = Boc::<RcCellFamily>::decode(data) {
        if let Ok(map) = RawDict::<RcCellFamily, 32>::load_from(&mut cell.as_slice()) {
            _ = map.iter().count();
            return Corpus::Keep;
        }
    }
    Corpus::Reject
});
