#![no_main]
use tycho_types::prelude::{Boc, RawDict};
use libfuzzer_sys::{fuzz_target, Corpus};

fuzz_target!(|data: &[u8]| -> Corpus {
    if let Ok(cell) = Boc::decode(data) {
        if let Ok(map) = cell.parse::<RawDict<32>>() {
            _ = map.iter().count();
            return Corpus::Keep;
        }
    }
    Corpus::Reject
});
