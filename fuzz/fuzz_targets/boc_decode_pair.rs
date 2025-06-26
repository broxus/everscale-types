#![no_main]
use tycho_types::prelude::Boc;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    _ = Boc::decode_pair(data);
});
