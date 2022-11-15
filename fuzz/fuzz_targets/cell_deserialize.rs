#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    _ = everscale_types::cell::arc_cell::deserialize(data);
});
