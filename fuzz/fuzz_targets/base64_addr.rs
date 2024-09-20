#![no_main]
use libfuzzer_sys::fuzz_target;

use everscale_types::models::{StdAddr, StdAddrFormat};
use libfuzzer_sys::Corpus;

fuzz_target!(|data: &[u8]| -> Corpus {
    if let Ok(s) = std::str::from_utf8(data) {
        if StdAddr::from_str_ext(s, StdAddrFormat::any()).is_ok() {
            return Corpus::Keep;
        }
    }
    Corpus::Reject
});
