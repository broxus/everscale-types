#![no_main]
use everscale_types::models::Message;
use everscale_types::prelude::Boc;
use libfuzzer_sys::{fuzz_target, Corpus};

fuzz_target!(|data: &[u8]| -> Corpus {
    if let Ok(cell) = Boc::decode(data) {
        if cell.parse::<Message>().is_ok() {
            return Corpus::Keep;
        }
    }
    Corpus::Reject
});
