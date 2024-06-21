#![no_main]
use libfuzzer_sys::{fuzz_target, Corpus};

use everscale_types::models::Message;
use everscale_types::prelude::Cell;

fuzz_target!(|cell: Cell| -> Corpus {
    if cell.parse::<Message>().is_ok() {
        return Corpus::Keep;
    }

    Corpus::Reject
});
