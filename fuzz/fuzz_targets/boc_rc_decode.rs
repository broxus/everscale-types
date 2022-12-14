#![no_main]
use libfuzzer_sys::fuzz_target;

use everscale_types::{Boc, RcCellFamily};

fuzz_target!(|data: &[u8]| {
    if let Ok(cell) = Boc::<RcCellFamily>::decode(data) {
        let mut slice = cell.as_slice();
        _ = slice.get_u8(0);
        _ = slice.get_u16(0);
        _ = slice.get_u32(0);
        _ = slice.get_u64(0);
        _ = slice.get_u128(0);
        _ = slice.get_u256(0);
        if slice.try_advance(3, 0) {
            _ = slice.get_u8(0);
            _ = slice.get_u16(0);
            _ = slice.get_u32(0);
            _ = slice.get_u64(0);
            _ = slice.get_u128(0);
            _ = slice.get_u256(0);
        }
    }
});
