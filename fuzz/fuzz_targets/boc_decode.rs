#![no_main]
use tycho_types::prelude::Boc;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(cell) = Boc::decode(data) {
        if let Ok(mut slice) = cell.as_slice() {
            _ = slice.get_u8(0);
            _ = slice.get_u16(0);
            _ = slice.get_u32(0);
            _ = slice.get_u64(0);
            _ = slice.get_u128(0);
            _ = slice.get_u256(0);
            if slice.skip_first(3, 0).is_ok() {
                _ = slice.get_u8(0);
                _ = slice.get_u16(0);
                _ = slice.get_u32(0);
                _ = slice.get_u64(0);
                _ = slice.get_u128(0);
                _ = slice.get_u256(0);
            }
        }
    }
});
