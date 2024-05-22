#![no_main]
use libfuzzer_sys::{fuzz_target, Corpus};

use everscale_types::cell::CellTreeStats;
use everscale_types::prelude::*;

fuzz_target!(|data: &[u8]| -> Corpus {
    if let Ok(cell) = Boc::decode(data) {
        let res = Boc::encode(cell.as_ref());
        let redecoded = Boc::decode(&res).unwrap();
        assert_eq!(cell.as_ref(), redecoded.as_ref());
        let l = call_all_cell_methods(&cell);
        let r = call_all_cell_methods(&redecoded);
        assert_eq!(l, r);
        return Corpus::Keep;
    }
    Corpus::Reject
});

fn call_all_cell_methods(cell: &Cell) -> CellTreeStats {
    let hash = cell.hash(0);
    let hash = cell.hash(1);
    let hash = cell.hash(2);
    let hash = cell.hash(3);

    let _ = cell.virtualize();
    cell.compute_unique_stats(usize::MAX).unwrap()
}
