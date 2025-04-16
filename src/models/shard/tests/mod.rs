use super::*;
use crate::models::Block;
use crate::prelude::Boc;

fn check_master_state(cell: Cell) {
    let data = cell.parse::<ShardStateUnsplit>().unwrap();
    println!("data: {data:#?}");
    assert_eq!(CellBuilder::build_from(&data).unwrap(), cell);

    for (i, entry) in data.libraries.iter().enumerate() {
        let (hash, descr) = entry.unwrap();
        println!("lib#{i} hash={hash}");
        for entry in descr.publishers.keys() {
            let address = entry.unwrap();
            println!("lib#{i} publisher={address}")
        }
    }

    let custom = data.load_custom().unwrap().unwrap();
    println!("custom: {custom:#?}");
    assert_eq!(
        CellBuilder::build_from(&custom).unwrap(),
        data.custom.unwrap()
    );
}

#[test]
fn prod_zerostate() {
    const BOC: &[u8] = include_bytes!("everscale_zerostate.boc");
    check_master_state(Boc::decode(BOC).unwrap());
}

#[test]
fn new_zerostate() {
    const BOC: &[u8] = include_bytes!("new_zerostate.boc");
    let zerostate = Boc::decode(BOC).unwrap();
    check_master_state(zerostate.clone());

    let block = Boc::decode(include_bytes!("first_block.boc")).unwrap();
    let block = block.parse::<Block>().unwrap();
    let state_update = block.state_update.load().unwrap();

    let new_state = state_update.apply(&zerostate).unwrap();
    check_master_state(new_state);
}
