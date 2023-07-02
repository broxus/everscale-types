use super::*;
use crate::models::Block;
use crate::prelude::Boc;

fn check_state(data: Cell) {
    let data = data.parse::<ShardStateUnsplit>().unwrap();

    println!("data: {data:#?}");

    let shard_accounts = data.load_accounts().unwrap();
    for entry in shard_accounts.iter() {
        let (id, shard_state) = entry.unwrap();
        let account = shard_state.load_account().unwrap();
        println!("{id}: {account:#?}");
    }

    let _elector = shard_accounts.get([0x33; 32]).unwrap().unwrap();
    assert!(shard_accounts.contains_account([0x55; 32]).unwrap());

    let custom = data.load_custom().unwrap().unwrap();
    println!("custom: {custom:#?}");
}

#[test]
fn prod_zerostate() {
    const BOC: &[u8] = include_bytes!("everscale_zerostate.boc");
    check_state(Boc::decode(BOC).unwrap());
}

#[test]
fn new_zerostate() {
    const BOC: &[u8] = include_bytes!("new_zerostate.boc");
    let zerostate = Boc::decode(BOC).unwrap();
    check_state(zerostate.clone());

    let block = Boc::decode(include_bytes!("first_block.boc")).unwrap();
    let block = block.parse::<Block>().unwrap();
    let state_update = block.state_update.load().unwrap();

    let new_state = state_update.apply(&zerostate).unwrap();
    check_state(new_state);
}
