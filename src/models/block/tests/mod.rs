use std::collections::HashMap;

use super::*;

#[cfg(not(feature = "tycho"))]
use crate::prelude::*;
#[cfg(feature = "tycho")]
use crate::{
    models::{ExtraCurrencyCollection, GlobalCapabilities},
    prelude::*,
};

fn serialize_any<T: Store>(data: T) -> Cell {
    CellBuilder::build_from(data).unwrap()
}

fn check_block(boc: &[u8], expected_shards: Option<Vec<ShardIdent>>) -> Cell {
    let boc = Boc::decode(boc).unwrap();
    let block = boc.parse::<Block>().unwrap();
    println!("block: {block:#?}");

    let info = block.load_info().unwrap();

    #[cfg(feature = "serde")]
    {
        let json = serde_json::to_string_pretty(&info).unwrap();
        let parsed: BlockInfo = serde_json::from_str(&json).unwrap();
        let parsed_boc = CellBuilder::build_from(&parsed).unwrap();
        assert_eq!(block.info.cell.repr_hash(), parsed_boc.repr_hash());
    }

    println!("info: {info:#?}");
    let prev_ref = info.load_prev_ref().unwrap();
    println!("prev_ref: {prev_ref:#?}");
    assert_eq!(serialize_any(info).as_ref(), block.info.cell.as_ref());

    let value_flow = block.load_value_flow().unwrap();
    println!("value_flow: {value_flow:#?}");
    assert_eq!(
        serialize_any(value_flow).as_ref(),
        block.value_flow.cell.as_ref()
    );

    let state_update = block.load_state_update().unwrap();
    println!("state_update: {state_update:#?}");
    assert_eq!(
        serialize_any(state_update).as_ref(),
        block.state_update.cell.as_ref()
    );

    let extra = block.load_extra().unwrap();
    println!("extra: {extra:#?}");
    let account_blocks = extra.account_blocks.load().unwrap();
    println!("account_blocks: {account_blocks:#?}");

    for entry in account_blocks.iter() {
        let (account, _, account_block) = entry.unwrap();
        assert_eq!(account, account_block.account);

        for entry in account_block.transactions.iter() {
            let (_lt, _, cell) = entry.unwrap();
            let tx = cell.load().unwrap();
            assert_eq!(account, tx.account);
        }
    }
    assert_eq!(
        serialize_any(account_blocks).as_ref(),
        extra.account_blocks.cell.as_ref()
    );

    let custom = extra.load_custom().unwrap();
    assert_eq!(expected_shards.is_some(), custom.is_some());
    if let Some(custom) = &custom {
        println!("custom: {custom:#?}");

        let expected_shards = expected_shards.unwrap();

        let shards = custom.shards.get_workchain_shards(0).unwrap().unwrap();
        let mut shard_ids = Vec::new();
        for entry in shards.raw_iter() {
            let (shard, _value) = entry.unwrap();
            println!("shard: {shard:?}");
            shard_ids.push(shard);
        }
        assert_eq!(expected_shards, shard_ids);

        for entry in custom.shards.iter() {
            let (shard, value) = entry.unwrap();
            println!("shard {shard:?}: {value:#?}");
        }
        println!(
            "origin encoded {}",
            BocRepr::encode_base64(&custom.shards).unwrap()
        );
        let shards = custom
            .shards
            .iter()
            .map(|x| x.unwrap())
            .collect::<HashMap<_, _>>();
        let encoded = ShardHashes::from_shards(&shards).unwrap();
        println!("encoded {}", BocRepr::encode_base64(&encoded).unwrap());

        let parsed = encoded.iter().collect::<Result<Vec<_>, _>>().unwrap();
        for (a, b) in shard_ids.iter().zip(parsed.iter()) {
            assert_eq!(*a, b.0);
        }

        for item in custom.shards.latest_blocks() {
            let block_id = item.unwrap();
            println!("block_id: {block_id}");
        }

        assert_eq!(
            serialize_any(custom).as_ref(),
            extra.custom.as_ref().unwrap().cell.as_ref()
        )
    }

    assert_eq!(serialize_any(extra).as_ref(), block.extra.cell.as_ref());

    let serialized = serialize_any(block);
    assert_eq!(serialized.as_ref(), boc.as_ref());

    boc
}

#[test]
fn masterchain_block() {
    check_block(
        include_bytes!("mc_simple_block.boc"),
        Some(vec![ShardIdent::new(0, ShardIdent::PREFIX_FULL).unwrap()]),
    );
}

#[test]
fn masterchain_key_block() {
    check_block(
        include_bytes!("mc_key_block.boc"),
        Some(vec![ShardIdent::new(0, ShardIdent::PREFIX_FULL).unwrap()]),
    );
}

#[test]
fn masterchain_block_with_shards() {
    check_block(
        include_bytes!("mc_block_with_shards.boc"),
        Some(vec![
            ShardIdent::new(0, 0x4000000000000000).unwrap(),
            ShardIdent::new(0, 0xa000000000000000).unwrap(),
            ShardIdent::new(0, 0xe000000000000000).unwrap(),
        ]),
    );
}

#[test]
fn shard_block_empty() {
    check_block(include_bytes!("empty_shard_block.boc"), None);
}

#[test]
fn shard_block_with_messages() {
    check_block(include_bytes!("simple_shard_block.boc"), None);
}

#[test]
fn parse_block_id() {
    let block_id = BlockId {
        shard: ShardIdent::MASTERCHAIN,
        seqno: 123321,
        root_hash: HashBytes([123; 32]),
        file_hash: HashBytes([234; 32]),
    };

    let s = block_id.to_string();
    println!("S: {s}");
    assert_eq!(s.parse::<BlockId>().unwrap(), block_id);
}

#[test]
fn shard_ident_operations() {
    let shard = ShardIdent::BASECHAIN;
    assert!(shard.is_left_child());
    assert_eq!(shard.prefix_len(), 0);
    assert!(shard.merge().is_none());
    assert_eq!(shard.opposite(), None);

    let (left, right) = shard.split().unwrap();
    assert!(left.is_left_child() && !left.is_right_child());
    assert!(right.is_right_child() && !right.is_left_child());

    assert_eq!(left.opposite(), Some(right));
    assert_eq!(right.opposite(), Some(left));

    assert!(!left.is_child_of(&ShardIdent::MASTERCHAIN));
    assert!(!right.is_child_of(&ShardIdent::MASTERCHAIN));

    assert!(left.is_child_of(&shard));
    assert!(!shard.is_child_of(&left));
    assert!(right.is_child_of(&shard));
    assert!(!shard.is_child_of(&right));

    assert!(!left.is_parent_of(&right));
    assert!(!right.is_parent_of(&left));
    assert!(!left.is_ancestor_of(&right));
    assert!(!right.is_ancestor_of(&left));

    assert!(shard.is_parent_of(&left));
    assert!(!left.is_parent_of(&shard));
    assert!(shard.is_parent_of(&right));
    assert!(!right.is_parent_of(&shard));

    assert!(shard.is_ancestor_of(&left));
    assert!(!left.is_ancestor_of(&shard));
    assert!(shard.is_ancestor_of(&right));
    assert!(!right.is_ancestor_of(&shard));

    assert_eq!(left.merge().unwrap(), shard);
    assert_eq!(right.merge().unwrap(), shard);

    let children = {
        let (ll, lr) = left.split().unwrap();
        let (rl, rr) = right.split().unwrap();

        assert_eq!(ll.opposite(), Some(lr));
        assert_eq!(lr.opposite(), Some(ll));
        assert_eq!(rl.opposite(), Some(rr));
        assert_eq!(rr.opposite(), Some(rl));

        assert!(ll.intersects(&left));
        assert!(left.intersects(&ll));
        assert!(lr.intersects(&left));
        assert!(left.intersects(&lr));

        assert!(rl.intersects(&right));
        assert!(right.intersects(&rl));
        assert!(rr.intersects(&right));
        assert!(right.intersects(&rr));

        assert!(!rl.intersects(&left));
        assert!(!left.intersects(&rl));
        assert!(!rr.intersects(&left));
        assert!(!left.intersects(&rr));

        assert!(!ll.intersects(&right));
        assert!(!right.intersects(&ll));
        assert!(!lr.intersects(&right));
        assert!(!right.intersects(&lr));

        [ll, lr, rl, rr]
    };

    for child in children {
        assert_eq!(child.prefix_len(), 2);
        assert!(child.is_left_child() != child.is_right_child());
        assert!(shard.is_ancestor_of(&child));

        assert!(!child.is_ancestor_of(&shard));
        assert!(!child.is_parent_of(&shard));
        assert!(!shard.is_parent_of(&child));

        assert!(shard.intersects(&child));
        assert!(child.intersects(&shard));

        assert!(!child.intersects(&ShardIdent::MASTERCHAIN));
    }
}

#[test]
fn shard_ident_max_split() {
    let mut shards = vec![];

    let mut shard = ShardIdent::BASECHAIN;
    shards.push(shard);

    for i in 0..ShardIdent::MAX_SPLIT_DEPTH {
        assert_eq!(shard.prefix_len(), i as u16);

        let (left, _) = shard.split().unwrap();
        shard = left;
        shards.push(shard);
    }
    assert!(shard.split().is_none());

    let mut rev_shard = ShardIdent::new(0, 1 << (63 - ShardIdent::MAX_SPLIT_DEPTH)).unwrap();
    while let Some(shard) = shards.pop() {
        assert_eq!(rev_shard, shard);

        if !shards.is_empty() {
            rev_shard = shard.merge().unwrap();
        }
    }
    assert!(rev_shard.merge().is_none());
}

#[test]
fn shard_ident_store_load() {
    fn check_store_load(shard: ShardIdent) {
        let mut builder = CellBuilder::new();
        shard
            .store_into(&mut builder, &mut Cell::empty_context())
            .unwrap();
        let cell = builder.build().unwrap();
        assert_eq!(cell.bit_len(), ShardIdent::BITS);

        let parsed_shard = cell.parse::<ShardIdent>().unwrap();
        assert_eq!(shard, parsed_shard);
    }

    let mut shard = ShardIdent::BASECHAIN;
    for _ in 0..ShardIdent::MAX_SPLIT_DEPTH {
        let (left, right) = shard.split().unwrap();
        check_store_load(left);
        check_store_load(right);
        shard = left;
    }
    assert!(shard.split().is_none());

    // Try loading from invalid cells
    fn check_invalid<F: FnOnce(&mut CellBuilder) -> Result<(), Error>>(f: F) {
        let mut builder = CellBuilder::new();
        f(&mut builder).unwrap();
        let cell = builder.build().unwrap();
        assert!(cell.parse::<ShardIdent>().is_err())
    }

    check_invalid(|b| b.store_bit_one());
    check_invalid(|b| b.store_u8(0));
    check_invalid(|b| {
        b.store_u8(ShardIdent::MAX_SPLIT_DEPTH + 1)?;
        b.store_u32(0)?;
        b.store_u64(0)
    });
}

#[test]
fn proof_for_masterchain_block() {
    let boc = Boc::decode(include_bytes!("mc_block_proof.boc")).unwrap();
    let proof = boc.parse::<BlockProof>().unwrap();

    assert_eq!(proof.proof_for.shard, ShardIdent::MASTERCHAIN);
    assert_eq!(proof.proof_for.seqno, 13121100);
    assert!(proof.signatures.is_some());

    assert_eq!(serialize_any(proof).as_ref(), boc.as_ref());
}

#[test]
fn proof_for_shardchain_block() {
    let boc = Boc::decode(include_bytes!("shard_block_proof.boc")).unwrap();
    let proof = boc.parse::<BlockProof>().unwrap();

    assert_eq!(
        proof.proof_for.shard,
        ShardIdent::new(0, 0xf800000000000000).unwrap()
    );
    assert_eq!(proof.proof_for.seqno, 19363091);
    assert!(proof.signatures.is_none());

    assert_eq!(serialize_any(proof).as_ref(), boc.as_ref());
}

#[test]
#[cfg(feature = "tycho")]
fn block_with_tycho_updates_store_load() {
    let block = Block {
        global_id: 42,
        info: Lazy::new(&BlockInfo {
            version: 0,
            gen_utime_ms: 123,
            after_merge: false,
            before_split: false,
            after_split: false,
            want_split: false,
            want_merge: true,
            key_block: false,
            flags: 1,
            seqno: 24721433,
            vert_seqno: 0,
            shard: ShardIdent::new(-1, 0x8000000000000000).unwrap(),
            gen_utime: 1674507085,
            start_lt: 34671157000000,
            end_lt: 34671157000005,
            gen_validator_list_hash_short: 3236125243,
            gen_catchain_seqno: 343054,
            min_ref_mc_seqno: 24721430,
            prev_key_block_seqno: 24715347,
            gen_software: GlobalVersion {
                version: 34,
                capabilities: GlobalCapabilities::new(464814),
            },
            master_ref: None,
            prev_ref: Cell::empty_cell(),
            prev_vert_ref: None,
        })
        .unwrap(),
        value_flow: Lazy::new(&ValueFlow {
            from_prev_block: CurrencyCollection {
                tokens: Tokens::new(3610625966274374005),
                other: ExtraCurrencyCollection::new(),
            },
            to_next_block: CurrencyCollection {
                tokens: Tokens::new(3610625969470214036),
                other: ExtraCurrencyCollection::new(),
            },
            imported: CurrencyCollection {
                tokens: Tokens::new(0),
                other: ExtraCurrencyCollection::new(),
            },
            exported: CurrencyCollection {
                tokens: Tokens::new(0),
                other: ExtraCurrencyCollection::new(),
            },
            fees_collected: CurrencyCollection {
                tokens: Tokens::new(3195840031),
                other: ExtraCurrencyCollection::new(),
            },
            fees_imported: CurrencyCollection {
                tokens: Tokens::new(1495840031),
                other: ExtraCurrencyCollection::new(),
            },
            recovered: CurrencyCollection {
                tokens: Tokens::new(3195840031),
                other: ExtraCurrencyCollection::new(),
            },
            created: CurrencyCollection {
                tokens: Tokens::new(1700000000),
                other: ExtraCurrencyCollection::new(),
            },
            minted: CurrencyCollection {
                tokens: Tokens::new(0),
                other: ExtraCurrencyCollection::new(),
            },
            copyleft_rewards: Dict::new(),
        })
        .unwrap(),
        state_update: Lazy::new(&MerkleUpdate {
            old_hash: HashBytes::ZERO,
            new_hash: HashBytes::ZERO,
            old_depth: 182,
            new_depth: 182,
            old: Cell::empty_cell(),
            new: Cell::empty_cell(),
        })
        .unwrap(),
        extra: Lazy::new(&BlockExtra {
            in_msg_description: Lazy::new(&AugDict::new()).unwrap(),
            out_msg_description: Lazy::new(&AugDict::new()).unwrap(),
            account_blocks: Lazy::new(&AugDict::new()).unwrap(),
            rand_seed: HashBytes::ZERO,
            created_by: HashBytes::ZERO,
            custom: None,
        })
        .unwrap(),
        out_msg_queue_updates: MsgQueueUpdates {
            diff_hash: HashBytes::ZERO,
        },
    };
    let encoded = BocRepr::encode(&block).unwrap();

    let cell: Cell = Boc::decode(&*encoded).unwrap();
    assert_eq!(
        Block::load_from(&mut cell.as_slice().unwrap())
            .unwrap()
            .out_msg_queue_updates,
        MsgQueueUpdates {
            diff_hash: HashBytes::ZERO,
        }
    );
}
