use super::*;
use crate::cell::EMPTY_CELL_HASH;
use crate::error::Error;
use crate::prelude::*;

#[test]
fn correct_proof_store_load() {
    let proof = MerkleProof::default();
    let cell = CellBuilder::build_from(&proof).unwrap();

    let parsed = cell.as_ref().parse::<MerkleProof>().unwrap();
    assert_eq!(parsed, proof);
}

#[test]
fn test_proof() {
    let root = Boc::decode(include_bytes!("simple_proof.boc")).unwrap();
    let target_hash = root.as_ref().reference(1).unwrap().repr_hash();

    let merkle_proof = MerkleProof::create_for_cell(root.as_ref(), target_hash)
        .build()
        .unwrap();

    let virtual_root = merkle_proof.cell.as_ref().virtualize();
    println!("{}", virtual_root.display_tree());

    assert_eq!(root.as_ref().repr_hash(), virtual_root.repr_hash());
    assert_eq!(root.as_ref().repr_depth(), virtual_root.repr_depth());
}

#[test]
#[cfg_attr(miri, ignore)] // takes too long to execute on miri
fn create_proof_for_deep_cell() {
    let mut cell = Cell::empty_cell();
    for i in 0..65000 {
        let mut builder = CellBuilder::new();
        builder.store_u32(i).unwrap();
        builder.store_reference(cell).unwrap();
        cell = builder.build().unwrap();
    }

    {
        let encoded = Boc::encode_base64(cell.as_ref());
        let decoded = Boc::decode_base64(encoded).unwrap();
        assert_eq!(decoded.as_ref(), cell.as_ref());
    }

    let cell = MerkleProof::create_for_cell(cell.as_ref(), EMPTY_CELL_HASH)
        .build()
        .unwrap();

    let encoded = BocRepr::encode_base64(&cell).unwrap();
    let decoded = Boc::decode_base64(encoded)
        .unwrap()
        .as_ref()
        .parse::<MerkleProof>()
        .unwrap();

    assert_eq!(cell, decoded);
}

#[test]
fn create_proof_for_dict() {
    // Create dict with keys 0..10
    let mut dict = Dict::<u32, u32>::new();

    for i in 0..10 {
        dict.add(i, i * 10).unwrap();
    }

    // Create a usage tree for accessing an element with keys 0 and 9
    let usage_tree = UsageTree::new(UsageTreeMode::OnDataAccess);
    let tracked_cell = usage_tree.track(&CellBuilder::build_from(dict).unwrap());
    let tracked_dict = tracked_cell.as_ref().parse::<Dict<u32, u32>>().unwrap();
    tracked_dict.get(0).unwrap().unwrap();
    tracked_dict.get(9).unwrap().unwrap();

    // Create proof from the usage tree
    let merkle_proof = MerkleProof::create(tracked_cell.as_ref(), usage_tree)
        .build()
        .unwrap();

    // Try to read some keys
    let dict = merkle_proof.cell.as_ref().virtualize();
    let dict = dict.parse::<Dict<u32, u32>>().unwrap();
    dict.get(0).unwrap().unwrap();
    dict.get(9).unwrap().unwrap();

    assert!(matches!(dict.get(5), Err(Error::PrunedBranchAccess)));
}

#[test]
fn proof_with_subtree() -> anyhow::Result<()> {
    let mut dict = Dict::<u32, u32>::new();
    for i in 0..10 {
        dict.add(i, i * 10)?;
    }
    let dict = CellBuilder::build_from(dict)?;

    let some_other_cell = {
        let mut builder = CellBuilder::new();
        builder.store_u128(123123)?;
        builder.store_reference(Cell::empty_cell())?;
        builder.store_reference(Cell::empty_cell())?;
        builder.build()?
    };

    let root_cell = {
        let mut builder = CellBuilder::new();
        builder.store_u128(321321)?;
        builder.store_reference(some_other_cell)?;
        builder.store_reference(dict.clone())?;
        builder.build()?
    };

    let mut usage_tree = UsageTree::new(UsageTreeMode::OnDataAccess).with_subtrees();
    let root_cell = usage_tree.track(&root_cell);

    {
        let mut root_cell = root_cell.as_ref().as_slice()?;
        root_cell.load_u32().unwrap();

        assert!(usage_tree.add_subtree(dict.as_ref()));
    }

    let proof = MerkleProof::create(root_cell.as_ref(), usage_tree).build()?;
    let mut virtual_cell = proof.cell.as_ref().virtualize().as_slice()?;

    assert_eq!(virtual_cell.load_u128(), Ok(321321));

    let first_ref = virtual_cell.load_reference()?;
    assert_eq!(first_ref.cell_type(), CellType::PrunedBranch);

    let second_ref = virtual_cell.load_reference()?;
    assert_eq!(second_ref.cell_type(), CellType::Ordinary);
    assert!(second_ref.descriptor().level_mask().is_empty());

    let dict = second_ref.parse::<Dict<u32, u32>>()?;
    for (i, entry) in dict.iter().enumerate() {
        let (key, value) = entry?;
        assert_eq!(i, key as usize);
        assert_eq!(key * 10, value);
    }
    assert_eq!(dict.values().count(), 10);

    Ok(())
}
