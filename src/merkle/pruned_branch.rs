use crate::cell::*;
use crate::error::Error;

/// Creates a pruned branch cell with the specified merkle depth.
pub fn make_pruned_branch(
    cell: &dyn CellImpl,
    merkle_depth: u8,
    finalizer: &mut dyn Finalizer,
) -> Result<Cell, Error> {
    let descriptor = cell.descriptor();

    let mut builder = CellBuilder::new();
    let level_mask = LevelMask::new(descriptor.level_mask().to_byte() | (1 << merkle_depth));
    let hash_count = descriptor.hash_count();

    builder.set_level_mask(level_mask);
    builder.set_exotic(true);

    _ = builder.store_u16(u16::from_be_bytes([
        CellType::PrunedBranch.to_byte(),
        level_mask.to_byte(),
    ]));

    for i in 0..hash_count {
        _ = builder.store_u256(cell.hash(i));
    }

    for i in 0..hash_count {
        _ = builder.store_u16(cell.depth(i));
    }

    builder.build_ext(finalizer)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::prelude::{RcCellBuilder, RcCellFamily};

    #[test]
    fn correct_pruned_branch() {
        let cell = {
            let mut builder = RcCellBuilder::new();
            builder.store_u128(0xdeafbeaf123123).unwrap();
            builder.store_reference(RcCellFamily::empty_cell()).unwrap();
            builder.build().unwrap()
        };

        let pruned_branch =
            make_pruned_branch(cell.as_ref(), 0, &mut RcCellFamily::default_finalizer()).unwrap();
        assert_eq!(cell.repr_hash(), pruned_branch.hash(0));
        assert_eq!(cell.depth(0), pruned_branch.depth(0));

        let virtual_cell = cell.virtualize();
        assert_eq!(cell.repr_hash(), virtual_cell.repr_hash());
        assert_eq!(cell.depth(3), virtual_cell.depth(3));

        let virtual_pruned_branch =
            make_pruned_branch(virtual_cell, 0, &mut RcCellFamily::default_finalizer()).unwrap();
        assert_eq!(pruned_branch.as_ref(), virtual_pruned_branch.as_ref());
    }
}
