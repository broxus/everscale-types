use crate::cell::*;

pub fn make_pruned_branch<C: CellFamily>(
    cell: &dyn Cell<C>,
    merkle_depth: u8,
    finalizer: &mut dyn Finalizer<C>,
) -> Option<CellContainer<C>> {
    let descriptor = cell.descriptor();

    let mut builder = CellBuilder::new();
    let level_mask = LevelMask::new(descriptor.level_mask().to_byte() | (1 << merkle_depth));
    let hash_count = descriptor.hash_count();

    builder.set_level_mask(level_mask);
    builder.store_u8(CellType::PrunedBranch.to_byte());
    builder.store_u8(level_mask.to_byte());
    for i in 0..hash_count {
        builder.store_u256(cell.hash(i));
    }

    for i in 0..hash_count {
        builder.store_u16(cell.depth(i));
    }

    builder.build_ext(finalizer)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{RcCellBuilder, RcCellFamily};

    #[test]
    fn correct_pruned_branch() {
        let cell = {
            let mut builder = RcCellBuilder::new();
            assert!(builder.store_u128(0xdeafbeaf123123));
            assert!(builder.store_reference(RcCellFamily::empty_cell()));
            builder.build().unwrap()
        };

        let pruned_branch =
            make_pruned_branch(cell.as_ref(), 0, &mut RcCellFamily::default_finalizer()).unwrap();
        assert_eq!(cell.repr_hash(), pruned_branch.hash(0));
        assert_eq!(cell.depth(0), pruned_branch.depth(0));
    }
}
