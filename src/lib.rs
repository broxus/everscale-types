macro_rules! ok {
    ($e:expr $(,)?) => {
        match $e {
            core::result::Result::Ok(val) => val,
            core::result::Result::Err(err) => return core::result::Result::Err(err),
        }
    };
}

pub use self::boc::Boc;
pub use self::cell::rc::{RcCell, RcCellFamily};
pub use self::cell::sync::{ArcCell, ArcCellFamily};
pub use self::cell::{Cell, CellBuilder, CellDescriptor, CellHash, CellSlice, CellType, LevelMask};

/// BOC (Bag Of Cells) helper for the `Arc` family of cells.
pub type ArcBoc = Boc<ArcCellFamily>;
/// BOC (Bag Of Cells) helper for the `Rc` family of cells.
pub type RcBoc = Boc<RcCellFamily>;

/// Cell builder for the `Arc` family of cells.
pub type ArcCellBuilder = CellBuilder<ArcCellFamily>;
/// Cell builder for the `Rc` family of cells.
pub type RcCellBuilder = CellBuilder<RcCellFamily>;

/// A read-only view for the `Arc` family of cells.
pub type ArcCellSlice<'a> = CellSlice<'a, ArcCellFamily>;
/// A read-only view for the `Rc` family of cells.
pub type RcCellSlice<'a> = CellSlice<'a, RcCellFamily>;

pub mod boc;
pub mod cell;
pub mod util;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn correct_deserialization() {
        let data = base64::decode("te6ccgEBBAEAzwACg4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEAIBAEAAAAAAAAAAAAAAAAAAAAAAAAAAm2c6ClpzoTVSAHvzVQGDAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHKq1w7OAAkYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACRwAwBAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEljGP8=").unwrap();

        let arc_cell = ArcBoc::decode(&data).unwrap();
        let rc_cell = RcBoc::decode(&data).unwrap();
        assert_eq!(arc_cell.as_ref(), rc_cell.as_ref());
        assert_eq!(
            arc_cell.repr_hash(),
            &[
                0x63, 0xd4, 0x75, 0x13, 0x9a, 0xc1, 0x4f, 0x3e, 0xfe, 0x69, 0x0e, 0xd7, 0xfd, 0x4f,
                0xf0, 0x02, 0x1c, 0xf2, 0x6b, 0xc4, 0xab, 0xd0, 0xaf, 0x01, 0x40, 0xa3, 0xb4, 0xc8,
                0x95, 0xf0, 0x73, 0x76
            ]
        );

        let serialized = RcBoc::encode(rc_cell.as_ref());
        assert_eq!(serialized, data);
    }

    #[test]
    fn cell_slices() {
        let data = base64::decode(
            "te6ccgEBAQEALQAAVb23gAA3/WsCOdnvw2dedGrVhjTaZxn/TYcWb7TR8Im/MkK13n6c883gt8A=",
        )
        .unwrap();
        let cell = RcBoc::decode(data).unwrap();

        let mut slice = cell.as_slice();
        assert!(!slice.is_data_empty());
        assert_eq!(slice.remaining_bits(), 337);
        assert!(slice.is_refs_empty());
        assert_eq!(slice.remaining_refs(), 0);
        assert!(slice.reference(0).is_none());
        assert!(slice.reference_cloned(0).is_none());
        assert!(slice.get_next_reference().is_none());
        assert!(slice.get_next_reference_cloned().is_none());

        assert_eq!(slice.get_bit(0), Some(true));
        assert_eq!(slice.get_next_bit(), Some(true));
        assert_eq!(slice.get_bits(0, 8), Some(123));
        assert_eq!(slice.get_bits(8, 8), Some(111));
        assert_eq!(slice.get_next_u16(), Some(0x7b6f));
        assert_eq!(slice.get_u32(0), Some(0x00006ffa));
        assert_eq!(slice.get_u32(32), Some(0xd60473b3));
        assert_eq!(slice.get_next_u64(), Some(0x6ffad60473b3));
        assert_eq!(
            slice.get_next_u256(),
            Some([
                0xdf, 0x86, 0xce, 0xbc, 0xe8, 0xd5, 0xab, 0x0c, 0x69, 0xb4, 0xce, 0x33, 0xfe, 0x9b,
                0x0e, 0x2c, 0xdf, 0x69, 0xa3, 0xe1, 0x13, 0x7e, 0x64, 0x85, 0x6b, 0xbc, 0xfd, 0x39,
                0xe7, 0x9b, 0xc1, 0x6f,
            ])
        );
        assert_eq!(slice.get_bits(0, 1), None);
    }

    #[test]
    fn test_builder() {
        let data = base64::decode("te6ccgEBAQEAAwAAAbE=").unwrap();
        let parsed_cell = Boc::<RcCellFamily>::decode(data).unwrap();

        let mut builder = CellBuilder::<RcCellFamily>::new();
        assert!(builder.store_bit_true());
        assert!(builder.store_bit_zero());
        assert!(builder.store_bit_true());
        assert!(builder.store_bit_true());
        assert!(builder.store_bit_zero());
        assert!(builder.store_bit_zero());
        assert!(builder.store_bit_zero());
        let built_cell = builder.build().unwrap();

        assert_eq!(parsed_cell.repr_hash(), built_cell.repr_hash());

        let data = base64::decode("te6ccgEBAQEAggAA////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////").unwrap();
        let parsed_cell = RcBoc::decode(data).unwrap();

        let mut builder = RcCellBuilder::new();
        for _ in 0..cell::MAX_BIT_LEN {
            assert!(builder.store_bit_true());
        }
        assert!(!builder.store_bit_true());
        let built_cell = builder.build().unwrap();

        assert_eq!(parsed_cell.repr_hash(), built_cell.repr_hash());

        let mut builder = RcCellBuilder::new();
        assert!(builder.store_bit_true());
        assert!(builder.store_u128(0xaaffaaffaaffaaffaaffaaffaaffaaff));
        let cell = builder.build().unwrap();

        let mut builder = RcCellBuilder::new();
        assert!(builder.store_bit_true());
        assert!(builder.store_u64(0xaaffaaffaaffaaff));
        assert!(builder.store_u64(0xaaffaaffaaffaaff));
        assert_eq!(cell.as_ref(), builder.build().unwrap().as_ref());

        let mut builder = RcCellBuilder::new();
        assert!(builder.store_zeros(1020));
        assert!(builder.store_small_uint(0x5, 3));
        builder.build().unwrap();

        let mut builder = RcCellBuilder::new();
        assert!(builder.store_small_uint(5, 3));
        assert!(builder.store_u256(&[
            0xdf, 0x86, 0xce, 0xbc, 0xe8, 0xd5, 0xab, 0x0c, 0x69, 0xb4, 0xce, 0x33, 0xfe, 0x9b,
            0x0e, 0x2c, 0xdf, 0x69, 0xa3, 0xe1, 0x13, 0x7e, 0x64, 0x85, 0x6b, 0xbc, 0xfd, 0x39,
            0xe7, 0x9b, 0xc1, 0x6f,
        ]));
        let cell = builder.build().unwrap();

        let target_cell = RcBoc::decode(
            base64::decode("te6ccgEBAQEAIwAAQbvw2dedGrVhjTaZxn/TYcWb7TR8Im/MkK13n6c883gt8A==")
                .unwrap(),
        )
        .unwrap();
        assert_eq!(cell.as_ref(), target_cell.as_ref());

        let mut builder = RcCellBuilder::new();
        assert!(builder.store_zeros(3));
        assert!(builder.store_raw(&[0xdd, 0x55], 10));
        assert!(builder.store_reference(target_cell));
        assert!(builder.store_reference(cell));
        let cell = builder.build().unwrap();

        let mut builder = RcCellBuilder::new();
        assert!(builder.store_slice(&cell.as_slice()));
        let cell = builder.build().unwrap();
        println!("{}", cell.display_tree());
    }
}
