#![warn(missing_docs)]

//! Everscale types

/// Prevents using `From::from` for plain error conversion.
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
pub use self::cell::{
    Cell, CellBuilder, CellDescriptor, CellFamily, CellHash, CellSlice, CellType, LevelMask, Load,
    RcUsageTree, Store, UsageTreeMode,
};
pub use self::dict::Dict;
pub use self::error::Error;

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

/// An ordinary dictionary with fixed length keys for the `Arc` family of cells.
pub type ArcDict<const N: u16> = Dict<ArcCellFamily, N>;
/// An ordinary dictionary with fixed length keys for the `Rc` family of cells.
pub type RcDict<const N: u16> = Dict<RcCellFamily, N>;

impl Store<RcCellFamily> for RcCell {
    fn store_into(
        &self,
        builder: &mut RcCellBuilder,
        _: &mut dyn cell::Finalizer<RcCellFamily>,
    ) -> bool {
        builder.store_reference(self.clone())
    }
}

impl Store<ArcCellFamily> for ArcCell {
    fn store_into(
        &self,
        builder: &mut CellBuilder<ArcCellFamily>,
        _: &mut dyn cell::Finalizer<ArcCellFamily>,
    ) -> bool {
        builder.store_reference(self.clone())
    }
}

impl<'a> Load<'a, RcCellFamily> for RcCell {
    fn load_from(slice: &mut CellSlice<'a, RcCellFamily>) -> Option<Self> {
        slice.load_reference_cloned()
    }
}

impl<'a> Load<'a, ArcCellFamily> for ArcCell {
    fn load_from(slice: &mut CellSlice<'a, ArcCellFamily>) -> Option<Self> {
        slice.load_reference_cloned()
    }
}

pub mod boc;
pub mod cell;
pub mod dict;
pub mod merkle;
pub mod num;
pub mod util;

#[cfg(feature = "serde")]
mod serde;

mod error;

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
    fn big_cell_deserialization() {
        let data = base64::decode("te6ccgIDAAwAAQAAAACIAAAEBAABAAEAAQABAAEEBAACAAIAAgACAAIEBAADAAMAAwADAAMEBAAEAAQABAAEAAQEBAAFAAUABQAFAAUEBAAGAAYABgAGAAYEBAAHAAcABwAHAAcEBAAIAAgACAAIAAgEBAAJAAkACQAJAAkEBAAKAAoACgAKAAoEBAALAAsACwALAAsABAAA").unwrap();
        _ = RcBoc::decode(data).unwrap();
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
        assert!(slice.get_reference(0).is_none());
        assert!(slice.get_reference_cloned(0).is_none());
        assert!(slice.load_reference().is_none());
        assert!(slice.load_reference_cloned().is_none());

        assert_eq!(slice.get_bit(0), Some(true));
        assert_eq!(slice.load_bit(), Some(true));
        assert_eq!(slice.get_small_uint(0, 8), Some(123));
        assert_eq!(slice.get_small_uint(8, 8), Some(111));
        assert_eq!(slice.load_u16(), Some(0x7b6f));
        assert_eq!(slice.get_u32(0), Some(0x00006ffa));
        assert_eq!(slice.get_u32(32), Some(0xd60473b3));
        assert_eq!(slice.load_u64(), Some(0x6ffad60473b3));
        assert_eq!(
            slice.load_u256(),
            Some([
                0xdf, 0x86, 0xce, 0xbc, 0xe8, 0xd5, 0xab, 0x0c, 0x69, 0xb4, 0xce, 0x33, 0xfe, 0x9b,
                0x0e, 0x2c, 0xdf, 0x69, 0xa3, 0xe1, 0x13, 0x7e, 0x64, 0x85, 0x6b, 0xbc, 0xfd, 0x39,
                0xe7, 0x9b, 0xc1, 0x6f,
            ])
        );
        assert_eq!(slice.get_small_uint(0, 1), None);
    }

    #[test]
    fn test_builder() {
        let data = base64::decode("te6ccgEBAQEAAwAAAbE=").unwrap();
        let parsed_cell = Boc::<RcCellFamily>::decode(data).unwrap();

        let mut builder = CellBuilder::<RcCellFamily>::new();
        assert!(builder.store_bit_one());
        assert!(builder.store_bit_zero());
        assert!(builder.store_bit_one());
        assert!(builder.store_bit_one());
        assert!(builder.store_bit_zero());
        assert!(builder.store_bit_zero());
        assert!(builder.store_bit_zero());
        let built_cell = builder.build().unwrap();

        assert_eq!(parsed_cell.repr_hash(), built_cell.repr_hash());

        let data = base64::decode("te6ccgEBAQEAggAA////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////").unwrap();
        let parsed_cell = RcBoc::decode(data).unwrap();

        let mut builder = RcCellBuilder::new();
        for _ in 0..cell::MAX_BIT_LEN {
            assert!(builder.store_bit_one());
        }
        assert!(!builder.store_bit_one());
        let built_cell = builder.build().unwrap();

        assert_eq!(parsed_cell.repr_hash(), built_cell.repr_hash());

        let mut builder = RcCellBuilder::new();
        assert!(builder.store_bit_one());
        assert!(builder.store_u128(0xaaffaaffaaffaaffaaffaaffaaffaaff));
        let cell = builder.build().unwrap();

        let mut builder = RcCellBuilder::new();
        assert!(builder.store_bit_one());
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
        assert!(builder.store_slice(cell.as_slice()));
        let cell = builder.build().unwrap();
        println!("{}", cell.display_tree());
    }

    #[test]
    fn test_tx() {
        RcBoc::decode_base64("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").unwrap();
    }
}
