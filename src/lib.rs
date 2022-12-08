macro_rules! ok {
    ($e:expr $(,)?) => {
        match $e {
            core::result::Result::Ok(val) => val,
            core::result::Result::Err(err) => return core::result::Result::Err(err),
        }
    };
}

macro_rules! offset_of {
    ($ty: path, $field: tt) => {{
        let $ty { $field: _, .. };

        let uninit = ::std::mem::MaybeUninit::<$ty>::uninit();
        let base_ptr = uninit.as_ptr() as *const $ty;
        unsafe {
            let field_ptr = std::ptr::addr_of!((*base_ptr).$field);
            (field_ptr as *const u8).offset_from(base_ptr as *const u8) as usize
        }
    }};
}

pub use self::boc::Boc;
pub use self::cell::builder::CellBuilder;
pub use self::cell::rc::{RcCell, RcCellFamily};
pub use self::cell::slice::CellSlice;
pub use self::cell::sync::{ArcCell, ArcCellFamily};
pub use self::cell::{Cell, CellDescriptor, CellHash, LevelMask};

pub mod boc;
pub mod cell;
pub mod util;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn correct_deserialization() {
        let data = base64::decode("te6ccgEBBAEAzwACg4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEAIBAEAAAAAAAAAAAAAAAAAAAAAAAAAAm2c6ClpzoTVSAHvzVQGDAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHKq1w7OAAkYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACRwAwBAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEljGP8=").unwrap();

        let cell = Boc::<ArcCellFamily>::decode(&data).unwrap();
        println!("{}", cell.display_tree());

        let cell = Boc::<RcCellFamily>::decode(&data).unwrap();
        println!("{}", cell.display_tree());
    }

    #[test]
    fn cell_slices() {
        let data = base64::decode(
            "te6ccgEBAQEALQAAVb23gAA3/WsCOdnvw2dedGrVhjTaZxn/TYcWb7TR8Im/MkK13n6c883gt8A=",
        )
        .unwrap();
        let cell = Boc::<RcCellFamily>::decode(data).unwrap();
        println!("{}", cell.display_tree());

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
        let parsed_cell = Boc::<RcCellFamily>::decode(data).unwrap();

        let mut builder = CellBuilder::<RcCellFamily>::new();
        for _ in 0..cell::MAX_BIT_LEN {
            assert!(builder.store_bit_true());
        }
        assert!(!builder.store_bit_true());
        let built_cell = builder.build().unwrap();

        println!("{}", built_cell.display_tree());
        println!("{}", parsed_cell.display_tree());

        assert_eq!(parsed_cell.repr_hash(), built_cell.repr_hash());
    }
}
