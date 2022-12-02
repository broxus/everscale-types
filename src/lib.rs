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
pub use self::cell::rc::{RcCell, RcCellFamily};
pub use self::cell::sync::{ArcCell, ArcCellFamily};
pub use self::cell::{Cell, CellDescriptor, LevelMask};

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
        let data = base64::decode("te6ccgEBAQEABQAABb23wA==").unwrap();
        let cell = Boc::<RcCellFamily>::decode(data).unwrap();
        println!("{}", cell.display_tree());

        let mut slice = cell.as_slice();
        assert!(!slice.is_data_empty());
        assert_eq!(slice.remaining_bits(), 17);
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
        assert_eq!(slice.get_bits(16, 1), None);
    }
}
