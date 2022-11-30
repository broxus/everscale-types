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
pub use self::cell::{ArcCell, Cell, CellDescriptor, LevelMask};

pub mod boc;
pub mod cell;
pub mod util;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn correct_deserialization() {
        let data = base64::decode("te6ccgEBBAEAzwACg4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEAIBAEAAAAAAAAAAAAAAAAAAAAAAAAAAm2c6ClpzoTVSAHvzVQGDAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHKq1w7OAAkYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACRwAwBAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEljGP8=").unwrap();
        //let data = base64::decode("te6ccgEBAQEABgAACACrQTA=").unwrap();
        let cell = Boc::decode(data).unwrap();
        println!("{}", cell.display_tree());
    }

    #[test]
    fn test_cell() {
        let data = [
            104, 255, 101, 243, 1, 1, 33, 1, 0, 104, 0, 1, 1, 1, 1, 1, 1, 196, 1, 37, 13, 34, 171,
            101, 40, 227, 0, 0, 0, 0, 0, 0, 33, 1, 1, 1, 40, 1, 1, 72, 72, 1, 2, 65, 72, 72, 1, 10,
            127, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 1, 1, 40, 1, 1, 72, 72, 1, 2, 1, 72, 72, 1, 115, 1, 1, 255, 250, 1, 1, 1, 196, 1,
            10, 127, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1,
            72, 72, 1, 2, 1, 72, 72, 1, 115, 1, 1, 254, 1, 1, 1, 1, 196, 1, 37, 13, 34, 255, 101,
            72, 72, 250, 140, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65, 0, 32, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 72, 72, 1, 2, 1, 72, 72, 1, 141, 3, 0, 0, 0,
            0, 0, 0, 0, 13, 34, 255, 101, 104, 7, 0, 127, 0, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 1, 10, 64, 40,
            243, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            1, 1, 72, 72, 1, 0, 150, 221, 30, 120, 127, 0, 0, 2, 1, 1, 115, 1, 1, 1, 0, 1, 72,
        ];
        println!("{}", base64::encode(data));
        let cell = Boc::decode(data).unwrap();
        println!("{}", cell.display_tree());
    }
}
