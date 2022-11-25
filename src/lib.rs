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

#[cfg(debug_assertions)]
macro_rules! debug_unreachable {
    () => {
        unreachable!()
    };
}

#[cfg(not(debug_assertions))]
macro_rules! debug_unreachable {
    () => {
        unsafe { std::hint::unreachable_unchecked() }
    };
}

pub use self::cell::Cell;

pub mod boc;
pub mod cell;
pub mod util;
pub mod error;
