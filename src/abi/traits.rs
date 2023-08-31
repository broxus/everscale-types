use std::collections::{BTreeMap, HashMap};
use std::num::NonZeroU8;
use std::rc::Rc;
use std::sync::Arc;

use bytes::Bytes;

use super::{AbiType, NamedAbiType, PlainAbiType};
use crate::cell::{Cell, HashBytes};
use crate::num::*;

use crate::models::message::{IntAddr, StdAddr, VarAddr};

/// A type with a known ABI type.
pub trait WithAbiType {
    /// Returns a corresponding ABI type.
    fn abi_type() -> AbiType;
}

macro_rules! impl_with_abi_type {
    ($($ty:ty => $ident:ident$(($n:expr))?),*$(,)?) => {$(
        impl WithAbiType for $ty {
            fn abi_type() -> AbiType {
                AbiType::$ident$(($n))?
            }
        }
    )*};
}

impl_with_abi_type! {
    u8 => Uint(8),
    u16 => Uint(16),
    u32 => Uint(32),
    u64 => Uint(64),
    u128 => Uint(128),
    HashBytes => Uint(256),
    SplitDepth => Uint(5),
    Uint9 => Uint(9),
    Uint12 => Uint(12),
    Uint15 => Uint(15),

    i8 => Uint(8),
    i16 => Uint(16),
    i32 => Uint(32),
    i64 => Uint(64),
    i128 => Uint(128),

    bool => Bool,

    VarUint24 => VarUint(NonZeroU8::new(4).unwrap()),
    VarUint56 => VarUint(NonZeroU8::new(8).unwrap()),
    VarUint248 => VarUint(NonZeroU8::new(32).unwrap()),

    Tokens => Token,

    Cell => Cell,

    Bytes => Bytes,
    String => String,
    str => String,

    IntAddr => Address,
    StdAddr => Address,
    VarAddr => Address,
}

impl<T: WithAbiType> WithAbiType for &T {
    fn abi_type() -> AbiType {
        T::abi_type()
    }
}

impl<T: WithAbiType> WithAbiType for &mut T {
    fn abi_type() -> AbiType {
        T::abi_type()
    }
}

impl<T: WithAbiType> WithAbiType for Box<T> {
    fn abi_type() -> AbiType {
        T::abi_type()
    }
}

impl<T: WithAbiType> WithAbiType for Arc<T> {
    fn abi_type() -> AbiType {
        T::abi_type()
    }
}

impl<T: WithAbiType> WithAbiType for Rc<T> {
    fn abi_type() -> AbiType {
        T::abi_type()
    }
}

impl<T: WithAbiType> WithAbiType for Option<T> {
    fn abi_type() -> AbiType {
        AbiType::Optional(Box::new(T::abi_type()))
    }
}

impl<T: WithAbiType> WithAbiType for Vec<T> {
    fn abi_type() -> AbiType {
        AbiType::Array(Box::new(T::abi_type()))
    }
}

impl<T: WithAbiType> WithAbiType for [T] {
    fn abi_type() -> AbiType {
        AbiType::Array(Box::new(T::abi_type()))
    }
}

impl<T: WithAbiType, const N: usize> WithAbiType for [T; N] {
    fn abi_type() -> AbiType {
        AbiType::FixedArray(Box::new(T::abi_type()), N)
    }
}

impl<K: WithPlainAbiType, V: WithAbiType> WithAbiType for BTreeMap<K, V> {
    fn abi_type() -> AbiType {
        AbiType::Map(K::plain_abi_type(), Box::new(V::abi_type()))
    }
}

impl<K: WithPlainAbiType, V: WithAbiType, S> WithAbiType for HashMap<K, V, S> {
    fn abi_type() -> AbiType {
        AbiType::Map(K::plain_abi_type(), Box::new(V::abi_type()))
    }
}

#[cfg(feature = "models")]
impl<T: WithAbiType> WithAbiType for crate::models::Lazy<T> {
    fn abi_type() -> AbiType {
        AbiType::Ref(Box::new(T::abi_type()))
    }
}

impl WithAbiType for () {
    fn abi_type() -> AbiType {
        AbiType::Tuple(Vec::new())
    }
}

macro_rules! impl_with_abi_type_for_tuple {
    ($($i:literal: $t:ident),+$(,)?) => {
        impl<$($t: WithAbiType),*> WithAbiType for ($($t),+,) {
            fn abi_type() -> AbiType {
                AbiType::Tuple(vec![
                    $(NamedAbiType::from_index($i, <$t as WithAbiType>::abi_type())),*
                ])
            }
        }
    };
}

impl_with_abi_type_for_tuple! { 0: T0 }
impl_with_abi_type_for_tuple! { 0: T0, 1: T1 }
impl_with_abi_type_for_tuple! { 0: T0, 1: T1, 2: T2 }
impl_with_abi_type_for_tuple! { 0: T0, 1: T1, 2: T2, 3: T3 }
impl_with_abi_type_for_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4 }
impl_with_abi_type_for_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5 }
impl_with_abi_type_for_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6 }

/// A type with a known plain ABI type.
pub trait WithPlainAbiType: WithAbiType {
    /// Returns a corresponding plain ABI type.
    fn plain_abi_type() -> PlainAbiType;
}

macro_rules! impl_with_plain_abi_type {
    ($($int:ty => $ident:ident$(($n:literal))?),*$(,)?) => {$(
        impl WithPlainAbiType for $int {
            fn plain_abi_type() -> PlainAbiType {
                PlainAbiType::$ident$(($n))?
            }
        }
    )*};
}

impl_with_plain_abi_type! {
    u8 => Uint(8),
    u16 => Uint(16),
    u32 => Uint(32),
    u64 => Uint(64),
    u128 => Uint(128),
    HashBytes => Uint(256),
    SplitDepth => Uint(5),
    Uint9 => Uint(9),
    Uint12 => Uint(12),
    Uint15 => Uint(15),

    i8 => Uint(8),
    i16 => Uint(16),
    i32 => Uint(32),
    i64 => Uint(64),
    i128 => Uint(128),

    bool => Bool,

    IntAddr => Address,
    StdAddr => Address,
    VarAddr => Address,
}
