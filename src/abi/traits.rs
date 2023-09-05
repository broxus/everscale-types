use std::collections::{BTreeMap, HashMap};
use std::num::NonZeroU8;
use std::rc::Rc;
use std::sync::Arc;

use bytes::Bytes;
use num_bigint::{BigInt, BigUint};

use super::{AbiType, AbiValue, NamedAbiType, NamedAbiValue, PlainAbiType, PlainAbiValue};
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

    i8 => Int(8),
    i16 => Int(16),
    i32 => Int(32),
    i64 => Int(64),
    i128 => Int(128),

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
        AbiType::Optional(Arc::new(T::abi_type()))
    }
}

impl<T: WithAbiType> WithAbiType for Vec<T> {
    fn abi_type() -> AbiType {
        AbiType::Array(Arc::new(T::abi_type()))
    }
}

impl<T: WithAbiType> WithAbiType for [T] {
    fn abi_type() -> AbiType {
        AbiType::Array(Arc::new(T::abi_type()))
    }
}

impl<T: WithAbiType, const N: usize> WithAbiType for [T; N] {
    fn abi_type() -> AbiType {
        AbiType::FixedArray(Arc::new(T::abi_type()), N)
    }
}

impl<K: WithPlainAbiType, V: WithAbiType> WithAbiType for BTreeMap<K, V> {
    fn abi_type() -> AbiType {
        AbiType::Map(K::plain_abi_type(), Arc::new(V::abi_type()))
    }
}

impl<K: WithPlainAbiType, V: WithAbiType, S> WithAbiType for HashMap<K, V, S> {
    fn abi_type() -> AbiType {
        AbiType::Map(K::plain_abi_type(), Arc::new(V::abi_type()))
    }
}

#[cfg(feature = "models")]
impl<T: WithAbiType> WithAbiType for crate::models::Lazy<T> {
    fn abi_type() -> AbiType {
        AbiType::Ref(Arc::new(T::abi_type()))
    }
}

impl WithAbiType for () {
    fn abi_type() -> AbiType {
        AbiType::Tuple(Arc::from([].as_slice()))
    }
}

macro_rules! impl_with_abi_type_for_tuple {
    ($($i:literal: $t:ident),+$(,)?) => {
        impl<$($t: WithAbiType),*> WithAbiType for ($($t),+,) {
            fn abi_type() -> AbiType {
                AbiType::Tuple(Arc::from(vec![
                    $(NamedAbiType::from_index($i, <$t as WithAbiType>::abi_type())),*
                ]))
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

    i8 => Int(8),
    i16 => Int(16),
    i32 => Int(32),
    i64 => Int(64),
    i128 => Int(128),

    bool => Bool,

    IntAddr => Address,
    StdAddr => Address,
    VarAddr => Address,
}

/// A type with can be converted into a plain ABI value.
pub trait IntoPlainAbi: IntoAbi {
    /// Returns a corresponding plain ABI value.
    ///
    /// NOTE: use [`IntoPlainAbi::into_plain_abi`] when building ABI from a temp value.
    fn as_plain_abi(&self) -> PlainAbiValue;

    /// Converts into a corresponding plain ABI value.
    fn into_plain_abi(self) -> PlainAbiValue
    where
        Self: Sized;
}

macro_rules! impl_into_plain_abi {
    ($($int:ty => |$n:ident| { $expr1:expr, $expr2:expr $(,)? }),*$(,)?) => {$(
        impl IntoPlainAbi for $int {
            #[inline]
            fn as_plain_abi(&self) -> PlainAbiValue {
                let $n = self;
                $expr1
            }

            #[inline]
            fn into_plain_abi(self) -> PlainAbiValue
            where
                Self: Sized
            {
                let $n = self;
                $expr2
            }
        }
    )*};
}

impl_into_plain_abi! {
    PlainAbiValue => |v| { v.clone(), v },

    u8 => |v| {
        PlainAbiValue::Uint(8, BigUint::from(*v)),
        PlainAbiValue::Uint(8, BigUint::from(v)),
    },
    u16 => |v| {
        PlainAbiValue::Uint(16, BigUint::from(*v)),
        PlainAbiValue::Uint(16, BigUint::from(v)),
    },
    u32 => |v| {
        PlainAbiValue::Uint(32, BigUint::from(*v)),
        PlainAbiValue::Uint(32, BigUint::from(v)),
    },
    u64 => |v| {
        PlainAbiValue::Uint(64, BigUint::from(*v)),
        PlainAbiValue::Uint(64, BigUint::from(v)),
    },
    u128 => |v| {
        PlainAbiValue::Uint(128, BigUint::from(*v)),
        PlainAbiValue::Uint(128, BigUint::from(v)),
    },
    HashBytes => |v| {
        PlainAbiValue::Uint(256, BigUint::from_bytes_be(v.as_array())),
        PlainAbiValue::Uint(256, BigUint::from_bytes_be(v.as_array())),
    },
    SplitDepth => |v| {
        PlainAbiValue::Uint(5, BigUint::from(v.into_bit_len())),
        PlainAbiValue::Uint(5, BigUint::from(v.into_bit_len())),
    },
    Uint9 => |v| {
        PlainAbiValue::Uint(9, BigUint::from(v.into_inner())),
        PlainAbiValue::Uint(9, BigUint::from(v.into_inner())),
    },
    Uint12 => |v| {
        PlainAbiValue::Uint(12, BigUint::from(v.into_inner())),
        PlainAbiValue::Uint(12, BigUint::from(v.into_inner())),
    },
    Uint15 => |v| {
        PlainAbiValue::Uint(15, BigUint::from(v.into_inner())),
        PlainAbiValue::Uint(15, BigUint::from(v.into_inner())),
    },

    i8 => |v| {
        PlainAbiValue::Int(8, BigInt::from(*v)),
        PlainAbiValue::Int(8, BigInt::from(v)),
    },
    i16 => |v| {
        PlainAbiValue::Int(16, BigInt::from(*v)),
        PlainAbiValue::Int(16, BigInt::from(v)),
    },
    i32 => |v| {
        PlainAbiValue::Int(32, BigInt::from(*v)),
        PlainAbiValue::Int(32, BigInt::from(v)),
    },
    i64 => |v| {
        PlainAbiValue::Int(64, BigInt::from(*v)),
        PlainAbiValue::Int(64, BigInt::from(v)),
    },
    i128 => |v| {
        PlainAbiValue::Int(128, BigInt::from(*v)),
        PlainAbiValue::Int(128, BigInt::from(v)),
    },

    bool => |v| {
        PlainAbiValue::Bool(*v),
        PlainAbiValue::Bool(v),
    },

    IntAddr => |v| {
        PlainAbiValue::Address(Box::new(v.clone())),
        PlainAbiValue::Address(Box::new(v)),
    },
    StdAddr => |v| {
        PlainAbiValue::Address(Box::new(v.clone().into())),
        PlainAbiValue::Address(Box::new(v.into())),
    },
    VarAddr => |v| {
        PlainAbiValue::Address(Box::new(v.clone().into())),
        PlainAbiValue::Address(Box::new(v.into())),
    },
}

/// A type with can be converted into an ABI value.
pub trait IntoAbi {
    /// Returns a corresponding ABI value.
    ///
    /// NOTE: use [`IntoAbi::into_abi`] when building ABI from a temp value.
    fn as_abi(&self) -> AbiValue;

    /// Converts into a corresponding ABI value.
    fn into_abi(self) -> AbiValue
    where
        Self: Sized;
}

macro_rules! impl_into_abi {
    ($($int:ty => |$n:ident| { $expr1:expr, $expr2:expr $(,)? }),*$(,)?) => {$(
        impl IntoAbi for $int {
            #[inline]
            fn as_abi(&self) -> AbiValue {
                let $n = self;
                $expr1
            }

            #[inline]
            fn into_abi(self) -> AbiValue
            where
                Self: Sized
            {
                let $n = self;
                $expr2
            }
        }
    )*};
}

impl_into_abi! {
    AbiValue => |v| { v.clone(), v },
    PlainAbiValue => |v| { v.clone().into(), v.into() },

    u8 => |v| {
        AbiValue::Uint(8, BigUint::from(*v)),
        AbiValue::Uint(8, BigUint::from(v)),
    },
    u16 => |v| {
        AbiValue::Uint(16, BigUint::from(*v)),
        AbiValue::Uint(16, BigUint::from(v)),
    },
    u32 => |v| {
        AbiValue::Uint(32, BigUint::from(*v)),
        AbiValue::Uint(32, BigUint::from(v)),
    },
    u64 => |v| {
        AbiValue::Uint(64, BigUint::from(*v)),
        AbiValue::Uint(64, BigUint::from(v)),
    },
    u128 => |v| {
        AbiValue::Uint(128, BigUint::from(*v)),
        AbiValue::Uint(128, BigUint::from(v)),
    },
    HashBytes => |v| {
        AbiValue::Uint(256, BigUint::from_bytes_be(v.as_array())),
        AbiValue::Uint(256, BigUint::from_bytes_be(v.as_array())),
    },
    SplitDepth => |v| {
        AbiValue::Uint(5, BigUint::from(v.into_bit_len())),
        AbiValue::Uint(5, BigUint::from(v.into_bit_len())),
    },
    Uint9 => |v| {
        AbiValue::Uint(9, BigUint::from(v.into_inner())),
        AbiValue::Uint(9, BigUint::from(v.into_inner())),
    },
    Uint12 => |v| {
        AbiValue::Uint(12, BigUint::from(v.into_inner())),
        AbiValue::Uint(12, BigUint::from(v.into_inner())),
    },
    Uint15 => |v| {
        AbiValue::Uint(15, BigUint::from(v.into_inner())),
        AbiValue::Uint(15, BigUint::from(v.into_inner())),
    },

    i8 => |v| {
        AbiValue::Int(8, BigInt::from(*v)),
        AbiValue::Int(8, BigInt::from(v)),
    },
    i16 => |v| {
        AbiValue::Int(16, BigInt::from(*v)),
        AbiValue::Int(16, BigInt::from(v)),
    },
    i32 => |v| {
        AbiValue::Int(32, BigInt::from(*v)),
        AbiValue::Int(32, BigInt::from(v)),
    },
    i64 => |v| {
        AbiValue::Int(64, BigInt::from(*v)),
        AbiValue::Int(64, BigInt::from(v)),
    },
    i128 => |v| {
        AbiValue::Int(128, BigInt::from(*v)),
        AbiValue::Int(128, BigInt::from(v)),
    },

    bool => |v| {
        AbiValue::Bool(*v),
        AbiValue::Bool(v),
    },

    VarUint24 => |v| {
        AbiValue::VarUint(NonZeroU8::new(4).unwrap(), BigUint::from(v.into_inner())),
        AbiValue::VarUint(NonZeroU8::new(4).unwrap(), BigUint::from(v.into_inner())),
    },
    VarUint56 => |v| {
        AbiValue::VarUint(NonZeroU8::new(8).unwrap(), BigUint::from(v.into_inner())),
        AbiValue::VarUint(NonZeroU8::new(8).unwrap(), BigUint::from(v.into_inner())),
    },

    Tokens => |v| {
        AbiValue::Token(*v),
        AbiValue::Token(v),
    },

    Cell => |v| {
        AbiValue::Cell(v.clone()),
        AbiValue::Cell(v),
    },

    Bytes => |v| {
        AbiValue::Bytes(v.clone()),
        AbiValue::Bytes(v),
    },
    String => |v| {
        AbiValue::String(v.clone()),
        AbiValue::String(v),
    },

    IntAddr => |v| {
        AbiValue::Address(Box::new(v.clone())),
        AbiValue::Address(Box::new(v)),
    },
    StdAddr => |v| {
        AbiValue::Address(Box::new(v.clone().into())),
        AbiValue::Address(Box::new(v.into())),
    },
    VarAddr => |v| {
        AbiValue::Address(Box::new(v.clone().into())),
        AbiValue::Address(Box::new(v.into())),
    },
}

impl IntoAbi for str {
    #[inline]
    fn as_abi(&self) -> AbiValue {
        AbiValue::String(self.to_owned())
    }

    #[inline]
    fn into_abi(self) -> AbiValue
    where
        for<'a> str: Sized,
    {
        unreachable!()
    }
}

impl<T: WithAbiType + IntoAbi> IntoAbi for [T] {
    fn as_abi(&self) -> AbiValue {
        AbiValue::Array(
            Arc::new(T::abi_type()),
            self.iter().map(T::as_abi).collect(),
        )
    }

    #[inline]
    fn into_abi(self) -> AbiValue
    where
        for<'a> [T]: Sized,
    {
        unreachable!()
    }
}

impl<T: WithAbiType + IntoAbi> IntoAbi for Vec<T> {
    fn as_abi(&self) -> AbiValue {
        AbiValue::Array(
            Arc::new(T::abi_type()),
            self.iter().map(T::as_abi).collect(),
        )
    }

    fn into_abi(self) -> AbiValue
    where
        Self: Sized,
    {
        AbiValue::Array(
            Arc::new(T::abi_type()),
            self.into_iter().map(T::into_abi).collect(),
        )
    }
}

impl<K: WithPlainAbiType + IntoPlainAbi, V: WithAbiType + IntoAbi> IntoAbi for BTreeMap<K, V> {
    fn as_abi(&self) -> AbiValue {
        AbiValue::Map(
            K::plain_abi_type(),
            Arc::new(V::abi_type()),
            self.iter()
                .map(|(key, value)| (K::as_plain_abi(key), V::as_abi(value)))
                .collect(),
        )
    }

    fn into_abi(self) -> AbiValue
    where
        Self: Sized,
    {
        AbiValue::Map(
            K::plain_abi_type(),
            Arc::new(V::abi_type()),
            self.into_iter()
                .map(|(key, value)| (K::into_plain_abi(key), V::into_abi(value)))
                .collect(),
        )
    }
}

impl<K: WithPlainAbiType + IntoPlainAbi, V: WithAbiType + IntoAbi, S> IntoAbi for HashMap<K, V, S> {
    fn as_abi(&self) -> AbiValue {
        AbiValue::Map(
            K::plain_abi_type(),
            Arc::new(V::abi_type()),
            self.iter()
                .map(|(key, value)| (K::as_plain_abi(key), V::as_abi(value)))
                .collect(),
        )
    }

    fn into_abi(self) -> AbiValue
    where
        Self: Sized,
    {
        AbiValue::Map(
            K::plain_abi_type(),
            Arc::new(V::abi_type()),
            self.into_iter()
                .map(|(key, value)| (K::into_plain_abi(key), V::into_abi(value)))
                .collect(),
        )
    }
}

impl<T: WithAbiType + IntoAbi> IntoAbi for Option<T> {
    #[inline]
    fn as_abi(&self) -> AbiValue {
        AbiValue::Optional(
            Arc::new(T::abi_type()),
            self.as_ref().map(T::as_abi).map(Box::new),
        )
    }

    #[inline]
    fn into_abi(self) -> AbiValue
    where
        Self: Sized,
    {
        AbiValue::Optional(Arc::new(T::abi_type()), self.map(T::into_abi).map(Box::new))
    }
}

impl IntoAbi for () {
    #[inline]
    fn as_abi(&self) -> AbiValue {
        AbiValue::Tuple(Vec::new())
    }

    #[inline]
    fn into_abi(self) -> AbiValue
    where
        Self: Sized,
    {
        self.as_abi()
    }
}

macro_rules! impl_into_abi_for_tuple {
    ($($i:tt: $t:ident),+$(,)?) => {
        impl<$($t: IntoAbi),*> IntoAbi for ($($t),+,) {
            fn as_abi(&self) -> AbiValue {
                AbiValue::Tuple(vec![
                    $(NamedAbiValue::from_index($i, <$t as IntoAbi>::as_abi(&self.$i))),*
                ])
            }

            fn into_abi(self) -> AbiValue
            where
                Self: Sized,
            {
                AbiValue::Tuple(vec![
                    $(NamedAbiValue::from_index($i, <$t as IntoAbi>::into_abi(self.$i))),*
                ])
            }
        }
    };
}

impl_into_abi_for_tuple! { 0: T0 }
impl_into_abi_for_tuple! { 0: T0, 1: T1 }
impl_into_abi_for_tuple! { 0: T0, 1: T1, 2: T2 }
impl_into_abi_for_tuple! { 0: T0, 1: T1, 2: T2, 3: T3 }
impl_into_abi_for_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4 }
impl_into_abi_for_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5 }
impl_into_abi_for_tuple! { 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6 }

#[cfg(test)]
mod tests {
    use crate::prelude::CellFamily;

    use super::*;

    #[test]
    fn tuple_to_abi() {
        let target_abi = AbiValue::unnamed_tuple([
            AbiValue::uint(32, 123u32),
            AbiValue::uint(32, 321u32),
            AbiValue::Bool(true),
            AbiValue::unnamed_tuple([
                AbiValue::Cell(Cell::empty_cell()),
                AbiValue::Optional(Arc::new(AbiType::Bool), None),
            ]),
        ]);

        let abi = (123u32, 321u32, true, (Cell::empty_cell(), None::<bool>));

        assert_eq!(abi.into_abi(), target_abi);
    }
}
