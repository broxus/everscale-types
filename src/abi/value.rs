use std::collections::BTreeMap;
use std::num::NonZeroU8;

use bytes::Bytes;
use everscale_crypto::ed25519;
use num_bigint::{BigInt, BigUint};

use super::ty::*;
use super::AbiVersion;
use crate::cell::{Cell, CellBuilder, DefaultFinalizer, Store};
use crate::error::Error;
use crate::models::IntAddr;
use crate::num::Tokens;

/// ABI value with name.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct NamedAbiValue {
    /// Item name.
    pub name: String,
    /// ABI value.
    pub value: AbiValue,
}

impl NamedAbiValue {
    /// Returns whether all values satisfy the provided types.
    pub fn have_types(items: &[Self], types: &[NamedAbiType]) -> bool {
        items.len() == types.len()
            && items
                .iter()
                .zip(types.iter())
                .all(|(item, t)| item.value.has_type(&t.ty))
    }
}

/// ABI encoded value.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum AbiValue {
    /// Unsigned integer of n bits.
    Uint(u16, BigUint),
    /// Signed integer of n bits.
    Int(u16, BigInt),
    /// Variable-length unsigned integer of maximum n bytes.
    VarUint(NonZeroU8, BigUint),
    /// Variable-length signed integer of maximum n bytes.
    VarInt(NonZeroU8, BigInt),
    /// Boolean.
    Bool(bool),
    /// Tree of cells ([`Cell`]).
    ///
    /// [`Cell`]: crate::cell::Cell
    Cell(Cell),
    /// Internal address ([`IntAddr`]).
    ///
    /// [`IntAddr`]: crate::models::message::IntAddr
    Address(Box<IntAddr>),
    /// Byte array.
    Bytes(Bytes),
    /// Byte array of fixed length.
    FixedBytes(Bytes),
    /// Utf8-encoded string.
    String(String),
    /// Variable length 120-bit integer ([`Tokens`]).
    ///
    /// [`Tokens`]: crate::num::Tokens
    Token(Tokens),
    /// Product type.
    Tuple(Vec<NamedAbiValue>),
    /// Array of ABI values.
    Array(Box<AbiType>, Vec<Self>),
    /// Fixed-length array of ABI values.
    FixedArray(Box<AbiType>, Vec<Self>),
    /// Sorted dictionary of ABI values.
    Map(
        PlainAbiType,
        Box<AbiType>,
        BTreeMap<PlainAbiValue, AbiValue>,
    ),
    /// Optional value.
    Optional(Box<AbiType>, Option<Box<Self>>),
    /// Value stored in a new cell.
    Ref(Box<Self>),
}

impl AbiValue {
    /// Returns whether this value has the same type as the provided one.
    pub fn has_type(&self, ty: &AbiType) -> bool {
        match (self, ty) {
            (Self::Uint(n, _), AbiType::Uint(t)) => n == t,
            (Self::Int(n, _), AbiType::Int(t)) => n == t,
            (Self::VarUint(n, _), AbiType::VarUint(t)) => n == t,
            (Self::VarInt(n, _), AbiType::VarInt(t)) => n == t,
            (Self::FixedBytes(bytes), AbiType::FixedBytes(len)) => bytes.len() == *len,
            (Self::Tuple(items), AbiType::Tuple(types)) => NamedAbiValue::have_types(items, types),
            (Self::Array(ty, _), AbiType::Array(t)) => ty == t,
            (Self::FixedArray(ty, items), AbiType::FixedArray(t, len)) => {
                items.len() == *len && ty == t
            }
            (Self::Map(key_ty, value_ty, _), AbiType::Map(k, v)) => key_ty == k && value_ty == v,
            (Self::Optional(ty, _), AbiType::Optional(t)) => ty == t,
            (Self::Ref(value), AbiType::Ref(t)) => value.has_type(t),
            (Self::Bool(_), AbiType::Bool)
            | (Self::Cell(_), AbiType::Cell)
            | (Self::Address(_), AbiType::Address)
            | (Self::Bytes(_), AbiType::Bytes)
            | (Self::String(_), AbiType::String)
            | (Self::Token(_), AbiType::Token) => true,
            _ => false,
        }
    }

    /// Returns an ABI type of the value.
    pub fn get_type(&self) -> AbiType {
        match self {
            AbiValue::Uint(n, _) => AbiType::Uint(*n),
            AbiValue::Int(n, _) => AbiType::Int(*n),
            AbiValue::VarUint(n, _) => AbiType::VarUint(*n),
            AbiValue::VarInt(n, _) => AbiType::VarInt(*n),
            AbiValue::Bool(_) => AbiType::Bool,
            AbiValue::Cell(_) => AbiType::Cell,
            AbiValue::Address(_) => AbiType::Address,
            AbiValue::Bytes(_) => AbiType::Bytes,
            AbiValue::FixedBytes(bytes) => AbiType::FixedBytes(bytes.len()),
            AbiValue::String(_) => AbiType::String,
            AbiValue::Token(_) => AbiType::Token,
            AbiValue::Tuple(items) => AbiType::Tuple(
                items
                    .iter()
                    .map(|item| NamedAbiType::new(item.name.clone(), item.value.get_type()))
                    .collect(),
            ),
            AbiValue::Array(ty, _) => AbiType::Array(ty.clone()),
            AbiValue::FixedArray(ty, items) => AbiType::FixedArray(ty.clone(), items.len()),
            AbiValue::Map(key_ty, value_ty, _) => AbiType::Map(*key_ty, value_ty.clone()),
            AbiValue::Optional(ty, _) => AbiType::Optional(ty.clone()),
            AbiValue::Ref(value) => AbiType::Ref(Box::new(value.get_type())),
        }
    }

    fn store_into_part(&self, version: AbiVersion) -> Result<SerializedValue, Error> {
        // TODO: use stack from builders and reuse the top item when possible
        match self {
            Self::Uint(bits, value) => write_int(*bits, num_bigint::Sign::Plus, value),
            Self::Int(bits, value) => write_int(*bits, value.sign(), value.magnitude()),
            Self::Bool(value) => write_simple(value, 1, 0),
            Self::Cell(value) => write_simple(value, 0, 1),
            Self::Address(value) => write_simple(value, IntAddr::BITS_MAX as usize, 0),
            Self::Token(value) => write_simple(value, Tokens::MAX_BITS as usize, 0),
            _ => todo!(),
        }
    }
}

/// ABI value which has a fixed bits representation
/// and therefore can be used as a map key.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum PlainAbiValue {
    /// Unsigned integer of n bits.
    Uint(u16, BigUint),
    /// Signed integer of n bits.
    Int(u16, BigInt),
    /// Boolean.
    Bool(bool),
    /// Internal address ([`IntAddr`]).
    ///
    /// [`IntAddr`]: crate::models::message::IntAddr
    Address(Box<IntAddr>),
}

impl PlainAbiValue {
    /// Returns whether this value has the same type as the provided one.
    pub fn has_type(&self, ty: &PlainAbiType) -> bool {
        match (self, ty) {
            (Self::Uint(n, _), PlainAbiType::Uint(t)) => n == t,
            (Self::Int(n, _), PlainAbiType::Int(t)) => n == t,
            (Self::Bool(_), PlainAbiType::Bool) | (Self::Address(_), PlainAbiType::Address) => true,
            _ => false,
        }
    }
}

impl From<PlainAbiValue> for AbiValue {
    fn from(value: PlainAbiValue) -> Self {
        match value {
            PlainAbiValue::Uint(n, value) => Self::Uint(n, value),
            PlainAbiValue::Int(n, value) => Self::Int(n, value),
            PlainAbiValue::Bool(value) => Self::Bool(value),
            PlainAbiValue::Address(value) => Self::Address(value),
        }
    }
}

/// ABI header value.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum AbiHeader {
    /// `time` header.
    Time(u64),
    /// `expire` header.
    Expire(u32),
    /// `pubkey` header.
    PublicKey(Option<Box<ed25519::PublicKey>>),
}

impl AbiHeader {
    /// Returns whether this value has the same type as the provided one.
    pub fn has_type(&self, ty: &AbiHeaderType) -> bool {
        matches!(
            (self, ty),
            (Self::Time(_), AbiHeaderType::Time)
                | (Self::Expire(_), AbiHeaderType::Expire)
                | (Self::PublicKey(_), AbiHeaderType::PublicKey)
        )
    }
}

struct SerializedValue {
    pub data: CellBuilder,
    pub max_bits: usize,
    pub max_refs: usize,
}

fn write_int(bits: u16, sign: num_bigint::Sign, value: &BigUint) -> Result<SerializedValue, Error> {
    #[inline]
    fn is_zero(value: &u8) -> bool {
        *value == 0
    }

    #[inline]
    pub fn twos_complement_le(digits: &mut [u8]) {
        let mut carry = true;
        for digit in digits {
            *digit = !*digit;
            if carry {
                let (d, c) = digit.overflowing_add(1);
                *digit = d;
                carry = c;
            }
        }
    }

    fn to_signed_bytes_be(value: &BigUint) -> Vec<u8> {
        let mut bytes = value.to_bytes_le();
        let last_byte = bytes.last().cloned().unwrap_or(0);
        if last_byte > 0x7f && !(last_byte == 0x80 && bytes.iter().rev().skip(1).all(is_zero)) {
            // msb used by magnitude, extend by 1 byte
            bytes.push(0);
        }
        twos_complement_le(&mut bytes);
        bytes.reverse();
        bytes
    }

    let mut result = CellBuilder::new();

    let is_negative = sign == num_bigint::Sign::Minus;

    let bytes = if is_negative {
        to_signed_bytes_be(value)
    } else {
        value.to_bytes_be()
    };
    let value_bits = (bytes.len() * 8) as u16;

    if bytes.is_empty() {
        ok!(result.store_zeros(bits));
    } else if bits > value_bits {
        let diff = bits - value_bits;
        ok!(if is_negative {
            result.store_ones(diff)
        } else {
            result.store_zeros(diff)
        });
        ok!(result.store_raw(&bytes, value_bits));
    } else {
        let bits_offset = value_bits - bits;
        let bytes_offset = (bits_offset / 8) as usize;
        let rem = bits_offset % 8;

        let (left, right) = bytes.split_at(bytes_offset + 1);
        if let Some(left) = left.last() {
            ok!(result.store_small_uint(*left << rem, 8 - rem));
        }
        if !right.is_empty() {
            ok!(result.store_raw(right, right.len() as u16));
        }
    }

    Ok(SerializedValue {
        data: result,
        max_bits: bits as usize,
        max_refs: 0,
    })
}

fn write_simple(
    value: &dyn Store,
    max_bits: usize,
    max_refs: usize,
) -> Result<SerializedValue, Error> {
    let mut data = CellBuilder::new();
    ok!(value.store_into(&mut data, &mut Cell::default_finalizer()));
    Ok(SerializedValue {
        data,
        max_bits,
        max_refs,
    })
}
