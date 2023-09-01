use std::collections::BTreeMap;
use std::num::NonZeroU8;

use bytes::Bytes;
use everscale_crypto::ed25519;
use num_bigint::{BigInt, BigUint, Sign};

use super::ty::*;
use super::AbiVersion;
use crate::cell::{
    Cell, CellBuilder, CellSlice, DefaultFinalizer, Finalizer, Store, MAX_BIT_LEN, MAX_REF_COUNT,
};
use crate::dict::{self, RawDict};
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
    /// Tries to store multiple values into a new builder according to the specified ABI version.
    pub fn tuple_to_builder(items: &[Self], version: AbiVersion) -> Result<CellBuilder, Error> {
        let mut parts = Vec::new();
        for item in items {
            ok!(item.value.store_as_parts(version, &mut parts));
        }
        SerializedPart::pack(parts, version)
    }

    /// Builds a new cell from multiple values according to the specified ABI version.
    pub fn tuple_to_cell(items: &[Self], version: AbiVersion) -> Result<Cell, Error> {
        Self::tuple_to_builder(items, version).and_then(CellBuilder::build)
    }

    /// Tries to store this value into a new builder according to the specified ABI version.
    pub fn make_builder(&self, version: AbiVersion) -> Result<CellBuilder, Error> {
        let mut parts = Vec::new();
        ok!(self.value.store_as_parts(version, &mut parts));
        SerializedPart::pack(parts, version)
    }

    /// Builds a new cell from this value according to the specified ABI version.
    pub fn make_cell(&self, version: AbiVersion) -> Result<Cell, Error> {
        self.make_builder(version).and_then(CellBuilder::build)
    }

    /// Returns whether all values satisfy the provided types.
    pub fn have_types(items: &[Self], types: &[NamedAbiType]) -> bool {
        items.len() == types.len()
            && items
                .iter()
                .zip(types.iter())
                .all(|(item, t)| item.value.has_type(&t.ty))
    }

    /// Creates a named ABI value with an index name (e.g. `value123`).
    pub fn from_index(index: usize, value: AbiValue) -> Self {
        Self {
            name: format!("value{index}"),
            value,
        }
    }
}

impl From<(String, AbiValue)> for NamedAbiValue {
    #[inline]
    fn from((name, value): (String, AbiValue)) -> Self {
        Self { name, value }
    }
}

impl<'a> From<(&'a str, AbiValue)> for NamedAbiValue {
    #[inline]
    fn from((name, value): (&'a str, AbiValue)) -> Self {
        Self {
            name: name.to_owned(),
            value,
        }
    }
}

impl From<(usize, AbiValue)> for NamedAbiValue {
    #[inline]
    fn from((index, value): (usize, AbiValue)) -> Self {
        Self::from_index(index, value)
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
    /// Tries to store multiple values into a new builder according to the specified ABI version.
    pub fn tuple_to_builder(values: &[Self], version: AbiVersion) -> Result<CellBuilder, Error> {
        let mut parts = Vec::new();
        for value in values {
            ok!(value.store_as_parts(version, &mut parts));
        }
        SerializedPart::pack(parts, version)
    }

    /// Builds a new cell from multiple values according to the specified ABI version.
    pub fn tuple_to_cell(values: &[Self], version: AbiVersion) -> Result<Cell, Error> {
        Self::tuple_to_builder(values, version).and_then(CellBuilder::build)
    }

    /// Tries to store this value into a new builder according to the specified ABI version.
    pub fn make_builder(&self, version: AbiVersion) -> Result<CellBuilder, Error> {
        let mut parts = Vec::new();
        ok!(self.store_as_parts(version, &mut parts));
        SerializedPart::pack(parts, version)
    }

    /// Builds a new cell from this value according to the specified ABI version.
    pub fn make_cell(&self, version: AbiVersion) -> Result<Cell, Error> {
        self.make_builder(version).and_then(CellBuilder::build)
    }

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

    fn store_as_parts(
        &self,
        version: AbiVersion,
        parts: &mut Vec<SerializedPart>,
    ) -> Result<(), Error> {
        let mut b = CellBuilder::new();

        let res = match self {
            Self::Tuple(items) => {
                for item in items {
                    ok!(item.value.store_as_parts(version, parts));
                }
                return Ok(());
            }
            Self::Uint(n, value) => write_int(*n, Sign::Plus, value, &mut b),
            Self::Int(n, value) => write_int(*n, value.sign(), value.magnitude(), &mut b),
            Self::VarUint(n, value) => write_varint(*n, Sign::Plus, value, &mut b),
            Self::VarInt(n, value) => write_varint(*n, value.sign(), value.magnitude(), &mut b),
            Self::Bool(value) => write_simple(value, 1, 0, &mut b),
            Self::Cell(value) => write_simple(value, 0, 1, &mut b),
            Self::Address(value) => write_simple(value, IntAddr::BITS_MAX, 0, &mut b),
            Self::Bytes(value) | Self::FixedBytes(value) => write_bytes(value, version, &mut b),
            Self::String(value) => write_bytes(value.as_bytes(), version, &mut b),
            Self::Token(value) => write_simple(value, Tokens::MAX_BITS, 0, &mut b),
            Self::Array(ty, values) => write_array(ty, values, false, version, &mut b),
            Self::FixedArray(ty, values) => write_array(ty, values, true, version, &mut b),
            Self::Map(k, v, values) => write_map(k, v, values, version, &mut b),
            Self::Optional(ty, value) => write_optional(ty, value.as_deref(), version, &mut b),
            Self::Ref(value) => write_ref(value, version, &mut b),
        };
        let (max_bits, max_refs) = ok!(res);

        parts.push(SerializedPart {
            data: b,
            max_bits,
            max_refs,
        });
        Ok(())
    }
}

// === impl AbiValue constructors ===

impl AbiValue {
    /// Simple `uintN` constructor.
    #[inline]
    pub fn uint<T>(bits: u16, value: T) -> Self
    where
        BigUint: From<T>,
    {
        Self::Uint(bits, BigUint::from(value))
    }

    /// Simple `intN` constructor.
    #[inline]
    pub fn int<T>(bits: u16, value: T) -> Self
    where
        BigInt: From<T>,
    {
        Self::Int(bits, BigInt::from(value))
    }

    /// Simple `address` constructor.
    #[inline]
    pub fn address<T>(value: T) -> Self
    where
        IntAddr: From<T>,
    {
        Self::Address(Box::new(IntAddr::from(value)))
    }

    /// Simple `bytes` constructor.
    #[inline]
    pub fn bytes<T>(value: T) -> Self
    where
        Bytes: From<T>,
    {
        Self::Bytes(Bytes::from(value))
    }

    /// Simple `bytes` constructor.
    #[inline]
    pub fn fixedbytes<T>(value: T) -> Self
    where
        Bytes: From<T>,
    {
        Self::FixedBytes(Bytes::from(value))
    }

    /// Simple `tuple` constructor.
    #[inline]
    pub fn tuple<I, T>(values: I) -> Self
    where
        I: IntoIterator<Item = T>,
        NamedAbiValue: From<T>,
    {
        Self::Tuple(values.into_iter().map(NamedAbiValue::from).collect())
    }

    /// Simple `tuple` constructor.
    #[inline]
    pub fn unnamed_tuple<I>(values: I) -> Self
    where
        I: IntoIterator<Item = AbiValue>,
    {
        Self::Tuple(
            values
                .into_iter()
                .enumerate()
                .map(|(i, value)| NamedAbiValue::from_index(i, value))
                .collect(),
        )
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

impl Store for PlainAbiValue {
    fn store_into(&self, builder: &mut CellBuilder, f: &mut dyn Finalizer) -> Result<(), Error> {
        match self {
            Self::Uint(bits, value) => {
                ok!(write_int(*bits, Sign::Plus, value, builder));
                Ok(())
            }
            Self::Int(bits, value) => {
                ok!(write_int(*bits, value.sign(), value.magnitude(), builder));
                Ok(())
            }
            Self::Bool(bit) => builder.store_bit(*bit),
            Self::Address(address) => address.store_into(builder, f),
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

struct SerializedPart {
    data: CellBuilder,
    max_bits: u16,
    max_refs: u8,
}

impl SerializedPart {
    fn pack(mut values: Vec<Self>, version: AbiVersion) -> Result<CellBuilder, Error> {
        // NOTE: this algorithm was copied from `ever-abi` but it is highly
        // inefficient. So, TODO: rewrite

        let use_max = version >= AbiVersion::V2_2;

        values.reverse();

        let mut packed_cells = match values.pop() {
            Some(cell) => vec![cell],
            None => return Err(Error::InvalidData),
        };
        while let Some(value) = values.pop() {
            let last_cell = packed_cells.last_mut().unwrap();

            let (remaining_bits, remaining_refs) = if use_max {
                (
                    MAX_BIT_LEN - last_cell.max_bits,
                    MAX_REF_COUNT as u8 - last_cell.max_refs,
                )
            } else {
                (
                    last_cell.data.spare_bits_capacity(),
                    last_cell.data.spare_refs_capacity(),
                )
            };
            let (value_bits, value_refs) = if use_max {
                (value.max_bits, value.max_refs)
            } else {
                (value.data.bit_len(), value.data.references().len() as u8)
            };

            let store_inline = if remaining_bits < value_bits || remaining_refs < value_refs {
                false
            } else if value_refs > 0 && value_refs == remaining_refs {
                let (bits, refs) = Self::compute_total_size(&values, version);
                version.major != 1
                    && (refs == 0 && value_bits as usize + bits <= remaining_bits as usize)
            } else {
                true
            };

            if store_inline {
                ok!(last_cell.data.store_builder(&value.data));
                last_cell.max_bits += value.max_bits;
                last_cell.max_refs += value.max_refs;
            } else {
                packed_cells.push(value);
            }
        }

        let mut last_cell = match packed_cells.pop() {
            Some(last_cell) => last_cell.data,
            None => return Err(Error::InvalidData),
        };

        while let Some(child) = packed_cells.pop() {
            let child = ok!(std::mem::replace(&mut last_cell, child.data).build());
            ok!(last_cell.store_reference(child));
        }

        Ok(last_cell)
    }

    fn compute_total_size(values: &[Self], version: AbiVersion) -> (usize, usize) {
        let use_max = version >= AbiVersion::V2_2;

        let mut result = (0, 0);
        let (total_bits, total_refs) = &mut result;
        for value in values {
            if use_max {
                *total_bits += value.max_bits as usize;
                *total_refs += value.max_refs as usize;
            } else {
                *total_bits += value.data.bit_len() as usize;
                *total_refs += value.data.references().len();
            }
        }

        result
    }
}

fn write_int(
    bits: u16,
    sign: Sign,
    value: &BigUint,
    target: &mut CellBuilder,
) -> Result<(u16, u8), Error> {
    if value.bits() > bits as u64 {
        return Err(Error::IntOverflow);
    }

    let is_negative = sign == Sign::Minus;
    let bytes = to_signed_bytes_be(is_negative, value);
    let value_bits = (bytes.len() * 8) as u16;

    if bytes.is_empty() {
        ok!(target.store_zeros(bits));
    } else if bits > value_bits {
        let diff = bits - value_bits;
        ok!(if is_negative {
            target.store_ones(diff)
        } else {
            target.store_zeros(diff)
        });
        ok!(target.store_raw(&bytes, value_bits));
    } else {
        let bits_offset = value_bits - bits;
        let bytes_offset = (bits_offset / 8) as usize;
        let rem = bits_offset % 8;

        let (left, right) = bytes.split_at(bytes_offset + 1);
        if let Some(left) = left.last() {
            ok!(target.store_small_uint(*left << rem, 8 - rem));
        }
        if !right.is_empty() {
            ok!(target.store_raw(right, right.len() as u16));
        }
    }

    Ok((bits, 0))
}

fn write_varint(
    size: NonZeroU8,
    sign: Sign,
    value: &BigUint,
    target: &mut CellBuilder,
) -> Result<(u16, u8), Error> {
    let is_negative = sign == Sign::Minus;
    let bytes = to_signed_bytes_be(is_negative, value);

    let value_size = size.get() - 1;
    if bytes.len() > value_size as usize {
        return Err(Error::IntOverflow);
    }

    let len_bits = (8 - value_size.leading_zeros()) as u16;
    let value_bits = (bytes.len() * 8) as u16;

    ok!(target.store_small_uint(bytes.len() as u8, len_bits));
    ok!(target.store_raw(&bytes, value_bits));

    Ok((len_bits + (value_size as u16) * 8, 0))
}

fn write_simple(
    value: &dyn Store,
    max_bits: u16,
    max_refs: u8,
    target: &mut CellBuilder,
) -> Result<(u16, u8), Error> {
    ok!(value.store_into(target, &mut Cell::default_finalizer()));
    Ok((max_bits, max_refs))
}

fn write_bytes(
    mut data: &[u8],
    version: AbiVersion,
    target: &mut CellBuilder,
) -> Result<(u16, u8), Error> {
    const MAX_BYTES_PER_BUILDER: usize = (MAX_BIT_LEN / 8) as usize;
    let mut len = data.len();

    let mut bytes_per_builder = if version.major == 1 {
        std::cmp::min(MAX_BYTES_PER_BUILDER, len)
    } else {
        match len % MAX_BYTES_PER_BUILDER {
            0 => MAX_BYTES_PER_BUILDER,
            x => x,
        }
    };

    let mut result = CellBuilder::new();
    while len > 0 {
        len -= bytes_per_builder;
        let (head, tail) = data.split_at(len);
        data = head;

        ok!(result.store_raw(tail, (bytes_per_builder * 8) as u16));

        let child = ok!(std::mem::take(&mut result).build());
        ok!(result.store_reference(child));

        bytes_per_builder = std::cmp::min(MAX_BYTES_PER_BUILDER, len);
    }

    ok!(target.store_reference(ok!(result.build())));

    Ok((0, 1))
}

fn write_array(
    value_ty: &AbiType,
    values: &[AbiValue],
    fixed_len: bool,
    version: AbiVersion,
    target: &mut CellBuilder,
) -> Result<(u16, u8), Error> {
    let inline_value = fits_into_dict_leaf(32, value_ty.max_bits());

    let mut dict = RawDict::<32>::new();
    let mut key_builder = CellBuilder::new();
    for (i, value) in values.iter().enumerate() {
        ok!(key_builder.store_u32(i as u32));

        let mut values = Vec::new();
        ok!(value.store_as_parts(version, &mut values));
        let value = ok!(SerializedPart::pack(values, version));
        let value = if inline_value {
            InlineOrRef::Inline(value.as_full_slice())
        } else {
            InlineOrRef::Ref(ok!(value.build()))
        };

        ok!(dict.set(key_builder.as_data_slice(), value));

        ok!(key_builder.rewind(32));
    }

    if !fixed_len {
        ok!(target.store_u32(values.len() as u32));
    }
    ok!(write_simple(&dict, 0, 0, target));

    Ok((1 + if fixed_len { 0 } else { 32 }, 1))
}

fn write_map(
    key_ty: &PlainAbiType,
    value_ty: &AbiType,
    value: &BTreeMap<PlainAbiValue, AbiValue>,
    version: AbiVersion,
    target: &mut CellBuilder,
) -> Result<(u16, u8), Error> {
    let key_bits = key_ty.max_bits();
    let inline_value = fits_into_dict_leaf(key_bits, value_ty.max_bits());

    let mut dict = None::<Cell>;
    let mut key_builder = CellBuilder::new();
    let finalizer = &mut Cell::default_finalizer();
    for (key, value) in value {
        ok!(key.store_into(&mut key_builder, &mut Cell::default_finalizer()));

        let mut values = Vec::new();
        ok!(value.store_as_parts(version, &mut values));
        let value = ok!(SerializedPart::pack(values, version));
        let value = if inline_value {
            InlineOrRef::Inline(value.as_full_slice())
        } else {
            InlineOrRef::Ref(ok!(value.build()))
        };

        let (new_dict, _) = ok!(dict::dict_insert(
            dict.as_ref(),
            &mut key_builder.as_data_slice(),
            key_bits,
            &value,
            dict::SetMode::Set,
            finalizer,
        ));
        dict = new_dict;

        ok!(key_builder.rewind(key_builder.bit_len()));
    }

    ok!(dict.store_into(target, finalizer));

    Ok((1, 1))
}

fn write_optional(
    ty: &AbiType,
    value: Option<&AbiValue>,
    version: AbiVersion,
    target: &mut CellBuilder,
) -> Result<(u16, u8), Error> {
    let (max_ty_bits, max_ty_refs) = ty.max_size();
    let (max_size, inline) = if max_ty_bits < MAX_BIT_LEN as usize && max_ty_refs < MAX_REF_COUNT {
        ((1 + max_ty_bits as u16, max_ty_refs as u8), true)
    } else {
        ((1, 1), false)
    };

    match value {
        Some(value) => {
            let builder = ok!(value.make_builder(version));

            ok!(target.store_bit(true));
            ok!(if inline {
                target.store_builder(&builder)
            } else {
                target.store_reference(ok!(builder.build()))
            })
        }
        None => ok!(target.store_bit(false)),
    }

    Ok(max_size)
}

fn write_ref(
    value: &AbiValue,
    version: AbiVersion,
    target: &mut CellBuilder,
) -> Result<(u16, u8), Error> {
    let cell = ok!(value.make_builder(version).and_then(CellBuilder::build));
    ok!(target.store_reference(cell));
    Ok((0, 1))
}

fn to_signed_bytes_be(is_negative: bool, value: &BigUint) -> Vec<u8> {
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

    fn negative_to_signed_bytes_be(value: &BigUint) -> Vec<u8> {
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

    if is_negative {
        negative_to_signed_bytes_be(value)
    } else {
        value.to_bytes_be()
    }
}

const fn fits_into_dict_leaf(key_bits: u16, value_bits: usize) -> bool {
    // NOTE: Label offset is calculated as 2 bits for tag + max ceil(log2(key_bits)).
    // However this might be incorrect as we have other parts of the label to store.
    const LABEL_OFFSET: usize = 12;

    LABEL_OFFSET + key_bits as usize + value_bits <= MAX_BIT_LEN as usize
}

enum InlineOrRef<'a> {
    Inline(CellSlice<'a>),
    Ref(Cell),
}

impl Store for InlineOrRef<'_> {
    fn store_into(&self, builder: &mut CellBuilder, _: &mut dyn Finalizer) -> Result<(), Error> {
        match self {
            Self::Inline(slice) => builder.store_slice(slice),
            Self::Ref(cell) => builder.store_reference(cell.clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn int_overflow() {
        assert_eq!(
            AbiValue::Uint(16, BigUint::from(u32::MAX)).make_cell(AbiVersion::V2_2),
            Err(Error::IntOverflow)
        );

        assert_eq!(
            AbiValue::Uint(16, BigUint::from(u16::MAX as u32 + 1)).make_cell(AbiVersion::V2_2),
            Err(Error::IntOverflow)
        );
    }
}
