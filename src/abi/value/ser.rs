use std::collections::BTreeMap;
use std::num::NonZeroU8;

use num_bigint::{BigUint, Sign};

use crate::abi::{AbiType, AbiValue, AbiVersion, NamedAbiValue, PlainAbiType, PlainAbiValue};
use crate::cell::{
    Cell, CellBuilder, CellSlice, DefaultFinalizer, Finalizer, Store, MAX_BIT_LEN, MAX_REF_COUNT,
};
use crate::dict::{self, RawDict};
use crate::error::Error;
use crate::models::IntAddr;
use crate::num::Tokens;

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
            ok!(target.store_raw(right, (right.len() * 8) as u16));
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

    let mut bytes_per_builder = if version.major > 1 {
        match len % MAX_BYTES_PER_BUILDER {
            0 => MAX_BYTES_PER_BUILDER,
            x => x,
        }
    } else {
        std::cmp::min(MAX_BYTES_PER_BUILDER, len)
    };

    let mut result = CellBuilder::new();
    while len > 0 {
        len -= bytes_per_builder;
        let (head, tail) = data.split_at(len);
        data = head;

        if result.bit_len() > 0 {
            let child = ok!(std::mem::take(&mut result).build());
            ok!(result.store_reference(child));
        }

        ok!(result.store_raw(tail, (bytes_per_builder * 8) as u16));

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
    let key_bits = key_ty.key_bits();
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

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use bytes::Bytes;

    use crate::dict::Dict;
    use crate::models::{StdAddr, VarAddr};
    use crate::num::Uint9;
    use crate::prelude::{CellFamily, HashBytes};

    use super::*;

    const VX_X: [AbiVersion; 5] = [
        AbiVersion::V1_0,
        AbiVersion::V2_0,
        AbiVersion::V2_1,
        AbiVersion::V2_2,
        AbiVersion::V2_3,
    ];
    const V2_X: [AbiVersion; 4] = [
        AbiVersion::V2_0,
        AbiVersion::V2_1,
        AbiVersion::V2_2,
        AbiVersion::V2_3,
    ];

    fn check_encoding(version: AbiVersion, value: AbiValue) {
        let cell = value.make_cell(version).unwrap();
        let parsed =
            AbiValue::load(&value.get_type(), version, &mut cell.as_slice().unwrap()).unwrap();
        assert_eq!(value, parsed);
    }

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

    #[test]
    fn encode_int() {
        macro_rules! define_tests {
            ($v:ident, { $($abi:ident($bits:literal) => [$($expr:expr),*$(,)?]),*$(,)? }) => {$(
                $(check_encoding($v, AbiValue::$abi($bits, $expr));)*
            )*};
        }

        for v in VX_X {
            println!("ABIv{v}");
            define_tests!(v, {
                uint(8) => [0u8, 123u8, u8::MAX],
                uint(16) => [0u16, 1234u16, u16::MAX],
                uint(32) => [0u32, 123456u32, u32::MAX],
                uint(64) => [0u64, 123456789u64, u64::MAX],
                uint(128) => [0u128, 123456789123123123123u128, u128::MAX],

                int(8) => [0i8, 123i8, i8::MIN, i8::MAX],
                int(16) => [0i16, 1234i16, i16::MIN, i16::MAX],
                int(32) => [0i32, 123456i32, i32::MIN, i32::MAX],
                int(64) => [0i64, 123456789i64, i64::MIN, i64::MAX],
                int(128) => [0i128, 123456789123123123123i128, i128::MIN, i128::MAX],
            });
        }
    }

    #[test]
    fn encode_varint() {
        for v in V2_X {
            println!("ABIv{v}");
            check_encoding(v, AbiValue::varuint(4, 0u32));
            check_encoding(v, AbiValue::varuint(4, u32::MAX >> 8));
            check_encoding(v, AbiValue::varuint(4, 123321u32));

            check_encoding(v, AbiValue::varuint(8, 0u32));
            check_encoding(v, AbiValue::varuint(8, u64::MAX >> 8));
            check_encoding(v, AbiValue::varuint(8, 1233213213123123u64));

            check_encoding(v, AbiValue::varuint(16, 0u8));
            check_encoding(v, AbiValue::Token(Tokens::ZERO));

            let mut prev_value = 0;
            for byte in 0..15 {
                let value = (0xffu128 << (byte * 8)) | prev_value;
                prev_value = value;
                check_encoding(v, AbiValue::varuint(16, value));
                check_encoding(v, AbiValue::Token(Tokens::new(value)));
            }

            check_encoding(v, AbiValue::varuint(128, 0u8));
            check_encoding(v, AbiValue::varuint(128, BigUint::from(1u8) << (126 * 8)));
        }
    }

    #[test]
    fn encode_bool() {
        for v in VX_X {
            println!("ABIv{v}");
            check_encoding(v, AbiValue::Bool(false));
            check_encoding(v, AbiValue::Bool(true));
        }
    }

    #[test]
    fn encode_cell() {
        // Simple cases
        for v in VX_X {
            check_encoding(v, AbiValue::Cell(Cell::empty_cell()));
        }

        // Complex case
        let value = AbiValue::unnamed_tuple([
            AbiValue::Cell(Cell::empty_cell()),
            AbiValue::Cell(Cell::empty_cell()),
            AbiValue::Cell(Cell::empty_cell()),
            AbiValue::Cell(Cell::empty_cell()),
        ]);

        // ABI v1
        let cell_v1 = {
            let mut builder = CellBuilder::new();
            builder.store_reference(Cell::empty_cell()).unwrap();
            builder.store_reference(Cell::empty_cell()).unwrap();
            builder.store_reference(Cell::empty_cell()).unwrap();
            builder
                .store_reference(CellBuilder::build_from(Cell::empty_cell()).unwrap())
                .unwrap();
            builder.build().unwrap()
        };

        assert_eq!(value.make_cell(AbiVersion::V1_0).unwrap(), cell_v1);

        // ABI v2.x
        let cell_v2 = CellBuilder::build_from((
            Cell::empty_cell(),
            Cell::empty_cell(),
            Cell::empty_cell(),
            Cell::empty_cell(),
        ))
        .unwrap();

        for v in V2_X {
            println!("ABIv{v}");
            assert_eq!(value.make_cell(v).unwrap(), cell_v2);
        }
    }

    #[test]
    fn encode_address() {
        for v in VX_X {
            check_encoding(v, AbiValue::address(StdAddr::new(0, HashBytes([0xff; 32]))));
            check_encoding(
                v,
                AbiValue::address(VarAddr {
                    address_len: Uint9::new(10 * 8),
                    anycast: None,
                    workchain: 123456,
                    address: vec![0xffu8; 10],
                }),
            );
        }
    }

    #[test]
    fn encode_bytes() {
        let mut bytes = vec![0xffu8; 256];
        bytes[0] = 0xff; // mark start
        let bytes = Bytes::from(bytes);

        let empty_bytes_cell = {
            let mut builder = CellBuilder::new();
            builder.store_reference(Cell::empty_cell()).unwrap();
            builder.build().unwrap()
        };

        // Check simple encoding
        for v in VX_X {
            println!("ABIv{v}");

            check_encoding(v, AbiValue::Bytes(bytes.clone()));

            // Bytes must have the same encoding as fixedbytes
            assert_eq!(
                AbiValue::Bytes(bytes.clone()).make_cell(v),
                AbiValue::FixedBytes(bytes.clone()).make_cell(v)
            );

            assert_eq!(
                AbiValue::Bytes(Bytes::new()).make_cell(v).unwrap(),
                empty_bytes_cell
            );
        }

        // ABI v1
        let cell_v1 = CellBuilder::build_from({
            let mut builder = CellBuilder::new();
            builder.store_raw(&[0xff; 2], 2 * 8).unwrap();

            builder
                .store_reference({
                    let mut builder = CellBuilder::new();
                    builder.store_raw(&[0xff; 127], 127 * 8).unwrap();

                    builder
                        .store_reference({
                            let mut builder = CellBuilder::new();
                            builder.store_raw(&[0xff; 127], 127 * 8).unwrap();
                            builder.build().unwrap()
                        })
                        .unwrap();

                    builder.build().unwrap()
                })
                .unwrap();

            builder.build().unwrap()
        })
        .unwrap();

        // ABI v2
        let cell_v2 = CellBuilder::build_from({
            let mut builder = CellBuilder::new();
            builder.store_raw(&[0xff; 127], 127 * 8).unwrap();

            builder
                .store_reference({
                    let mut builder = CellBuilder::new();
                    builder.store_raw(&[0xff; 127], 127 * 8).unwrap();

                    builder
                        .store_reference({
                            let mut builder = CellBuilder::new();
                            builder.store_raw(&[0xff; 2], 2 * 8).unwrap();
                            builder.build().unwrap()
                        })
                        .unwrap();

                    builder.build().unwrap()
                })
                .unwrap();

            builder.build().unwrap()
        })
        .unwrap();

        //

        assert_eq!(
            AbiValue::Bytes(bytes.clone())
                .make_cell(AbiVersion::V1_0)
                .unwrap(),
            cell_v1
        );

        for v in V2_X {
            println!("ABIv{v}");

            assert_eq!(
                AbiValue::Bytes(bytes.clone()).make_cell(v).unwrap(),
                cell_v2
            );
        }
    }

    #[test]
    fn encode_string() {
        for v in VX_X {
            println!("ABIv{v}");
            check_encoding(v, AbiValue::String(String::new()));
            check_encoding(v, AbiValue::String("Hello".to_owned()));
            check_encoding(
                v,
                AbiValue::String(
                    std::iter::repeat_with(|| "HELLO".to_owned())
                        .take(200)
                        .collect::<Vec<String>>()
                        .join(" "),
                ),
            );
        }
    }

    #[test]
    fn encode_nested_simple_tuple() {
        let value = AbiValue::unnamed_tuple([
            AbiValue::uint(32, 0u32),
            AbiValue::Cell(Cell::empty_cell()),
            AbiValue::Bool(false),
            AbiValue::unnamed_tuple([
                AbiValue::int(8, -15),
                AbiValue::int(16, -9845),
                AbiValue::unnamed_tuple([
                    AbiValue::int(32, -1),
                    AbiValue::int(64, 12345678),
                    AbiValue::int(128, -12345678),
                ]),
            ]),
            AbiValue::unnamed_tuple([
                AbiValue::uint(8, 255_u8),
                AbiValue::uint(16, 0_u16),
                AbiValue::unnamed_tuple([
                    AbiValue::uint(32, 256_u32),
                    AbiValue::uint(64, 123_u64),
                    AbiValue::uint(128, 1234567890_u128),
                ]),
            ]),
        ]);

        for v in VX_X {
            println!("ABIv{v}");

            let cell = value.make_cell(v).unwrap();
            assert_eq!(
                cell.bit_len(),
                32 + 1 + 8 + 16 + 32 + 64 + 128 + 8 + 16 + 32 + 64 + 128
            );
            assert_eq!(cell.reference_count(), 1);

            check_encoding(v, value.clone());
        }
    }

    #[test]
    fn encode_tuple_four_refs_and_four_uint256() {
        let bytes = HashBytes([0xff; 32]);
        let bytes_cell = CellBuilder::build_from(bytes).unwrap();

        let cell = {
            let mut builder = CellBuilder::new();
            builder.store_u32(0).unwrap();
            builder.store_reference(Cell::empty_cell()).unwrap();

            builder.store_reference(bytes_cell.clone()).unwrap();
            builder.store_reference(bytes_cell.clone()).unwrap();

            let mut second_builder = CellBuilder::new();
            second_builder.store_reference(bytes_cell.clone()).unwrap();
            second_builder.store_u256(&bytes).unwrap();
            second_builder.store_u256(&bytes).unwrap();
            second_builder.store_u256(&bytes).unwrap();

            let mut third_builder = CellBuilder::new();
            third_builder.store_u256(&bytes).unwrap();

            second_builder
                .store_reference(third_builder.build().unwrap())
                .unwrap();
            builder
                .store_reference(second_builder.build().unwrap())
                .unwrap();

            builder.build().unwrap()
        };

        let value = AbiValue::unnamed_tuple([
            AbiValue::uint(32, 0_u32),
            AbiValue::Cell(Cell::empty_cell()),
            AbiValue::Cell(bytes_cell.clone()),
            AbiValue::Bytes(Bytes::copy_from_slice(bytes.as_slice())),
            AbiValue::Cell(bytes_cell),
            AbiValue::uint(256, BigUint::from_bytes_be(bytes.as_slice())),
            AbiValue::uint(256, BigUint::from_bytes_be(bytes.as_slice())),
            AbiValue::uint(256, BigUint::from_bytes_be(bytes.as_slice())),
            AbiValue::uint(256, BigUint::from_bytes_be(bytes.as_slice())),
        ]);

        for v in VX_X {
            println!("ABIv{v}");

            assert_eq!(value.make_cell(v).unwrap(), cell);
            check_encoding(v, value.clone());
        }
    }

    #[test]
    fn encode_tuple_four_refs_and_one_uint256() {
        let bytes = HashBytes([0x55; 32]);
        let bytes_cell = CellBuilder::build_from(bytes).unwrap();

        let mut builder = CellBuilder::new();
        builder.store_u32(0).unwrap();
        builder.store_reference(Cell::empty_cell()).unwrap();

        builder.store_reference(bytes_cell.clone()).unwrap();
        builder.store_reference(bytes_cell.clone()).unwrap();

        let cell_v2 = {
            let mut builder = builder.clone();
            builder.store_reference(bytes_cell.clone()).unwrap();
            builder.store_u256(&bytes).unwrap();
            builder.build().unwrap()
        };

        let cell_v1 = {
            let mut child_builder = CellBuilder::new();
            child_builder.store_reference(bytes_cell.clone()).unwrap();
            child_builder.store_u256(&bytes).unwrap();

            builder
                .store_reference(child_builder.build().unwrap())
                .unwrap();
            builder.build().unwrap()
        };

        let value = AbiValue::unnamed_tuple([
            AbiValue::uint(32, 0_u32),
            AbiValue::Cell(Cell::empty_cell()),
            AbiValue::Cell(bytes_cell.clone()),
            AbiValue::Bytes(Bytes::copy_from_slice(bytes.as_slice())),
            AbiValue::Cell(bytes_cell.clone()),
            AbiValue::uint(256, BigUint::from_bytes_be(bytes.as_slice())),
        ]);

        for v in VX_X {
            println!("ABIv{v}");
            check_encoding(v, value.clone());
        }

        assert_eq!(value.make_cell(AbiVersion::V1_0).unwrap(), cell_v1);

        for v in V2_X {
            println!("ABIv{v}");
            assert_eq!(value.make_cell(v).unwrap(), cell_v2);
        }
    }

    #[test]
    fn encode_map_simple() {
        let bytes = HashBytes([0x55; 32]);
        let bytes_cell = CellBuilder::build_from(bytes).unwrap();

        let mut bytes_map = Dict::<u8, Cell>::new();
        for i in 1..=3 {
            bytes_map.set(i, bytes_cell.clone()).unwrap();
        }
        let bytes_map_cell = CellBuilder::build_from(bytes_map).unwrap();
        let bytes_map_value = AbiValue::map([
            (1u8, Bytes::copy_from_slice(bytes.as_slice())),
            (2, Bytes::copy_from_slice(bytes.as_slice())),
            (3, Bytes::copy_from_slice(bytes.as_slice())),
        ]);

        for v in VX_X {
            println!("ABIv{v}");

            assert_eq!(bytes_map_value.make_cell(v).unwrap(), bytes_map_cell);
            check_encoding(v, bytes_map_value.clone());
        }

        //
        let mut int_map = Dict::<i16, i128>::new();
        for i in -1..=1 {
            int_map.set(i, i as i128).unwrap();
        }
        let int_map_cell = CellBuilder::build_from(int_map).unwrap();
        let int_map_value = AbiValue::map([(-1i16, -1i128), (0, 0), (1, 1)]);

        for v in VX_X {
            println!("ABIv{v}");

            assert_eq!(int_map_value.make_cell(v).unwrap(), int_map_cell);
            check_encoding(v, int_map_value.clone());
        }

        //
        let mut tuples_map = Dict::<u128, (u32, bool)>::new();
        for i in 1..=5 {
            tuples_map.set(i as u128, (i, i % 2 != 0)).unwrap();
        }
        let tuples_map_cell = CellBuilder::build_from(tuples_map).unwrap();
        let tuples_map_value = AbiValue::map([
            (1u128, (1u32, true)),
            (2, (2, false)),
            (3, (3, true)),
            (4, (4, false)),
            (5, (5, true)),
        ]);

        for v in VX_X {
            println!("ABIv{v}");

            assert_eq!(tuples_map_value.make_cell(v).unwrap(), tuples_map_cell);
            check_encoding(v, tuples_map_value.clone());
        }

        //
        let addr1 = StdAddr::new(0, HashBytes([0x11; 32]));
        let addr2 = StdAddr::new(0, HashBytes([0x22; 32]));

        let mut addr_map = Dict::<StdAddr, u32>::new();
        addr_map.set(&addr1, 123).unwrap();
        addr_map.set(&addr2, 456).unwrap();
        let addr_map_cell = CellBuilder::build_from(addr_map).unwrap();
        let addr_map_value = AbiValue::map([(addr1, 123u32), (addr2, 456)]);

        for v in VX_X {
            println!("ABIv{v}");

            assert_eq!(addr_map_value.make_cell(v).unwrap(), addr_map_cell);
            check_encoding(v, addr_map_value.clone());
        }
    }

    #[test]
    fn encode_map_big_value() {
        //
        let tuple_value = AbiValue::unnamed_tuple([
            AbiValue::uint(256, 1_u32),
            AbiValue::uint(256, 2_u32),
            AbiValue::uint(256, 3_u32),
            AbiValue::uint(256, 4_u32),
        ]);

        //
        let mut map_value = CellBuilder::new();
        map_value.store_u128(0).unwrap();
        map_value.store_u128(1).unwrap();
        map_value.store_u128(0).unwrap();
        map_value.store_u128(2).unwrap();
        map_value.store_u128(0).unwrap();
        map_value.store_u128(3).unwrap();
        map_value
            .store_reference(CellBuilder::build_from((0u128, 4u128)).unwrap())
            .unwrap();
        let map_value = map_value.build().unwrap();

        let mut key = CellBuilder::new();
        key.store_u128(0).unwrap();
        key.store_u128(123).unwrap();

        let mut map = RawDict::<256>::new();
        map.set(key.as_data_slice(), &map_value).unwrap();
        let map_cell = CellBuilder::build_from(map).unwrap();
        let map = AbiValue::Map(
            PlainAbiType::Uint(256),
            Arc::new(tuple_value.get_type()),
            BTreeMap::from([(
                PlainAbiValue::Uint(256, BigUint::from(123u32)),
                tuple_value.clone(),
            )]),
        );

        for v in VX_X {
            println!("ABIv{v}");
            assert_eq!(map.make_cell(v).unwrap(), map_cell);
            check_encoding(v, map.clone());
        }

        //
        let mut key = CellBuilder::new();
        key.store_u32(0).unwrap();

        let mut array = RawDict::<32>::new();
        array.set(key.as_data_slice(), &map_value).unwrap();
        let array_cell = CellBuilder::build_from((1u32, array)).unwrap();
        let array = AbiValue::Array(Arc::new(tuple_value.get_type()), vec![tuple_value]);

        for v in V2_X {
            println!("ABIv{v}");
            assert_eq!(array.make_cell(v).unwrap(), array_cell);
            check_encoding(v, array.clone());
        }
    }

    #[test]
    fn encode_optional() {
        const STR: &str = "Some string";

        let string_cell = {
            let mut builder = CellBuilder::new();
            builder
                .store_raw(STR.as_bytes(), (STR.len() * 8) as u16)
                .unwrap();
            builder.build().unwrap()
        };
        let string_value = AbiValue::String(STR.to_owned());

        let tuple_value = AbiValue::unnamed_tuple([
            string_value.clone(),
            string_value.clone(),
            string_value.clone(),
            string_value.clone(),
        ]);

        let value = AbiValue::unnamed_tuple([
            AbiValue::uint(32, 0u32),
            AbiValue::Cell(Cell::empty_cell()),
            AbiValue::varint(16, -123),
            AbiValue::varuint(32, 456u32),
            AbiValue::optional(None::<bool>),
            AbiValue::Optional(
                Arc::new(AbiType::Uint(1022)),
                Some(Box::new(AbiValue::uint(1022, 1u32))),
            ),
            AbiValue::Optional(
                Arc::new(AbiType::varuint(128)),
                Some(Box::new(AbiValue::varuint(128, 123u32))),
            ),
            AbiValue::Optional(
                Arc::new(tuple_value.get_type()),
                Some(Box::new(tuple_value)),
            ),
        ]);

        let cell = {
            let mut builder = CellBuilder::new();
            builder.store_u32(0).unwrap();
            builder.store_reference(Cell::empty_cell()).unwrap();

            builder.store_small_uint(1, 4).unwrap();
            builder.store_u8(-123i8 as _).unwrap();

            builder.store_small_uint(2, 5).unwrap();
            builder.store_u16(456).unwrap();

            builder.store_bit_zero().unwrap();

            builder
                .store_reference({
                    let mut builder = CellBuilder::new();
                    builder.store_bit_one().unwrap();
                    builder.store_zeros(127 * 8).unwrap();
                    builder.store_small_uint(1, 6).unwrap();

                    builder
                        .store_reference({
                            let mut builder = CellBuilder::new();
                            builder.store_bit_one().unwrap();
                            builder
                                .store_reference({
                                    let mut builder = CellBuilder::new();
                                    builder.store_small_uint(1, 7).unwrap();
                                    builder.store_u8(123).unwrap();
                                    builder.build().unwrap()
                                })
                                .unwrap();

                            builder.store_bit_one().unwrap();
                            builder
                                .store_reference(
                                    CellBuilder::build_from((
                                        string_cell.clone(),
                                        string_cell.clone(),
                                        string_cell.clone(),
                                        string_cell.clone(),
                                    ))
                                    .unwrap(),
                                )
                                .unwrap();

                            builder.build().unwrap()
                        })
                        .unwrap();

                    builder.build().unwrap()
                })
                .unwrap();

            builder.build().unwrap()
        };

        for v in V2_X {
            println!("ABIv{v}");

            assert_eq!(value.make_cell(v).unwrap(), cell);
            check_encoding(v, value.clone());
        }
    }

    #[test]
    fn encode_ref() {
        let cell = CellBuilder::build_from((
            CellBuilder::build_from(123u64).unwrap(),
            CellBuilder::build_from((true, Cell::empty_cell())).unwrap(),
        ))
        .unwrap();

        let value = AbiValue::unnamed_tuple([
            AbiValue::reference(123u64),
            AbiValue::reference((true, Cell::empty_cell())),
        ]);

        for v in V2_X {
            println!("ABIv{v}");
            assert_eq!(value.make_cell(v).unwrap(), cell);
            check_encoding(v, value.clone());
        }
    }
}
