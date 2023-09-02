use std::collections::BTreeMap;
use std::num::NonZeroU8;

use bytes::Bytes;
use num_bigint::{BigInt, BigUint};

use crate::abi::{AbiType, AbiValue, AbiVersion, NamedAbiValue, PlainAbiType, PlainAbiValue};
use crate::cell::{Cell, CellSlice, Load, MAX_BIT_LEN, MAX_REF_COUNT};
use crate::dict::{self, RawDict};
use crate::error::Error;
use crate::models::IntAddr;
use crate::num::Tokens;

impl AbiValue {
    /// Loads an ABI value from the specified slice.
    pub fn load_ext(
        ty: &AbiType,
        version: AbiVersion,
        last: bool,
        allow_partial: bool,
        slice: &mut CellSlice,
    ) -> Result<Self, Error> {
        match ty {
            AbiType::Uint(bits) => load_uint(*bits, slice).map(|value| Self::Uint(*bits, value)),
            AbiType::Int(bits) => load_int(*bits, slice).map(|value| Self::Int(*bits, value)),
            AbiType::VarUint(size) => {
                load_varuint(*size, slice).map(|value| Self::VarUint(*size, value))
            }
            AbiType::VarInt(size) => {
                load_varint(*size, slice).map(|value| Self::VarInt(*size, value))
            }
            AbiType::Bool => {
                ok!(preload_bits(1, slice));
                slice.load_bit().map(Self::Bool)
            }
            AbiType::Cell => load_cell(version, last, slice).map(Self::Cell),
            AbiType::Address => {
                ok!(preload_bits(1, slice));
                IntAddr::load_from(slice).map(Box::new).map(Self::Address)
            }
            AbiType::Bytes => load_bytes(version, last, slice).map(Self::Bytes),
            AbiType::FixedBytes(len) => {
                load_fixed_bytes(*len, version, last, slice).map(Self::FixedBytes)
            }
            AbiType::String => load_string(version, last, slice).map(Self::String),
            AbiType::Token => {
                ok!(preload_bits(1, slice));
                Tokens::load_from(slice).map(Self::Token)
            }
            AbiType::Tuple(items) => {
                let items_len = items.len();
                let mut values = Vec::with_capacity(items_len);
                for (i, item) in items.iter().enumerate() {
                    let last = last && i + 1 == items_len;
                    values.push(NamedAbiValue {
                        value: ok!(Self::load_ext(
                            &item.ty,
                            version,
                            last,
                            allow_partial,
                            slice
                        )),
                        name: item.name.clone(),
                    });
                }
                Ok(Self::Tuple(values))
            }
            AbiType::Array(ty) => load_array(ty, version, allow_partial, slice)
                .map(|values| Self::Array(ty.clone(), values)),
            AbiType::FixedArray(ty, len) => {
                load_fixed_array(ty, *len, version, allow_partial, slice)
                    .map(|values| Self::FixedArray(ty.clone(), values))
            }
            AbiType::Map(key_ty, value_ty) => {
                load_map(*key_ty, value_ty, version, allow_partial, slice)
                    .map(|value| Self::Map(*key_ty, value_ty.clone(), value))
            }
            AbiType::Optional(ty) => load_optional(ty, version, last, allow_partial, slice)
                .map(|value| Self::Optional(ty.clone(), value)),
            AbiType::Ref(ty) => load_ref(ty, version, last, allow_partial, slice).map(Self::Ref),
        }
    }
}

impl PlainAbiValue {
    /// Loads a corresponding value from the slice.
    pub fn load(ty: PlainAbiType, slice: &mut CellSlice) -> Result<Self, Error> {
        match ty {
            PlainAbiType::Uint(bits) => {
                load_uint_plain(bits, slice).map(|value| Self::Uint(bits, value))
            }
            PlainAbiType::Int(bits) => {
                load_int_plain(bits, slice).map(|value| Self::Int(bits, value))
            }
            PlainAbiType::Bool => slice.load_bit().map(Self::Bool),
            PlainAbiType::Address => IntAddr::load_from(slice).map(Box::new).map(Self::Address),
        }
    }
}

fn preload_bits(bits: u16, slice: &mut CellSlice) -> Result<(), Error> {
    if bits == 0 {
        return Ok(());
    }

    let remaining_bits = slice.remaining_bits();
    if remaining_bits == 0 {
        // TODO: check for an imcomplete deserialization.
        let first_ref = ok!(slice.load_reference_as_slice());
        *slice = first_ref;
    } else if remaining_bits < bits {
        return Err(Error::CellUnderflow);
    }

    Ok(())
}

fn load_uint(bits: u16, slice: &mut CellSlice) -> Result<BigUint, Error> {
    ok!(preload_bits(bits, slice));
    load_uint_plain(bits, slice)
}

fn load_int(bits: u16, slice: &mut CellSlice) -> Result<BigInt, Error> {
    ok!(preload_bits(bits, slice));
    load_int_plain(bits, slice)
}

fn load_uint_plain(bits: u16, slice: &mut CellSlice) -> Result<BigUint, Error> {
    match bits {
        0 => Ok(BigUint::default()),
        1..=64 => slice.load_uint(bits).map(BigUint::from),
        _ => {
            let rem = bits % 8;
            let mut buffer = [0u8; 33];
            slice.load_raw(&mut buffer, bits).map(|buffer| {
                let mut int = BigUint::from_bytes_be(buffer);
                if rem != 0 {
                    int >>= 8 - rem;
                }
                int
            })
        }
    }
}

fn load_int_plain(bits: u16, slice: &mut CellSlice) -> Result<BigInt, Error> {
    match bits {
        0 => Ok(BigInt::default()),
        1..=64 => slice.load_uint(bits).map(|mut int| {
            if bits < 64 {
                // Clone sign bit into all high bits
                int |= ((int >> (bits - 1)) * u64::MAX) << (bits - 1);
            }
            BigInt::from(int as i64)
        }),
        _ => {
            let rem = bits % 8;
            let mut buffer = [0u8; 33];
            slice.load_raw(&mut buffer, bits).map(|buffer| {
                let mut int = BigInt::from_signed_bytes_be(buffer);
                if rem != 0 {
                    int >>= 8 - rem;
                }
                int
            })
        }
    }
}

fn load_varuint(size: NonZeroU8, slice: &mut CellSlice) -> Result<BigUint, Error> {
    let bytes = ok!(load_varuint_raw(size, slice));
    Ok(BigUint::from_bytes_le(&bytes))
}

fn load_varint(size: NonZeroU8, slice: &mut CellSlice) -> Result<BigInt, Error> {
    // TODO: manually use `twos_complement_le` to prevent useless cloning in `from_signed_bytes_le`
    let bytes = ok!(load_varuint_raw(size, slice));
    Ok(BigInt::from_signed_bytes_le(&bytes))
}

/// Loads a varuint as bytes in LE (!) order.
fn load_varuint_raw(size: NonZeroU8, slice: &mut CellSlice) -> Result<Vec<u8>, Error> {
    let value_size = size.get();

    let len_bits = (8 - value_size.leading_zeros()) as u16;
    ok!(preload_bits(len_bits, slice));

    let value_bytes = ok!(slice.load_small_uint(len_bits)) as usize;
    let value_bits = (value_bytes * 8) as u16;
    ok!(preload_bits(value_bits, slice));

    let mut bytes = vec![0u8; value_bytes];
    ok!(slice.load_raw(&mut bytes, value_bits));

    // NOTE: reverse and use `from_bytes_le` to prevent useless cloning in `from_bytes_be`
    bytes.reverse();
    Ok(bytes)
}

fn load_cell(version: AbiVersion, last: bool, slice: &mut CellSlice) -> Result<Cell, Error> {
    if slice.remaining_refs() == 1
        && (version.major == 1 && slice.cell().reference_count() as usize == MAX_REF_COUNT
            || version.major > 1 && !last && slice.remaining_bits() == 0)
    {
        *slice = ok!(slice.load_reference_as_slice());
    }
    slice.load_reference_cloned()
}

fn load_bytes_raw(
    version: AbiVersion,
    last: bool,
    slice: &mut CellSlice,
) -> Result<Vec<u8>, Error> {
    let cell = ok!(load_cell(version, last, slice));
    let mut cell = cell.as_ref();

    let mut bytes = Vec::new();
    loop {
        if cell.bit_len() % 8 != 0 {
            return Err(Error::InvalidData);
        }
        bytes.extend_from_slice(cell.data());

        match cell.reference(0) {
            Some(child) => cell = child,
            None => break Ok(bytes),
        };
    }
}

fn load_bytes(version: AbiVersion, last: bool, slice: &mut CellSlice) -> Result<Bytes, Error> {
    load_bytes_raw(version, last, slice).map(Bytes::from)
}

fn load_fixed_bytes(
    len: usize,
    version: AbiVersion,
    last: bool,
    slice: &mut CellSlice,
) -> Result<Bytes, Error> {
    let bytes = ok!(load_bytes(version, last, slice));
    if bytes.len() == len {
        Ok(bytes)
    } else {
        Err(Error::InvalidData)
    }
}

fn load_string(version: AbiVersion, last: bool, slice: &mut CellSlice) -> Result<String, Error> {
    let bytes = ok!(load_bytes_raw(version, last, slice));
    String::from_utf8(bytes).map_err(|_| Error::InvalidData)
}

fn load_array_raw(
    ty: &AbiType,
    len: usize,
    version: AbiVersion,
    allow_partial: bool,
    slice: &mut CellSlice,
) -> Result<Vec<AbiValue>, Error> {
    ok!(preload_bits(1, slice));
    let dict = ok!(RawDict::<32>::load_from(slice));

    let mut result = Vec::with_capacity(len);
    for value in dict.values().take(len) {
        let slice = &mut ok!(value);
        let value = ok!(AbiValue::load_ext(ty, version, true, allow_partial, slice));
        result.push(value);

        // TODO: check full decode
    }

    Ok(result)
}

fn load_array(
    ty: &AbiType,
    version: AbiVersion,
    allow_partial: bool,
    slice: &mut CellSlice,
) -> Result<Vec<AbiValue>, Error> {
    ok!(preload_bits(32, slice));
    let len = ok!(slice.load_u32());
    load_array_raw(ty, len as usize, version, allow_partial, slice)
}

fn load_fixed_array(
    ty: &AbiType,
    len: usize,
    version: AbiVersion,
    allow_partial: bool,
    slice: &mut CellSlice,
) -> Result<Vec<AbiValue>, Error> {
    let values = ok!(load_array_raw(ty, len, version, allow_partial, slice));
    if values.len() == len {
        Ok(values)
    } else {
        Err(Error::InvalidData)
    }
}

fn load_map(
    key_ty: PlainAbiType,
    value_ty: &AbiType,
    version: AbiVersion,
    allow_partial: bool,
    slice: &mut CellSlice,
) -> Result<BTreeMap<PlainAbiValue, AbiValue>, Error> {
    ok!(preload_bits(1, slice));

    let key_bits = key_ty.max_bits();
    let dict = ok!(Option::<Cell>::load_from(slice));

    let mut result = BTreeMap::new();
    for entry in dict::RawIter::new(&dict, key_bits) {
        let (key, mut slice) = ok!(entry);
        let key = ok!(PlainAbiValue::load(key_ty, &mut key.as_data_slice()));
        let value = ok!(AbiValue::load_ext(
            value_ty,
            version,
            true,
            allow_partial,
            &mut slice
        ));
        result.insert(key, value);
    }

    Ok(result)
}

fn load_optional(
    ty: &AbiType,
    version: AbiVersion,
    last: bool,
    allow_partial: bool,
    slice: &mut CellSlice,
) -> Result<Option<Box<AbiValue>>, Error> {
    ok!(preload_bits(1, slice));

    if !ok!(slice.load_bit()) {
        return Ok(None);
    }

    let (max_ty_bits, max_ty_refs) = ty.max_size();
    if max_ty_bits < MAX_BIT_LEN as usize && max_ty_refs < MAX_REF_COUNT {
        let cell = ok!(load_cell(version, last, slice));
        let slice = &mut ok!(cell.as_slice());
        let value = ok!(AbiValue::load_ext(ty, version, true, allow_partial, slice));
        // TODO: check full decode
        Ok(Some(Box::new(value)))
    } else {
        let value = ok!(AbiValue::load_ext(ty, version, last, allow_partial, slice));
        Ok(Some(Box::new(value)))
    }
}

fn load_ref(
    ty: &AbiType,
    version: AbiVersion,
    last: bool,
    allow_partial: bool,
    slice: &mut CellSlice,
) -> Result<Box<AbiValue>, Error> {
    let cell = ok!(load_cell(version, last, slice));
    let slice = &mut ok!(cell.as_slice());
    let value = ok!(AbiValue::load_ext(ty, version, true, allow_partial, slice));
    // TODO: check full decode
    Ok(Box::new(value))
}
