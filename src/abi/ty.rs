use std::borrow::Cow;
use std::num::NonZeroU8;
use std::str::FromStr;

use serde::{Deserialize, Serialize};

use super::error::{ParseAbiTypeError, ParseNamedAbiTypeError};
use crate::cell::{MAX_BIT_LEN, MAX_REF_COUNT};
use crate::models::IntAddr;
use crate::num::Tokens;

/// ABI value type with name.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct NamedAbiType {
    /// Item name.
    pub name: String,
    /// ABI value type.
    pub ty: AbiType,
}

impl NamedAbiType {
    /// Creates a named ABI type.
    pub fn new(name: String, ty: AbiType) -> Self {
        Self { name, ty }
    }

    /// Creates a named ABI type with an index name (e.g. `value123`).
    pub fn from_index(index: usize, ty: AbiType) -> Self {
        Self {
            name: format!("value{index}"),
            ty,
        }
    }
}

impl Serialize for NamedAbiType {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        #[derive(Serialize)]
        struct Helper<'a> {
            name: &'a str,
            #[serde(rename = "type", serialize_with = "collect_str")]
            ty: DisplayAbiTypeSimple<'a>,
            #[serde(skip_serializing_if = "Option::is_none")]
            components: Option<&'a [NamedAbiType]>,
        }

        Helper {
            name: &self.name,
            ty: self.ty.display_simple(),
            components: self.ty.components(),
        }
        .serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for NamedAbiType {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::Error;

        #[derive(Deserialize)]
        struct Helper<'a> {
            name: String,
            #[serde(rename = "type", borrow)]
            ty: Cow<'a, str>,
            #[serde(default)]
            components: Option<Vec<Helper<'a>>>,
        }

        impl TryFrom<Helper<'_>> for NamedAbiType {
            type Error = ParseNamedAbiTypeError;

            fn try_from(value: Helper<'_>) -> Result<Self, Self::Error> {
                let mut ty = ok!(AbiType::from_simple_str(&value.ty).map_err(|error| {
                    ParseNamedAbiTypeError::InvalidType {
                        ty: value.ty.to_string(),
                        error,
                    }
                }));
                match (ty.components_mut(), value.components) {
                    (Some(ty), Some(components)) => {
                        *ty = ok!(components
                            .into_iter()
                            .map(Self::try_from)
                            .collect::<Result<Vec<_>, _>>());
                    }
                    (Some(_), None) => {
                        return Err(ParseNamedAbiTypeError::ExpectedComponents {
                            ty: value.ty.to_string(),
                        })
                    }
                    (None, Some(_)) => {
                        return Err(ParseNamedAbiTypeError::UnexpectedComponents {
                            ty: value.ty.to_string(),
                        });
                    }
                    (None, None) => {}
                }

                Ok(Self {
                    name: value.name,
                    ty,
                })
            }
        }

        let helper = ok!(<Helper as Deserialize>::deserialize(deserializer));
        helper.try_into().map_err(Error::custom)
    }
}

/// Contract header value type.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum AbiHeaderType {
    /// Time header type. Serialized as `uint64`.
    Time,
    /// Expire header type. Serialized as `uint32`.
    Expire,
    /// Public key type. Serialized as `optional(uint256)`.
    PublicKey,
}

impl FromStr for AbiHeaderType {
    type Err = ParseAbiTypeError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "time" => Self::Time,
            "expire" => Self::Expire,
            "pubkey" => Self::PublicKey,
            _ => return Err(ParseAbiTypeError::UnknownType),
        })
    }
}

impl std::fmt::Display for AbiHeaderType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Time => "time",
            Self::Expire => "expire",
            Self::PublicKey => "pubkey",
        })
    }
}

/// ABI value type.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum AbiType {
    /// Unsigned integer of n bits.
    Uint(u16),
    /// Signed integer of n bits.
    Int(u16),
    /// Variable-length unsigned integer of maximum n bytes.
    VarUint(NonZeroU8),
    /// Variable-length signed integer of maximum n bytes.
    VarInt(NonZeroU8),
    /// Boolean.
    Bool,
    /// Tree of cells ([`Cell`]).
    ///
    /// [`Cell`]: crate::cell::Cell
    Cell,
    /// Internal address ([`IntAddr`]).
    ///
    /// [`IntAddr`]: crate::models::message::IntAddr
    Address,
    /// Byte array.
    Bytes,
    /// Byte array of fixed length.
    FixedBytes(usize),
    /// Utf8-encoded string.
    String,
    /// Variable length 120-bit integer ([`Tokens`]).
    ///
    /// [`Tokens`]: crate::num::Tokens
    Token,
    /// Product type.
    Tuple(Vec<NamedAbiType>),
    /// Array of elements of the specified ABI type.
    Array(Box<Self>),
    /// Fixed-length array of elements of the specified ABI type.
    FixedArray(Box<Self>, usize),
    /// Dictionary with the specified key and value ABI types.
    Map(PlainAbiType, Box<Self>),
    /// Optional type.
    Optional(Box<Self>),
    /// Type stored in a new cell.
    Ref(Box<Self>),
}

impl AbiType {
    /// Tries to convert a generic ABI type into a plain ABI type.
    pub fn as_plain(&self) -> Option<PlainAbiType> {
        Some(match self {
            Self::Uint(n) => PlainAbiType::Uint(*n),
            Self::Int(n) => PlainAbiType::Int(*n),
            Self::Bool => PlainAbiType::Bool,
            Self::Address => PlainAbiType::Address,
            _ => return None,
        })
    }

    /// Returns the maximum number of bits that this type can occupy.
    pub fn max_bits(&self) -> usize {
        match self {
            Self::Uint(n) | Self::Int(n) => *n as usize,
            Self::VarUint(n) | Self::VarInt(n) => {
                let rest_bytes: u8 = n.get() - 1;
                (8 - rest_bytes.leading_zeros()) as usize + (rest_bytes as usize * 8)
            }
            Self::Bool | Self::FixedArray(..) | Self::Map(..) => 1,
            Self::Cell | Self::Ref(_) | Self::Bytes | Self::FixedBytes(_) | Self::String => 0,
            Self::Address => IntAddr::BITS_MAX as usize,
            Self::Token => Tokens::MAX_BITS as usize,
            Self::Array(_) => 33,
            Self::Optional(ty) => {
                let max_ty_bits = ty.max_bits();
                if max_ty_bits < MAX_BIT_LEN as usize {
                    let max_ty_refs = ty.max_refs();
                    if max_ty_refs < MAX_REF_COUNT {
                        return 1 + max_ty_bits;
                    }
                }
                1
            }
            Self::Tuple(items) => items.iter().map(|item| item.ty.max_bits()).sum(),
        }
    }

    /// Returns the maximum number of cells that this type can occupy.
    pub fn max_refs(&self) -> usize {
        match self {
            Self::Uint(_)
            | Self::Int(_)
            | Self::VarUint(_)
            | Self::VarInt(_)
            | Self::Bool
            | Self::Address
            | Self::Token => 0,

            Self::Cell
            | Self::Bytes
            | Self::FixedBytes(_)
            | Self::String
            | Self::Array(_)
            | Self::FixedArray(..)
            | Self::Map(..)
            | Self::Ref(_) => 1,

            Self::Optional(ty) => {
                let max_ty_bits = ty.max_bits();
                if max_ty_bits < MAX_BIT_LEN as usize {
                    let max_ty_refs = ty.max_refs();
                    if max_ty_refs < MAX_REF_COUNT {
                        return max_ty_refs;
                    }
                }
                1
            }

            Self::Tuple(items) => items.iter().map(|item| item.ty.max_refs()).sum(),
        }
    }

    fn components(&self) -> Option<&[NamedAbiType]> {
        match self {
            Self::Tuple(types) => Some(types),
            Self::Array(ty) => ty.components(),
            Self::FixedArray(ty, _) => ty.components(),
            Self::Map(_, value_ty) => value_ty.components(),
            Self::Optional(ty) => ty.components(),
            Self::Ref(ty) => ty.components(),
            _ => None,
        }
    }

    fn components_mut(&mut self) -> Option<&mut Vec<NamedAbiType>> {
        match self {
            Self::Tuple(types) => Some(types),
            Self::Array(ty) => ty.components_mut(),
            Self::FixedArray(ty, _) => ty.components_mut(),
            Self::Map(_, value_ty) => value_ty.components_mut(),
            Self::Optional(ty) => ty.components_mut(),
            Self::Ref(ty) => ty.components_mut(),
            _ => None,
        }
    }

    fn from_simple_str(s: &str) -> Result<Self, ParseAbiTypeError> {
        if let Some(arr_ty) = s.strip_suffix(']') {
            let (ty, len) = ok!(arr_ty
                .rsplit_once('[')
                .ok_or(ParseAbiTypeError::InvalidArrayType));

            let len = if len.is_empty() {
                None
            } else {
                Some(ok!(len
                    .parse::<usize>()
                    .map_err(ParseAbiTypeError::InvalidArrayLength)))
            };

            let ty = ok!(Self::from_simple_str(ty).map(Box::new));
            return Ok(match len {
                None => Self::Array(ty),
                Some(len) => Self::FixedArray(ty, len),
            });
        }

        Ok(match s {
            "bool" => Self::Bool,
            "cell" => Self::Cell,
            "address" => Self::Address,
            "bytes" => Self::Bytes,
            "string" => Self::String,
            "gram" | "token" => Self::Token,
            "tuple" => Self::Tuple(Default::default()),
            _ => {
                if let Some(s) = s.strip_prefix("uint") {
                    Self::Uint(ok!(s
                        .parse::<u16>()
                        .map_err(ParseAbiTypeError::InvalidBitLen)))
                } else if let Some(s) = s.strip_prefix("int") {
                    Self::Int(ok!(s
                        .parse::<u16>()
                        .map_err(ParseAbiTypeError::InvalidBitLen)))
                } else if let Some(s) = s.strip_prefix("varuint") {
                    Self::VarUint(ok!(s
                        .parse::<NonZeroU8>()
                        .map_err(ParseAbiTypeError::InvalidByteLen)))
                } else if let Some(s) = s.strip_prefix("varint") {
                    Self::VarInt(ok!(s
                        .parse::<NonZeroU8>()
                        .map_err(ParseAbiTypeError::InvalidByteLen)))
                } else if let Some(s) = s.strip_prefix("fixedbytes") {
                    Self::FixedBytes(ok!(s
                        .parse::<usize>()
                        .map_err(ParseAbiTypeError::InvalidByteLen)))
                } else if let Some(s) = s.strip_prefix("map(") {
                    let s = ok!(s
                        .strip_suffix(')')
                        .ok_or(ParseAbiTypeError::UnterminatedInnerType));
                    let (key_ty, value_ty) = ok!(s
                        .split_once(',')
                        .ok_or(ParseAbiTypeError::ValueTypeNotFound));

                    Self::Map(
                        ok!(PlainAbiType::from_str(key_ty)),
                        ok!(Self::from_simple_str(value_ty).map(Box::new)),
                    )
                } else if let Some(s) = s.strip_prefix("optional(") {
                    let s = ok!(s
                        .strip_suffix(')')
                        .ok_or(ParseAbiTypeError::UnterminatedInnerType));

                    Self::Optional(ok!(Self::from_simple_str(s).map(Box::new)))
                } else if let Some(s) = s.strip_prefix("ref(") {
                    let s = ok!(s
                        .strip_suffix(')')
                        .ok_or(ParseAbiTypeError::UnterminatedInnerType));

                    Self::Ref(ok!(Self::from_simple_str(s).map(Box::new)))
                } else {
                    return Err(ParseAbiTypeError::UnknownType);
                }
            }
        })
    }

    fn display_simple(&self) -> DisplayAbiTypeSimple<'_> {
        DisplayAbiTypeSimple(self)
    }
}

impl std::fmt::Display for AbiType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::Uint(n) => return write!(f, "uint{n}"),
            Self::Int(n) => return write!(f, "int{n}"),
            Self::VarUint(n) => return write!(f, "varuint{n}"),
            Self::VarInt(n) => return write!(f, "varint{n}"),
            Self::Bool => "bool",
            Self::Cell => "cell",
            Self::Address => "address",
            Self::Bytes => "bytes",
            Self::FixedBytes(n) => return write!(f, "fixedbytes{n}"),
            Self::String => "string",
            Self::Token => "gram",
            Self::Tuple(items) => {
                if items.is_empty() {
                    "()"
                } else {
                    let mut first = true;
                    ok!(f.write_str("("));
                    for item in items {
                        if !std::mem::take(&mut first) {
                            ok!(f.write_str(","));
                        }
                        ok!(std::fmt::Display::fmt(&item.ty, f));
                    }
                    ")"
                }
            }
            Self::Array(ty) => return write!(f, "{ty}[]"),
            Self::FixedArray(ty, n) => return write!(f, "{ty}[{n}]"),
            Self::Map(key_ty, value_ty) => return write!(f, "map({key_ty},{value_ty})"),
            Self::Optional(ty) => return write!(f, "optional({ty})"),
            Self::Ref(ty) => return write!(f, "ref({ty})"),
        };
        f.write_str(s)
    }
}

#[derive(Clone, Copy)]
struct DisplayAbiTypeSimple<'a>(&'a AbiType);

impl std::fmt::Display for DisplayAbiTypeSimple<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            AbiType::Tuple(_) => f.write_str("tuple"),
            AbiType::Array(ty) => write!(f, "{}[]", ty.display_simple()),
            AbiType::FixedArray(ty, n) => write!(f, "{}[{n}]", ty.display_simple()),
            AbiType::Map(key_ty, value_ty) => {
                write!(f, "map({key_ty},{})", value_ty.display_simple())
            }
            AbiType::Optional(ty) => write!(f, "optional({})", ty.display_simple()),
            AbiType::Ref(ty) => write!(f, "ref({})", ty.display_simple()),
            ty => std::fmt::Display::fmt(ty, f),
        }
    }
}

/// ABI type which has a fixed bits representation
/// and therefore can be used as a map key.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum PlainAbiType {
    /// Unsigned integer of n bits.
    Uint(u16),
    /// Signed integer of n bits.
    Int(u16),
    /// Boolean.
    Bool,
    /// Internal address ([`IntAddr`]).
    ///
    /// [`IntAddr`]: crate::models::message::IntAddr
    Address,
}

impl From<PlainAbiType> for AbiType {
    fn from(value: PlainAbiType) -> Self {
        match value {
            PlainAbiType::Uint(n) => Self::Uint(n),
            PlainAbiType::Int(n) => Self::Int(n),
            PlainAbiType::Bool => Self::Bool,
            PlainAbiType::Address => Self::Address,
        }
    }
}

impl FromStr for PlainAbiType {
    type Err = ParseAbiTypeError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "bool" => Self::Bool,
            "address" => Self::Address,
            s => {
                if let Some(s) = s.strip_prefix("uint") {
                    Self::Uint(ok!(s
                        .parse::<u16>()
                        .map_err(ParseAbiTypeError::InvalidBitLen)))
                } else if let Some(s) = s.strip_prefix("int") {
                    Self::Int(ok!(s
                        .parse::<u16>()
                        .map_err(ParseAbiTypeError::InvalidBitLen)))
                } else {
                    return Err(ParseAbiTypeError::UnknownType);
                }
            }
        })
    }
}

impl std::fmt::Display for PlainAbiType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::Uint(n) => return write!(f, "uint{n}"),
            Self::Int(n) => return write!(f, "int{n}"),
            Self::Bool => "bool",
            Self::Address => "address",
        };
        f.write_str(s)
    }
}

#[inline]
fn collect_str<T, S>(value: &T, serializer: S) -> Result<S::Ok, S::Error>
where
    T: std::fmt::Display,
    S: serde::ser::Serializer,
{
    serializer.collect_str(value)
}
