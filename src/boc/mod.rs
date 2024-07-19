//! BOC (Bag Of Cells) implementation.

use crate::cell::{Cell, CellBuilder, CellContext, CellFamily, DynCell, HashBytes, Load, Store};

/// BOC decoder implementation.
pub mod de;
/// BOC encoder implementation.
pub mod ser;

#[cfg(test)]
mod tests;

/// BOC file magic number.
#[derive(Default, Copy, Clone, Eq, PartialEq)]
pub enum BocTag {
    /// Single root, cells index, no CRC32.
    Indexed,
    /// Single root, cells index, with CRC32.
    IndexedCrc32,
    /// Multiple roots, optional cells index, optional CRC32.
    #[default]
    Generic,
}

impl BocTag {
    const INDEXED: [u8; 4] = [0x68, 0xff, 0x65, 0xf3];
    const INDEXED_CRC32: [u8; 4] = [0xac, 0xc3, 0xa7, 0x28];
    const GENERIC: [u8; 4] = [0xb5, 0xee, 0x9c, 0x72];

    /// Tries to match bytes with BOC tag.
    pub const fn from_bytes(data: [u8; 4]) -> Option<Self> {
        match data {
            Self::GENERIC => Some(Self::Generic),
            Self::INDEXED_CRC32 => Some(Self::IndexedCrc32),
            Self::INDEXED => Some(Self::Indexed),
            _ => None,
        }
    }

    /// Converts BOC tag to bytes.
    pub const fn to_bytes(self) -> [u8; 4] {
        match self {
            Self::Indexed => Self::INDEXED,
            Self::IndexedCrc32 => Self::INDEXED_CRC32,
            Self::Generic => Self::GENERIC,
        }
    }
}

/// A serde helper to use [`Boc`] inside [`Option`].
#[cfg(feature = "serde")]
pub struct OptionBoc;

#[cfg(feature = "serde")]
impl OptionBoc {
    /// Serializes an optional cell into an encoded BOC
    /// (as base64 for human readable serializers).
    pub fn serialize<S, T>(cell: &Option<T>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
        T: AsRef<DynCell>,
    {
        match cell {
            Some(cell) => serializer.serialize_some(cell.as_ref()),
            None => serializer.serialize_none(),
        }
    }

    /// Deserializes an optional cell from an encoded BOC
    /// (from base64 for human readable deserializers).
    pub fn deserialize<'de, D>(deserializer: D) -> Result<Option<Cell>, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::Deserialize;

        #[derive(Deserialize)]
        #[repr(transparent)]
        struct Wrapper(#[serde(with = "Boc")] Cell);

        Ok(ok!(Option::<Wrapper>::deserialize(deserializer)).map(|Wrapper(cell)| cell))
    }
}

/// BOC (Bag Of Cells) helper.
pub struct Boc;

impl Boc {
    /// Computes a simple SHA256 hash of the data.
    #[inline]
    pub fn file_hash(data: impl AsRef<[u8]>) -> HashBytes {
        use sha2::Digest;

        sha2::Sha256::digest(data).into()
    }

    /// Computes a Blake3 hash of the data.
    #[cfg(feature = "blake3")]
    #[inline]
    pub fn file_hash_blake(data: impl AsRef<[u8]>) -> HashBytes {
        #[cfg(not(feature = "rayon"))]
        {
            blake3::hash(data.as_ref()).into()
        }

        #[cfg(feature = "rayon")]
        {
            // Use Rayon for parallel hashing if data is larger than 256 KB.
            const RAYON_THRESHOLD: usize = 256 * 1024;

            let data = data.as_ref();
            if data.len() < RAYON_THRESHOLD {
                blake3::hash(data)
            } else {
                blake3::Hasher::new().update_rayon(data).finalize()
            }
            .into()
        }
    }

    /// Encodes the specified cell tree as BOC and
    /// returns the `base64` encoded bytes as a string.
    #[cfg(any(feature = "base64", test))]
    pub fn encode_base64<T>(cell: T) -> String
    where
        T: AsRef<DynCell>,
    {
        crate::util::encode_base64(Self::encode(cell))
    }

    /// Encodes the specified cell tree as BOC and
    /// returns the `base64` encoded bytes as a string.
    ///
    /// Uses `rayon` under the hood to parallelize encoding.
    #[cfg(all(any(feature = "base64", test), feature = "rayon"))]
    pub fn encode_base64_rayon<T>(cell: T) -> String
    where
        T: AsRef<DynCell>,
    {
        crate::util::encode_base64(Self::encode_rayon(cell))
    }

    /// Encodes the specified cell tree as BOC.
    pub fn encode<T>(cell: T) -> Vec<u8>
    where
        T: AsRef<DynCell>,
    {
        fn encode_impl(cell: &DynCell) -> Vec<u8> {
            let mut result = Vec::new();
            ser::BocHeader::<ahash::RandomState>::with_root(cell).encode(&mut result);
            result
        }
        encode_impl(cell.as_ref())
    }

    /// Encodes the specified cell tree as BOC.
    ///
    /// Uses `rayon` under the hood to parallelize encoding.
    #[cfg(feature = "rayon")]
    pub fn encode_rayon<T>(cell: T) -> Vec<u8>
    where
        T: AsRef<DynCell>,
    {
        fn encode_impl(cell: &DynCell) -> Vec<u8> {
            let mut result = Vec::new();
            ser::BocHeader::<ahash::RandomState>::with_root(cell).encode_rayon(&mut result);
            result
        }
        encode_impl(cell.as_ref())
    }

    /// Encodes a pair of cell trees as BOC.
    pub fn encode_pair<T1, T2>((cell1, cell2): (T1, T2)) -> Vec<u8>
    where
        T1: AsRef<DynCell>,
        T2: AsRef<DynCell>,
    {
        fn encode_pair_impl(cell1: &DynCell, cell2: &DynCell) -> Vec<u8> {
            let mut result = Vec::new();
            let mut encoder = ser::BocHeader::<ahash::RandomState>::with_root(cell1);
            encoder.add_root(cell2);
            encoder.encode(&mut result);
            result
        }
        encode_pair_impl(cell1.as_ref(), cell2.as_ref())
    }

    /// Decodes a `base64` encoded BOC into a cell tree
    /// using an empty cell context.
    #[cfg(any(feature = "base64", test))]
    #[inline]
    pub fn decode_base64<T: AsRef<[u8]>>(data: T) -> Result<Cell, de::Error> {
        fn decode_base64_impl(data: &[u8]) -> Result<Cell, de::Error> {
            match crate::util::decode_base64(data) {
                Ok(data) => Boc::decode_ext(data.as_slice(), &mut Cell::empty_context()),
                Err(_) => Err(de::Error::UnknownBocTag),
            }
        }
        decode_base64_impl(data.as_ref())
    }

    /// Decodes a cell tree using an empty cell context.
    #[inline]
    pub fn decode<T>(data: T) -> Result<Cell, de::Error>
    where
        T: AsRef<[u8]>,
    {
        fn decode_impl(data: &[u8]) -> Result<Cell, de::Error> {
            Boc::decode_ext(data, &mut Cell::empty_context())
        }
        decode_impl(data.as_ref())
    }

    /// Decodes a pair of cell trees using an empty cell context.
    #[inline]
    pub fn decode_pair<T>(data: T) -> Result<(Cell, Cell), de::Error>
    where
        T: AsRef<[u8]>,
    {
        fn decode_pair_impl(data: &[u8]) -> Result<(Cell, Cell), de::Error> {
            Boc::decode_pair_ext(data, &mut Cell::empty_context())
        }
        decode_pair_impl(data.as_ref())
    }

    /// Decodes a cell tree using the specified cell context.
    pub fn decode_ext(data: &[u8], context: &mut dyn CellContext) -> Result<Cell, de::Error> {
        use self::de::*;

        let header = ok!(de::BocHeader::decode(
            data,
            &Options {
                max_roots: Some(1),
                min_roots: Some(1),
            },
        ));

        if let Some(&root) = header.roots().first() {
            let cells = ok!(header.finalize(context));
            if let Some(root) = cells.get(root) {
                return Ok(root);
            }
        }

        Err(de::Error::RootCellNotFound)
    }

    /// Decodes a pair of cell trees using the specified cell context.
    pub fn decode_pair_ext(
        data: &[u8],
        context: &mut dyn CellContext,
    ) -> Result<(Cell, Cell), de::Error> {
        use self::de::*;

        let header = ok!(de::BocHeader::decode(
            data,
            &Options {
                max_roots: Some(2),
                min_roots: Some(2),
            },
        ));

        let mut roots = header.roots().iter();
        if let (Some(&root1), Some(&root2)) = (roots.next(), roots.next()) {
            let cells = ok!(header.finalize(context));
            if let (Some(root1), Some(root2)) = (cells.get(root1), cells.get(root2)) {
                return Ok((root1, root2));
            }
        }

        Err(de::Error::RootCellNotFound)
    }

    /// Serializes cell into an encoded BOC (as base64 for human readable serializers).
    #[cfg(feature = "serde")]
    pub fn serialize<S, T>(cell: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
        T: AsRef<DynCell> + ?Sized,
    {
        use serde::Serialize;

        cell.as_ref().serialize(serializer)
    }

    /// Deserializes cell from an encoded BOC (from base64 for human readable deserializers).
    #[cfg(feature = "serde")]
    pub fn deserialize<'de, D>(deserializer: D) -> Result<Cell, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::Error;

        let is_human_readable = deserializer.is_human_readable();
        let mut boc = ok!(borrow_cow_bytes(deserializer));

        if is_human_readable {
            match crate::util::decode_base64(boc) {
                Ok(bytes) => {
                    boc = std::borrow::Cow::Owned(bytes);
                }
                Err(_) => return Err(Error::custom("invalid base64 string")),
            }
        }

        match Boc::decode(boc) {
            Ok(cell) => Ok(cell),
            Err(e) => Err(Error::custom(e)),
        }
    }
}

/// BOC representation helper.
pub struct BocRepr;

impl BocRepr {
    /// Encodes the specified cell tree as BOC using an empty cell context and
    /// returns the `base64` encoded bytes as a string.
    #[cfg(any(feature = "base64", test))]
    pub fn encode_base64<T>(data: T) -> Result<String, crate::error::Error>
    where
        T: Store,
    {
        let boc = ok!(Self::encode_ext(data, &mut Cell::empty_context()));
        Ok(crate::util::encode_base64(boc))
    }

    /// Encodes the specified cell tree as BOC using an empty cell context and
    /// returns the `base64` encoded bytes as a string.
    ///
    /// Uses `rayon` under the hood to parallelize encoding.
    #[cfg(all(any(feature = "base64", test), feature = "rayon"))]
    pub fn encode_base64_rayon<T>(data: T) -> Result<String, crate::error::Error>
    where
        T: Store,
    {
        let boc = ok!(Self::encode_rayon_ext(data, &mut Cell::empty_context()));
        Ok(crate::util::encode_base64(boc))
    }

    /// Encodes the specified cell tree as BOC using an empty cell context.
    pub fn encode<T>(data: T) -> Result<Vec<u8>, crate::error::Error>
    where
        T: Store,
    {
        Self::encode_ext(data, &mut Cell::empty_context())
    }

    /// Encodes the specified cell tree as BOC using an empty cell context.
    ///
    /// Uses `rayon` under the hood to parallelize encoding.
    #[cfg(feature = "rayon")]
    pub fn encode_rayon<T>(data: T) -> Result<Vec<u8>, crate::error::Error>
    where
        T: Store,
    {
        Self::encode_rayon_ext(data, &mut Cell::empty_context())
    }

    /// Decodes a `base64` encoded BOC into an object
    /// using an empty cell context.
    #[cfg(any(feature = "base64", test))]
    #[inline]
    pub fn decode_base64<T, D>(data: D) -> Result<T, BocReprError>
    where
        for<'a> T: Load<'a>,
        D: AsRef<[u8]>,
    {
        fn decode_base64_impl<T>(data: &[u8]) -> Result<T, BocReprError>
        where
            for<'a> T: Load<'a>,
        {
            match crate::util::decode_base64(data) {
                Ok(data) => BocRepr::decode_ext(data.as_slice(), &mut Cell::empty_context()),
                Err(_) => Err(BocReprError::InvalidBoc(de::Error::UnknownBocTag)),
            }
        }
        decode_base64_impl::<T>(data.as_ref())
    }

    /// Decodes an object using an empty cell context.
    #[inline]
    pub fn decode<T, D>(data: D) -> Result<T, BocReprError>
    where
        for<'a> T: Load<'a>,
        D: AsRef<[u8]>,
    {
        fn decode_impl<T>(data: &[u8]) -> Result<T, BocReprError>
        where
            for<'a> T: Load<'a>,
        {
            BocRepr::decode_ext(data, &mut Cell::empty_context())
        }
        decode_impl::<T>(data.as_ref())
    }

    /// Encodes the specified object as BOC.
    pub fn encode_ext<T>(
        data: T,
        context: &mut dyn CellContext,
    ) -> Result<Vec<u8>, crate::error::Error>
    where
        T: Store,
    {
        fn encode_ext_impl(
            data: &dyn Store,
            context: &mut dyn CellContext,
        ) -> Result<Vec<u8>, crate::error::Error> {
            let mut builder = CellBuilder::new();
            ok!(data.store_into(&mut builder, context));
            let cell = ok!(builder.build_ext(context));
            Ok(Boc::encode(cell))
        }
        encode_ext_impl(&data, context)
    }

    /// Encodes the specified object as BOC.
    ///
    /// Uses `rayon` under the hood to parallelize encoding.
    #[cfg(feature = "rayon")]
    pub fn encode_rayon_ext<T>(
        data: T,
        context: &mut dyn CellContext,
    ) -> Result<Vec<u8>, crate::error::Error>
    where
        T: Store,
    {
        fn encode_ext_impl(
            data: &dyn Store,
            context: &mut dyn CellContext,
        ) -> Result<Vec<u8>, crate::error::Error> {
            let mut builder = CellBuilder::new();
            ok!(data.store_into(&mut builder, context));
            let cell = ok!(builder.build_ext(context));
            Ok(Boc::encode_rayon(cell))
        }
        encode_ext_impl(&data, context)
    }

    /// Decodes object from BOC using the specified cell context.
    pub fn decode_ext<T>(data: &[u8], context: &mut dyn CellContext) -> Result<T, BocReprError>
    where
        for<'a> T: Load<'a>,
    {
        let cell = match Boc::decode_ext(data, context) {
            Ok(cell) => cell,
            Err(e) => return Err(BocReprError::InvalidBoc(e)),
        };

        match cell.as_ref().parse::<T>() {
            Ok(data) => Ok(data),
            Err(e) => Err(BocReprError::InvalidData(e)),
        }
    }

    /// Serializes the type into an encoded BOC using an empty cell context
    /// (as base64 for human readable serializers).
    #[cfg(feature = "serde")]
    pub fn serialize<S, T>(data: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
        T: Store,
    {
        use serde::ser::{Error, Serialize};

        let context = &mut Cell::empty_context();

        let mut builder = CellBuilder::new();
        if data.store_into(&mut builder, context).is_err() {
            return Err(Error::custom("cell overflow"));
        }

        let cell = match builder.build_ext(context) {
            Ok(cell) => cell,
            Err(_) => return Err(Error::custom("failed to store into builder")),
        };

        cell.as_ref().serialize(serializer)
    }

    /// Deserializes the type from an encoded BOC using an empty cell context
    /// (from base64 for human readable serializers).
    #[cfg(feature = "serde")]
    pub fn deserialize<'de, D, T>(deserializer: D) -> Result<T, D::Error>
    where
        D: serde::Deserializer<'de>,
        for<'a> T: Load<'a>,
    {
        use serde::de::Error;

        let cell = ok!(Boc::deserialize(deserializer));
        match cell.as_ref().parse::<T>() {
            Ok(data) => Ok(data),
            Err(_) => Err(Error::custom("failed to decode object from cells")),
        }
    }
}

/// Error type for BOC repr decoding related errors.
#[derive(Debug, thiserror::Error)]
pub enum BocReprError {
    /// Failed to decode BOC.
    #[error("invalid BOC")]
    InvalidBoc(#[source] de::Error),
    /// Failed to decode data from cells.
    #[error("failed to decode object from cells")]
    InvalidData(#[source] crate::error::Error),
}

#[cfg(feature = "serde")]
fn borrow_cow_bytes<'de: 'a, 'a, D>(deserializer: D) -> Result<std::borrow::Cow<'a, [u8]>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    use std::borrow::Cow;

    use serde::de::{Error, Visitor};

    struct CowBytesVisitor;

    impl<'a> Visitor<'a> for CowBytesVisitor {
        type Value = Cow<'a, [u8]>;

        fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
            formatter.write_str("a byte array")
        }

        fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
        where
            E: Error,
        {
            Ok(Cow::Owned(v.as_bytes().to_vec()))
        }

        fn visit_borrowed_str<E>(self, v: &'a str) -> Result<Self::Value, E>
        where
            E: Error,
        {
            Ok(Cow::Borrowed(v.as_bytes()))
        }

        fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
        where
            E: Error,
        {
            Ok(Cow::Owned(v.into_bytes()))
        }

        fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
        where
            E: Error,
        {
            Ok(Cow::Owned(v.to_vec()))
        }

        fn visit_borrowed_bytes<E>(self, v: &'a [u8]) -> Result<Self::Value, E>
        where
            E: Error,
        {
            Ok(Cow::Borrowed(v))
        }

        fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
        where
            E: Error,
        {
            Ok(Cow::Owned(v))
        }
    }

    deserializer.deserialize_bytes(CowBytesVisitor)
}
