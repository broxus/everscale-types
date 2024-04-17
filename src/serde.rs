use std::borrow::Cow;

use ::serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::boc::*;
use crate::cell::*;

impl Serialize for HashBytes {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        if serializer.is_human_readable() {
            let mut output = [0u8; 64];
            hex::encode_to_slice(self.0.as_slice(), &mut output).ok();

            // SAFETY: output is guaranteed to contain only [0-9a-f]
            let output = unsafe { std::str::from_utf8_unchecked(&output) };
            serializer.serialize_str(output)
        } else {
            serializer.serialize_bytes(&self.0)
        }
    }
}

impl<'a> Deserialize<'a> for HashBytes {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'a>,
    {
        use ::serde::de::{Error, Visitor};

        struct HashBytesHexVisitor;

        impl<'de> Visitor<'de> for HashBytesHexVisitor {
            type Value = HashBytes;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("hex-encoded byte array of size 32")
            }

            fn visit_str<E: Error>(self, value: &str) -> Result<Self::Value, E> {
                let mut result = HashBytes([0; 32]);
                match hex::decode_to_slice(value, &mut result.0) {
                    Ok(()) => Ok(result),
                    Err(_) => Err(Error::invalid_value(
                        serde::de::Unexpected::Str(value),
                        &self,
                    )),
                }
            }
        }

        pub struct HashBytesRawVisitor;

        impl<'de> Visitor<'de> for HashBytesRawVisitor {
            type Value = HashBytes;

            fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.write_fmt(format_args!("a byte array of size 32"))
            }

            fn visit_bytes<E: Error>(self, v: &[u8]) -> Result<Self::Value, E> {
                v.try_into()
                    .map(HashBytes)
                    .map_err(|_e| Error::invalid_length(v.len(), &self))
            }
        }

        if deserializer.is_human_readable() {
            deserializer.deserialize_str(HashBytesHexVisitor)
        } else {
            deserializer.deserialize_bytes(HashBytesRawVisitor)
        }
    }
}

impl Serialize for DynCell {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let boc = Boc::encode(self);
        if serializer.is_human_readable() {
            serializer.serialize_str(&crate::util::encode_base64(boc))
        } else {
            serializer.serialize_bytes(&boc)
        }
    }
}

impl Boc {
    /// Serializes cell into an encoded BOC (as base64 for human readable serializers).
    pub fn serialize<S: Serializer, T>(cell: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: AsRef<DynCell> + ?Sized,
    {
        cell.as_ref().serialize(serializer)
    }
}

impl Boc {
    /// Deserializes cell from an encoded BOC (from base64 for human readable deserializers).
    pub fn deserialize<'de, D>(deserializer: D) -> Result<Cell, D::Error>
    where
        D: Deserializer<'de>,
    {
        use ::serde::de::Error;

        let is_human_readable = deserializer.is_human_readable();
        let mut boc = ok!(borrow_cow_bytes(deserializer));

        if is_human_readable {
            match crate::util::decode_base64(boc) {
                Ok(bytes) => {
                    boc = Cow::Owned(bytes);
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

impl BocRepr {
    /// Serializes the type into an encoded BOC using an empty cell context
    /// (as base64 for human readable serializers).
    pub fn serialize<S: Serializer, T>(data: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: Store,
    {
        use ::serde::ser::Error;

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
    pub fn deserialize<'de, D, T>(deserializer: D) -> Result<T, D::Error>
    where
        D: Deserializer<'de>,
        for<'a> T: Load<'a>,
    {
        use ::serde::de::Error;

        let cell = ok!(Boc::deserialize(deserializer));
        match cell.as_ref().parse::<T>() {
            Ok(data) => Ok(data),
            Err(_) => Err(Error::custom("failed to decode object from cells")),
        }
    }
}

fn borrow_cow_bytes<'de: 'a, 'a, D>(deserializer: D) -> Result<Cow<'a, [u8]>, D::Error>
where
    D: Deserializer<'de>,
{
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

#[cfg(test)]
mod tests {
    use crate::boc::*;
    use crate::cell::*;

    #[derive(::serde::Serialize)]
    struct SerdeWithCellRef<'a> {
        cell: &'a DynCell,
    }

    #[derive(::serde::Serialize, ::serde::Deserialize)]
    struct SerdeWithHashBytes {
        some_hash: HashBytes,
    }

    #[derive(::serde::Serialize, ::serde::Deserialize)]
    struct SerdeWithCellContainer {
        #[serde(with = "Boc")]
        some_cell: Cell,
    }

    #[derive(::serde::Serialize, ::serde::Deserialize)]
    struct SerdeWithRepr {
        #[serde(with = "BocRepr")]
        dict: crate::dict::RawDict<32>,
        #[serde(with = "BocRepr")]
        merkle_proof: crate::merkle::MerkleProof,
        #[serde(with = "BocRepr")]
        merkle_update: crate::merkle::MerkleUpdate,
    }

    #[test]
    fn hex_bytes() {
        let hash: HashBytes = rand::random();

        let test = format!(r#"{{"some_hash":"{hash}"}}"#);
        let SerdeWithHashBytes { some_hash } = serde_json::from_str(&test).unwrap();
        assert_eq!(some_hash, hash);

        let serialized = serde_json::to_string(&SerdeWithHashBytes { some_hash }).unwrap();
        assert_eq!(serialized, test);
    }

    #[test]
    fn struct_with_cell() {
        let boc = "te6ccgEBAQEAWwAAsUgBUkKKaORs1v/d2CpkdS1rueLjL5EbgaivG/SlIBcUZ5cAKkhRTRyNmt/7uwVMjqWtdzxcZfIjcDUV436UpALijPLQ7msoAAYUWGAAAD6o4PtmhMeK8nJA";

        let test = format!(r#"{{"some_cell":"{boc}"}}"#);
        let SerdeWithCellContainer { some_cell } = serde_json::from_str(&test).unwrap();

        let original = Boc::decode_base64(boc).unwrap();
        assert_eq!(some_cell.as_ref(), original.as_ref());
    }

    #[test]
    fn struct_with_repr() {
        let boc_dict =
            "te6ccgEBCAEAMAABAcABAgPPQAUCAgEgBAMACQAAADqgAAkAAABQYAIBIAcGAAkAAAAe4AAJAAAAbCA=";
        let boc_dict_escaped =
            "te6ccgEBC\\u0041EAMAABAcABAgPPQAUCAgEgBAMACQAAADqgAAkAAABQYAIBIAcGAAkAAAAe4AAJAAAAbCA=";

        let boc_merkle_proof = "te6ccgECBQEAARwACUYDcijLZ4hNbjcLQiThSx8fvxTaVufKbXsXRYbyiUZApXoADQEiccAJ2Y4sgpswmr6/odN0WmKosRtoIzobXRBE9uCeOA1nuXKSo06DG3E/cAAAdbacX3gRQHLHOx0TQAQCAdURYfZ8pYDdK5k1lnsEEJ4OmIYB/AiU4UX3zVZTToFyVwAAAYRmS/s2iLD7PlLAbpXMmss9gghPB0xDAP4ESnCi++arKadAuSuAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACAsAMARaACLD7PlLAbpXMmss9gghPB0xDAP4ESnCi++arKadAuSuAQKEgBAYDWxHxKJVQ8mzl7cXFvP64eLF0kcXTFLiwZvYlkQrEFAAw=";
        let boc_merkle_update = "te6ccgECEAEAARwACooEmiQq0C+sMHHtQMrhM1KQs0bAR0to7UTxJ/BQaQGQ83mYWpNZrI3tjuzPRZkP0y+odW6SpuxZc6qHEJbPhzX/oAAFAAUIASEBwAIiA85AAwoiASAEDCIBIAUOAgEgBwYACQAAAAKgAAkAAAAAYCEBwAkiA85ACwooSAEBGK24YcgkheIaweTweCPOdGONsG1894aroQWmpQQGjHEAASIBIA0MKEgBAcoZQygrtOJrqvmwmN7NXJy91VsFFfgo/bXAJjbPwI+zAAIiASAPDihIAQGIedrQvLIQIcZHiObah2QWYzPcsgz02CKj0RfEEjv9NwABKEgBAf96V360Wpctur/NPJVfI6Mc5W43dmQzVmLGk0RxKb5RAAE=";

        let test = format!(
            r#"{{"dict":"{boc_dict_escaped}","merkle_proof":"{boc_merkle_proof}","merkle_update":"{boc_merkle_update}"}}"#
        );
        let SerdeWithRepr {
            dict,
            merkle_proof,
            merkle_update,
        } = serde_json::from_str(&test).unwrap();

        let boc = Boc::decode_base64(boc_dict).unwrap();
        let orig_dict = boc.parse::<crate::dict::RawDict<32>>().unwrap();
        assert_eq!(dict, orig_dict);

        let boc = Boc::decode_base64(boc_merkle_proof).unwrap();
        let orig_merkle_proof = boc.parse::<crate::merkle::MerkleProof>().unwrap();
        assert_eq!(merkle_proof, orig_merkle_proof);

        let boc = Boc::decode_base64(boc_merkle_update).unwrap();
        let orig_merkle_update = boc.parse::<crate::merkle::MerkleUpdate>().unwrap();
        assert_eq!(merkle_update, orig_merkle_update);
    }
}
