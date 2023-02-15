use std::borrow::Cow;

use ::serde::{Deserializer, Serialize, Serializer};

use crate::boc::*;
use crate::cell::*;

impl<C: CellFamily> Serialize for dyn Cell<C> + '_ {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let boc = Boc::<C>::encode(self);
        if serializer.is_human_readable() {
            serializer.serialize_str(&crate::util::encode_base64(boc))
        } else {
            serializer.serialize_bytes(&boc)
        }
    }
}

impl<C: CellFamily> Boc<C> {
    /// Serializes cell into an encoded BOC (as base64 for human readable serializers).
    pub fn serialize<S: Serializer, T>(cell: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: AsRef<dyn Cell<C>>,
    {
        cell.as_ref().serialize(serializer)
    }
}

impl<C: DefaultFinalizer> Boc<C> {
    /// Deserializes cell from an encoded BOC (from base64 for human readable deserializers).
    pub fn deserialize<'de, D>(deserializer: D) -> Result<CellContainer<C>, D::Error>
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

        match Boc::<C>::decode(boc) {
            Ok(cell) => Ok(cell),
            Err(e) => Err(Error::custom(e)),
        }
    }
}

impl<C: DefaultFinalizer> BocRepr<C> {
    /// Serializes type using default finalizer into an encoded BOC
    /// (as base64 for human readable serializers).
    pub fn serialize<S: Serializer, T>(data: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: Store<C>,
    {
        use ::serde::ser::Error;

        let mut finalizer = C::default_finalizer();

        let mut builder = CellBuilder::<C>::new();
        if !data.store_into(&mut builder, &mut finalizer) {
            return Err(Error::custom("cell overflow"));
        }

        let cell = match builder.build_ext(&mut finalizer) {
            Some(cell) => cell,
            None => return Err(Error::custom("failed to store into builder")),
        };

        cell.as_ref().serialize(serializer)
    }

    /// Deserializes type using default finalizer from an encoded BOC
    /// (from base64 for human readable serializers).
    pub fn deserialize<'de, D, T>(deserializer: D) -> Result<T, D::Error>
    where
        D: Deserializer<'de>,
        for<'a> T: Load<'a, C>,
    {
        use ::serde::de::Error;

        let cell = ok!(Boc::<C>::deserialize(deserializer));
        match T::load_from(&mut cell.as_ref().as_slice()) {
            Some(data) => Ok(data),
            None => Err(Error::custom("failed to decode object from cells")),
        }
    }
}

fn borrow_cow_bytes<'de: 'a, 'a, D, R>(deserializer: D) -> Result<R, D::Error>
where
    D: Deserializer<'de>,
    R: From<Cow<'a, [u8]>>,
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

    deserializer
        .deserialize_bytes(CowBytesVisitor)
        .map(From::from)
}

#[cfg(test)]
mod tests {
    use crate::boc::*;
    use crate::cell::*;
    use crate::{RcBoc, RcCellFamily};

    #[derive(::serde::Serialize)]
    struct SerdeWithCellRef<'a, C: CellFamily> {
        cell: &'a dyn Cell<C>,
    }

    #[derive(::serde::Serialize, ::serde::Deserialize)]
    struct SerdeWithCellContainer<C: DefaultFinalizer> {
        #[serde(with = "Boc::<C>")]
        some_cell: CellContainer<C>,
    }

    #[derive(::serde::Serialize, ::serde::Deserialize)]
    struct SerdeWithRepr<C: DefaultFinalizer> {
        #[serde(with = "BocRepr::<C>")]
        dict: crate::dict::RawDict<C, 32>,
        #[serde(with = "BocRepr::<C>")]
        merkle_proof: crate::merkle::MerkleProof<C>,
        #[serde(with = "BocRepr::<C>")]
        merkle_update: crate::merkle::MerkleUpdate<C>,
    }

    #[test]
    fn struct_with_cell() {
        let boc = "te6ccgEBAQEAWwAAsUgBUkKKaORs1v/d2CpkdS1rueLjL5EbgaivG/SlIBcUZ5cAKkhRTRyNmt/7uwVMjqWtdzxcZfIjcDUV436UpALijPLQ7msoAAYUWGAAAD6o4PtmhMeK8nJA";

        let test = format!(r#"{{"some_cell":"{boc}"}}"#);
        let SerdeWithCellContainer::<RcCellFamily> { some_cell } =
            serde_json::from_str(&test).unwrap();

        let original = RcBoc::decode_base64(boc).unwrap();
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
        let SerdeWithRepr::<RcCellFamily> {
            dict,
            merkle_proof,
            merkle_update,
        } = serde_json::from_str(&test).unwrap();

        let boc = RcBoc::decode_base64(boc_dict).unwrap();
        let orig_dict = boc.parse::<crate::dict::RawDict<_, 32>>().unwrap();
        assert_eq!(dict, orig_dict);

        let boc = RcBoc::decode_base64(boc_merkle_proof).unwrap();
        let orig_merkle_proof = boc.parse::<crate::merkle::MerkleProof<_>>().unwrap();
        assert_eq!(merkle_proof, orig_merkle_proof);

        let boc = RcBoc::decode_base64(boc_merkle_update).unwrap();
        let orig_merkle_update = boc.parse::<crate::merkle::MerkleUpdate<_>>().unwrap();
        assert_eq!(merkle_update, orig_merkle_update);
    }
}
