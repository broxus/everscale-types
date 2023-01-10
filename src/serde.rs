use std::borrow::Cow;

use ::serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::boc::*;
use crate::cell::*;

impl<C: CellFamily> Serialize for dyn Cell<C> + '_ {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let boc = Boc::<C>::encode(self);
        if serializer.is_human_readable() {
            serializer.serialize_str(&base64::encode(boc))
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
        let mut boc = ok!(Cow::<'de, [u8]>::deserialize(deserializer));

        if is_human_readable {
            match base64::decode(boc) {
                Ok(bytes) => {
                    boc = Cow::Owned(bytes);
                }
                Err(_) => return Err(Error::custom("invalid base64 string")),
            }
        }

        match Boc::<C>::decode(boc) {
            Ok(cell) => Ok(cell),
            Err(e) => Err(D::Error::custom(e)),
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

#[cfg(test)]
mod tests {
    use crate::boc::*;
    use crate::cell::*;

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
        dict: crate::dict::Dict<C, 32>,
        #[serde(with = "BocRepr::<C>")]
        merkle_proof: crate::merkle::MerkleProof<C>,
        #[serde(with = "BocRepr::<C>")]
        merkle_update: crate::merkle::MerkleUpdate<C>,
    }
}
