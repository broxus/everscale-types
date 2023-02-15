//! BOC (Bag Of Cells) implementation.

use std::borrow::Borrow;

use crate::cell::{
    Cell, CellBuilder, CellContainer, CellFamily, DefaultFinalizer, Finalizer, Load, Store,
};

/// BOC decoder implementation.
pub mod de;
/// BOC encoder implementation.
pub mod ser;

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

/// BOC (Bag Of Cells) helper.
pub struct Boc<C> {
    _cell_type: std::marker::PhantomData<C>,
}

impl<C: CellFamily> Boc<C> {
    /// Encodes the specified cell tree as BOC and
    /// returns the `base64` encoded bytes as a string.
    #[cfg(any(feature = "base64", test))]
    pub fn encode_base64<'a, T>(cell: T) -> String
    where
        T: Borrow<dyn Cell<C> + 'a>,
    {
        crate::util::encode_base64(Self::encode(cell))
    }

    /// Encodes the specified cell tree as BOC.
    pub fn encode<'a, T>(cell: T) -> Vec<u8>
    where
        T: Borrow<dyn Cell<C> + 'a>,
    {
        fn encode_impl<C: CellFamily>(cell: &dyn Cell<C>) -> Vec<u8> {
            let mut result = Vec::new();
            ser::BocHeader::<C>::new(cell).encode(&mut result);
            result
        }
        encode_impl(cell.borrow())
    }

    /// Encodes a pair of cell trees as BOC.
    pub fn encode_pair<'a, T1, T2>((cell1, cell2): (T1, T2)) -> Vec<u8>
    where
        T1: Borrow<dyn Cell<C> + 'a>,
        T2: Borrow<dyn Cell<C> + 'a>,
    {
        fn encode_pair_impl<C: CellFamily>(cell1: &dyn Cell<C>, cell2: &dyn Cell<C>) -> Vec<u8> {
            let mut result = Vec::new();
            let mut encoder = ser::BocHeader::<C>::new(cell1);
            encoder.add_root(cell2);
            encoder.encode(&mut result);
            result
        }
        encode_pair_impl(cell1.borrow(), cell2.borrow())
    }
}

impl<C: DefaultFinalizer> Boc<C> {
    /// Decodes a `base64` encoded BOC into a cell tree
    /// using the default Cell family finalizer.
    #[cfg(any(feature = "base64", test))]
    #[inline]
    pub fn decode_base64<T: AsRef<[u8]>>(data: T) -> Result<CellContainer<C>, de::Error> {
        fn decode_base64_impl<C: DefaultFinalizer>(
            data: &[u8],
        ) -> Result<CellContainer<C>, de::Error> {
            match crate::util::decode_base64(data) {
                Ok(data) => Boc::<C>::decode_ext(data.as_slice(), &mut C::default_finalizer()),
                Err(_) => Err(de::Error::UnknownBocTag),
            }
        }
        decode_base64_impl::<C>(data.as_ref())
    }

    /// Decodes a cell tree using the default Cell family finalizer.
    #[inline]
    pub fn decode<T>(data: T) -> Result<CellContainer<C>, de::Error>
    where
        T: AsRef<[u8]>,
    {
        fn decode_impl<C: DefaultFinalizer>(data: &[u8]) -> Result<CellContainer<C>, de::Error> {
            Boc::<C>::decode_ext(data, &mut C::default_finalizer())
        }
        decode_impl::<C>(data.as_ref())
    }

    /// Decodes a pair of cell trees using the default Cell family finalizer.
    #[inline]
    pub fn decode_pair<T>(data: T) -> Result<CellContainerPair<C>, de::Error>
    where
        T: AsRef<[u8]>,
    {
        fn decode_pair_impl<C: DefaultFinalizer>(
            data: &[u8],
        ) -> Result<CellContainerPair<C>, de::Error> {
            Boc::<C>::decode_pair_ext(data, &mut C::default_finalizer())
        }
        decode_pair_impl::<C>(data.as_ref())
    }
}

impl<C: CellFamily> Boc<C> {
    /// Decodes a cell tree using the specified finalizer.
    pub fn decode_ext(
        data: &[u8],
        finalizer: &mut dyn Finalizer<C>,
    ) -> Result<CellContainer<C>, de::Error> {
        use self::de::*;

        let header = ok!(de::BocHeader::decode(
            data,
            &Options {
                max_roots: Some(1),
                min_roots: Some(1),
            },
        ));

        if let Some(&root) = header.roots().first() {
            let cells = ok!(header.finalize(finalizer));
            if let Some(root) = cells.get(root) {
                return Ok(root);
            }
        }

        Err(de::Error::RootCellNotFound)
    }

    /// Decodes a pair of cell trees using the specified finalizer.
    pub fn decode_pair_ext(
        data: &[u8],
        finalizer: &mut dyn Finalizer<C>,
    ) -> Result<CellContainerPair<C>, de::Error> {
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
            let cells = ok!(header.finalize(finalizer));
            if let (Some(root1), Some(root2)) = (cells.get(root1), cells.get(root2)) {
                return Ok((root1, root2));
            }
        }

        Err(de::Error::RootCellNotFound)
    }
}

/// BOC representation helper.
pub struct BocRepr<C> {
    _cell_type: std::marker::PhantomData<C>,
}

impl<C: DefaultFinalizer> BocRepr<C> {
    /// Encodes the specified cell tree as BOC using default finalizer and
    /// returns the `base64` encoded bytes as a string.
    #[cfg(any(feature = "base64", test))]
    pub fn encode_base64<T>(data: T) -> Option<String>
    where
        T: Store<C>,
    {
        let boc = Self::encode_ext(data, &mut C::default_finalizer())?;
        Some(crate::util::encode_base64(boc))
    }

    /// Encodes the specified cell tree as BOC using default finalizer.
    pub fn encode<T>(data: T) -> Option<Vec<u8>>
    where
        T: Store<C>,
    {
        Self::encode_ext(data, &mut C::default_finalizer())
    }

    /// Decodes a `base64` encoded BOC into an object
    /// using the default Cell family finalizer.
    #[cfg(any(feature = "base64", test))]
    #[inline]
    pub fn decode_base64<T, D>(data: D) -> Result<T, BocReprError>
    where
        for<'a> T: Load<'a, C>,
        D: AsRef<[u8]>,
    {
        fn decode_base64_impl<C, T>(data: &[u8]) -> Result<T, BocReprError>
        where
            C: DefaultFinalizer,
            for<'a> T: Load<'a, C>,
        {
            match crate::util::decode_base64(data) {
                Ok(data) => BocRepr::<C>::decode_ext(data.as_slice(), &mut C::default_finalizer()),
                Err(_) => Err(BocReprError::InvalidBoc(de::Error::UnknownBocTag)),
            }
        }
        decode_base64_impl::<C, T>(data.as_ref())
    }

    /// Decodes an object using the default Cell family finalizer.
    #[inline]
    pub fn decode<T, D>(data: D) -> Result<T, BocReprError>
    where
        for<'a> T: Load<'a, C>,
        D: AsRef<[u8]>,
    {
        fn decode_impl<C, T>(data: &[u8]) -> Result<T, BocReprError>
        where
            C: DefaultFinalizer,
            for<'a> T: Load<'a, C>,
        {
            BocRepr::<C>::decode_ext(data, &mut C::default_finalizer())
        }
        decode_impl::<C, T>(data.as_ref())
    }
}

impl<C: CellFamily> BocRepr<C> {
    /// Encodes the specified object as BOC.
    pub fn encode_ext<T>(data: T, finalizer: &mut dyn Finalizer<C>) -> Option<Vec<u8>>
    where
        T: Store<C>,
    {
        let mut builder = CellBuilder::<C>::new();
        if !data.store_into(&mut builder, finalizer) {
            return None;
        }

        let cell = builder.build_ext(finalizer)?;
        Some(Boc::<C>::encode(cell))
    }

    /// Decodes object from BOC using the specified finalizer.
    pub fn decode_ext<T>(data: &[u8], finalizer: &mut dyn Finalizer<C>) -> Result<T, BocReprError>
    where
        for<'a> T: Load<'a, C>,
    {
        let cell = match Boc::<C>::decode_ext(data, finalizer) {
            Ok(cell) => cell,
            Err(e) => return Err(BocReprError::InvalidBoc(e)),
        };
        match T::load_from(&mut cell.as_ref().as_slice()) {
            Some(data) => Ok(data),
            None => Err(BocReprError::InvalidData),
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
    InvalidData,
}

type CellContainerPair<C> = (CellContainer<C>, CellContainer<C>);
