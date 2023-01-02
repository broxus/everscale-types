//! BOC (Bag Of Cells) implementation.

use crate::cell::{Cell, CellContainer, CellFamily, DefaultFinalizer, Finalizer};

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
    #[cfg(feature = "base64")]
    pub fn encode_base64(cell: &dyn Cell<C>) -> String {
        base64::encode(Self::encode(cell))
    }

    /// Encodes the specified cell tree as BOC.
    // TODO: somehow use Borrow with GATs
    pub fn encode(cell: &dyn Cell<C>) -> Vec<u8> {
        let mut result = Vec::new();
        ser::BocHeader::<C>::new(cell).encode(&mut result);
        result
    }

    /// Encodes a pair of cell trees as BOC.
    // TODO: somehow use Borrow with GATs
    pub fn encode_pair((cell1, cell2): (&dyn Cell<C>, &dyn Cell<C>)) -> Vec<u8> {
        let mut result = Vec::new();
        let mut encoder = ser::BocHeader::<C>::new(cell1);
        encoder.add_root(cell2);
        encoder.encode(&mut result);
        result
    }
}

impl<C: DefaultFinalizer> Boc<C> {
    /// Decodes a `base64` encoded BOC into a cell tree
    /// using the default Cell family finalizer.
    #[cfg(feature = "base64")]
    #[inline]
    pub fn decode_base64<T: AsRef<[u8]>>(data: T) -> Result<CellContainer<C>, de::Error> {
        fn decode_base64_impl<C: DefaultFinalizer>(
            data: &[u8],
        ) -> Result<CellContainer<C>, de::Error> {
            match base64::decode(data) {
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

type CellContainerPair<C> = (CellContainer<C>, CellContainer<C>);
