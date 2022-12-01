use crate::cell::finalizer::Finalizer;
use crate::cell::generic_cell::GenericCellFinalizer;
use crate::cell::{ArcCell, Cell};

/// BOC decoder implementation
pub mod de;

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum BocTag {
    Indexed,
    IndexedCrc32,
    Generic,
}

impl BocTag {
    const INDEXED: [u8; 4] = [0x68, 0xff, 0x65, 0xf3];
    const INDEXED_CRC32: [u8; 4] = [0xac, 0xc3, 0xa7, 0x28];
    const GENERIC: [u8; 4] = [0xb5, 0xee, 0x9c, 0x72];

    pub const fn from_bytes(data: [u8; 4]) -> Option<Self> {
        match data {
            Self::GENERIC => Some(Self::Generic),
            Self::INDEXED_CRC32 => Some(Self::IndexedCrc32),
            Self::INDEXED => Some(Self::Indexed),
            _ => None,
        }
    }

    pub const fn to_bytes(self) -> [u8; 4] {
        match self {
            Self::Indexed => Self::INDEXED,
            Self::IndexedCrc32 => Self::INDEXED_CRC32,
            Self::Generic => Self::GENERIC,
        }
    }
}

/// BOC (Bag Of Cells) helper
pub struct Boc<R = ArcCell> {
    _cell_type: std::marker::PhantomData<R>,
}

impl<R> Boc<R>
where
    R: AsRef<dyn Cell> + Clone,
{
    /// Decodes a cell tree using the specified finalizer
    pub fn decode_ext(data: &[u8], finalizer: &mut dyn Finalizer<R>) -> Result<R, de::Error> {
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

    /// Decodes a pair of cell trees using the specified finalizer
    pub fn decode_pair_ext(
        data: &[u8],
        finalizer: &mut dyn Finalizer<R>,
    ) -> Result<(R, R), de::Error> {
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

impl Boc<ArcCell> {
    /// Decodes a cell tree
    #[inline]
    pub fn decode<T>(data: T) -> Result<ArcCell, de::Error>
    where
        T: AsRef<[u8]>,
    {
        fn decode_impl(data: &[u8]) -> Result<ArcCell, de::Error> {
            Boc::<ArcCell>::decode_ext(data, &mut GenericCellFinalizer)
        }
        decode_impl(data.as_ref())
    }

    /// Decodes a pair of cell trees
    #[inline]
    pub fn decode_pair<T>(data: &T) -> Result<(ArcCell, ArcCell), de::Error>
    where
        T: AsRef<[u8]>,
    {
        fn decode_pair_impl(data: &[u8]) -> Result<(ArcCell, ArcCell), de::Error> {
            Boc::<ArcCell>::decode_pair_ext(data, &mut GenericCellFinalizer)
        }
        decode_pair_impl(data.as_ref())
    }
}
