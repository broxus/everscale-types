pub use boc_reader::BocReader;

mod boc_reader;

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum BocTag {
    Indexed,
    IndexedCrc32,
    Generic,
}

impl BocTag {
    pub const BOC_INDEXED_TAG: [u8; 4] = [0x68, 0xff, 0x65, 0xf3];
    pub const BOC_INDEXED_CRC32_TAG: [u8; 4] = [0xac, 0xc3, 0xa7, 0x28];
    pub const BOC_GENERIC_TAG: [u8; 4] = [0xb5, 0xee, 0x9c, 0x72];

    pub const fn from_bytes(data: [u8; 4]) -> Option<Self> {
        match data {
            Self::BOC_GENERIC_TAG => Some(Self::Generic),
            Self::BOC_INDEXED_CRC32_TAG => Some(Self::IndexedCrc32),
            Self::BOC_INDEXED_TAG => Some(Self::Indexed),
            _ => None,
        }
    }

    pub const fn to_bytes(self) -> [u8; 4] {
        match self {
            Self::Indexed => Self::BOC_INDEXED_TAG,
            Self::IndexedCrc32 => Self::BOC_INDEXED_CRC32_TAG,
            Self::Generic => Self::BOC_GENERIC_TAG,
        }
    }
}
