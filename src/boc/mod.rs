use crate::cell::ArcCell;

pub mod de;

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum BocTag {
    Indexed,
    IndexedCrc32,
    Generic,
}

impl BocTag {
    pub const INDEXED: [u8; 4] = [0x68, 0xff, 0x65, 0xf3];
    pub const INDEXED_CRC32: [u8; 4] = [0xac, 0xc3, 0xa7, 0x28];
    pub const GENERIC: [u8; 4] = [0xb5, 0xee, 0x9c, 0x72];

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

pub fn decode<R>(data: &[u8]) -> std::io::Result<ArcCell> {}
