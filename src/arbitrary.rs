//!

use arbitrary::{Arbitrary, MaxRecursionReached, Result, Unstructured};

use crate::cell::{
    Cell, CellBuilder, CellFamily, CellType, DynCell, HashBytes, LevelMask, Store, MAX_BIT_LEN,
};
use crate::merkle::{MerkleProof, MerkleUpdate};
use crate::num::{SplitDepth, Tokens, Uint12, Uint15, Uint9, VarUint24, VarUint248, VarUint56};
use crate::util::ArrayVec;

impl<'a> Arbitrary<'a> for HashBytes {
    #[inline]
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary().map(Self)
    }

    #[inline]
    fn size_hint(_: usize) -> (usize, Option<usize>) {
        (32, Some(32))
    }
}

impl<'a> Arbitrary<'a> for CellType {
    #[inline]
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        static ALL_TYPES: [CellType; 5] = [
            CellType::Ordinary,
            CellType::PrunedBranch,
            CellType::LibraryReference,
            CellType::MerkleProof,
            CellType::MerkleUpdate,
        ];

        u.choose(&ALL_TYPES).copied()
    }

    #[inline]
    fn size_hint(_: usize) -> (usize, Option<usize>) {
        (1, Some(1))
    }
}

impl<'a> Arbitrary<'a> for LevelMask {
    #[inline]
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.int_in_range(0b000..=0b111).map(LevelMask::new)
    }

    #[inline]
    fn size_hint(_: usize) -> (usize, Option<usize>) {
        (1, Some(1))
    }
}

impl<'a> Arbitrary<'a> for Cell {
    #[inline]
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(CellBuilder::arbitrary(u)?.build().unwrap())
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        Self::try_size_hint(depth).unwrap_or_default()
    }

    #[inline]
    fn try_size_hint(depth: usize) -> Result<(usize, Option<usize>), MaxRecursionReached> {
        <CellBuilder as Arbitrary>::try_size_hint(depth)
    }
}

impl<'a> Arbitrary<'a> for CellBuilder {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        match CellType::arbitrary(u)? {
            CellType::Ordinary => {
                let bit_len = u.int_in_range(0..=MAX_BIT_LEN)?;
                let refs = u.int_in_range(0..=4)?;

                let mut b = CellBuilder::new();
                b.store_raw(u.bytes(bit_len.div_ceil(8) as _)?, bit_len)
                    .unwrap();

                let mut children = ArrayVec::<Cell, 4>::new();
                for i in 0..refs as u8 {
                    let cell = 'cell: {
                        if i > 0 {
                            // Allow to reuse cells.
                            if let Some(i) = u.int_in_range(0..=i)?.checked_sub(1) {
                                break 'cell children.get(i).cloned().unwrap();
                            }
                        }

                        Cell::arbitrary(u).and_then(check_max_depth)?
                    };

                    b.store_reference(cell.clone()).unwrap();

                    // SAFETY: `refs` is at most 4.
                    unsafe { children.push(cell) };
                }

                Ok(b)
            }
            CellType::PrunedBranch => {
                let level_mask = LevelMask::new(u.int_in_range(0b001..=0b111)?);

                let mut b = CellBuilder::new();
                b.set_exotic(true);
                b.store_u16(u16::from_be_bytes([
                    CellType::PrunedBranch.to_byte(),
                    level_mask.to_byte(),
                ]))
                .unwrap();

                let level_count = level_mask.level() as usize;

                let hashes = 32 * level_count;
                b.store_raw(u.bytes(hashes)?, hashes as u16 * 8).unwrap();

                for _ in 0..level_count {
                    b.store_u16(u.int_in_range(0..=(u16::MAX - 1))?).unwrap();
                }

                Ok(b)
            }
            CellType::LibraryReference => {
                let hash = u.bytes(32)?;

                let mut b = CellBuilder::new();
                b.set_exotic(true);
                b.store_u8(CellType::LibraryReference.to_byte()).unwrap();
                b.store_raw(hash, 256).unwrap();
                Ok(b)
            }
            CellType::MerkleProof => {
                let mut b = CellBuilder::new();
                MerkleProof::arbitrary(u)?
                    .store_into(&mut b, Cell::empty_context())
                    .unwrap();
                Ok(b)
            }
            CellType::MerkleUpdate => {
                let mut b = CellBuilder::new();
                MerkleUpdate::arbitrary(u)?
                    .store_into(&mut b, Cell::empty_context())
                    .unwrap();
                Ok(b)
            }
        }
    }

    fn size_hint(_: usize) -> (usize, Option<usize>) {
        (2, None)
    }
}

impl<'a> Arbitrary<'a> for MerkleProof {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let cell = Cell::arbitrary(u).and_then(check_max_depth)?;
        Ok(Self {
            hash: *cell.hash(0),
            depth: cell.depth(0),
            cell,
        })
    }
}

impl<'a> Arbitrary<'a> for MerkleUpdate {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let old = Cell::arbitrary(u).and_then(check_max_depth)?;
        let new = Cell::arbitrary(u).and_then(check_max_depth)?;
        Ok(Self {
            old_hash: *old.hash(0),
            new_hash: *new.hash(0),
            old_depth: old.depth(0),
            new_depth: new.depth(0),
            old,
            new,
        })
    }

    fn size_hint(_: usize) -> (usize, Option<usize>) {
        (4, None)
    }
}

fn check_max_depth<T: AsRef<DynCell>>(cell: T) -> Result<T, arbitrary::Error> {
    if has_max_depth(cell.as_ref()) {
        return Err(arbitrary::Error::IncorrectFormat);
    }

    Ok(cell)
}

fn has_max_depth(cell: &DynCell) -> bool {
    for level in cell.descriptor().level_mask() {
        if cell.depth(level) == u16::MAX {
            return false;
        }
    }
    true
}

macro_rules! impl_custom_int {
    ($($ty:ty => $n:literal),*$(,)?) => {
        $(impl<'a> Arbitrary<'a> for $ty {
            #[inline]
            fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
                u.int_in_range(0..=<$ty>::MAX.into_inner()).map(<$ty>::new)
            }

            #[inline]
            fn size_hint(_: usize) -> (usize, Option<usize>) {
                ($n, Some($n))
            }
        })*
    };
}

impl_custom_int! {
    Uint9 => 2,
    Uint12 => 2,
    Uint15 => 2,
    VarUint24 => 4,
    VarUint56 => 8,
    Tokens => 16,
}

impl<'a> Arbitrary<'a> for VarUint248 {
    #[inline]
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(Self::from_words(
            u.int_in_range(0..=(u128::MAX >> 8))?,
            u.arbitrary()?,
        ))
    }

    #[inline]
    fn size_hint(_: usize) -> (usize, Option<usize>) {
        (32, Some(32))
    }
}

impl<'a> Arbitrary<'a> for SplitDepth {
    #[inline]
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        const MIN: u8 = SplitDepth::MIN.into_bit_len() as u8;
        const MAX: u8 = SplitDepth::MAX.into_bit_len() as u8;
        Ok(Self::new(u.int_in_range(MIN..=MAX)?).unwrap())
    }

    fn size_hint(_: usize) -> (usize, Option<usize>) {
        (1, Some(1))
    }
}

#[cfg(feature = "models")]
impl<'a> Arbitrary<'a> for crate::models::Anycast {
    #[inline]
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let split_depth = SplitDepth::arbitrary(u)?;
        let bit_len = split_depth.into_bit_len();

        let bytes = u.bytes(bit_len.div_ceil(8) as _)?;

        let b = CellBuilder::from_raw_data(&bytes, bit_len).unwrap();
        Ok(Self::from_slice(&b.as_data_slice()).unwrap())
    }

    #[inline]
    fn size_hint(_: usize) -> (usize, Option<usize>) {
        (2, Some(5))
    }
}

#[cfg(feature = "models")]
impl<'a> Arbitrary<'a> for crate::models::StdAddr {
    #[inline]
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(Self {
            anycast: u.ratio(1u8, 20u8)?.then(|| u.arbitrary()).transpose()?,
            workchain: u.arbitrary()?,
            address: u.arbitrary()?,
        })
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            Option::<crate::models::Anycast>::size_hint(depth),
            (33, Some(33)),
        )
    }
}

#[cfg(feature = "models")]
impl<'a> Arbitrary<'a> for crate::models::VarAddr {
    #[inline]
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let anycast = u.ratio(1u8, 20u8)?.then(|| u.arbitrary()).transpose()?;
        let address_len = u.arbitrary::<Uint9>()?;
        let workchain = u.arbitrary()?;

        let bit_len = address_len.into_inner() as usize;
        let mut address = u.bytes(bit_len.div_ceil(8))?.to_vec();
        if let Some(last_byte) = address.last_mut() {
            let rem = bit_len % 8;
            if rem != 0 {
                *last_byte &= u8::MAX << (8 - rem);
            }
        }

        Ok(Self {
            anycast,
            address_len,
            workchain,
            address,
        })
    }

    #[inline]
    fn size_hint(_: usize) -> (usize, Option<usize>) {
        (1 + 2 + 4, None)
    }
}

#[cfg(feature = "models")]
impl<'a> Arbitrary<'a> for crate::models::IntAddr {
    #[inline]
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        if u.ratio(1u8, 20u8)? {
            u.arbitrary().map(Self::Var)
        } else {
            u.arbitrary().map(Self::Std)
        }
    }

    #[inline]
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        Self::try_size_hint(depth).unwrap_or_default()
    }

    #[inline]
    fn try_size_hint(depth: usize) -> Result<(usize, Option<usize>), MaxRecursionReached> {
        Ok(arbitrary::size_hint::and(
            <u8 as Arbitrary>::try_size_hint(depth)?,
            arbitrary::size_hint::or(
                crate::models::StdAddr::size_hint(depth),
                crate::models::VarAddr::size_hint(depth),
            ),
        ))
    }
}
