use crate::cell::*;

pub struct MerkleProof<C: CellFamily> {
    pub hash: CellHash,
    pub depth: u16,
    pub cell: CellContainer<C>,
}

impl<C: CellFamily> std::fmt::Debug for MerkleProof<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MerkleProof")
            .field("hash", &hex::encode(self.hash.as_slice()))
            .field("depth", &self.depth)
            .field("cell", &self.cell.as_ref().debug_root())
            .finish()
    }
}

impl<C: CellFamily> Eq for MerkleProof<C> {}
impl<C: CellFamily> PartialEq for MerkleProof<C> {
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash
            && self.depth == other.depth
            && self.cell.as_ref() == other.cell.as_ref()
    }
}

impl<C: CellFamily> Default for MerkleProof<C> {
    fn default() -> Self {
        Self {
            hash: EMPTY_CELL_HASH,
            depth: 0,
            cell: C::empty_cell(),
        }
    }
}

impl<C: CellFamily> Load<'_, C> for MerkleProof<C> {
    fn load_from(s: &mut CellSlice<C>) -> Option<Self> {
        if !s.has_remaining(Self::BITS, Self::REFS) {
            return None;
        }

        if s.get_u8(0)? != CellType::MerkleProof.to_byte() {
            return None;
        }

        let res = Self {
            hash: s.get_u256(8)?,
            depth: s.get_u16(8 + 256)?,
            cell: s.get_reference_cloned(0)?,
        };
        if res.cell.as_ref().hash(0) == &res.hash
            && res.cell.as_ref().depth(0) == res.depth
            && s.try_advance(Self::BITS, Self::REFS)
        {
            Some(res)
        } else {
            None
        }
    }
}

impl<C: CellFamily> Store<C> for MerkleProof<C> {
    fn store_into(&self, b: &mut CellBuilder<C>) -> bool {
        if !b.has_capacity(Self::BITS, Self::REFS) {
            return false;
        }

        let level_mask = self.cell.as_ref().level_mask();
        b.set_level_mask(level_mask.virtualize(1));
        b.store_u8(CellType::MerkleProof.to_byte())
            && b.store_u256(&self.hash)
            && b.store_u16(self.depth)
            && b.store_reference(self.cell.clone())
    }
}

impl<C: CellFamily> MerkleProof<C> {
    pub const BITS: u16 = 8 + 256 + 16;
    pub const REFS: u8 = 1;
}

#[cfg(test)]
mod tests {
    use crate::{RcCellBuilder, RcCellFamily};

    use super::*;

    #[test]
    fn correct_store_load() {
        let default = MerkleProof::<RcCellFamily>::default();

        let mut builder = RcCellBuilder::new();
        assert!(default.store_into(&mut builder));
        let cell = builder.build().unwrap();

        let parsed = MerkleProof::load_from(&mut cell.as_slice()).unwrap();
        assert_eq!(default, parsed);
    }
}
