use crate::cell::*;

pub struct MerkleUpdate<C: CellFamily> {
    pub old_hash: CellHash,
    pub new_hash: CellHash,
    pub old_depth: u16,
    pub new_depth: u16,
    pub old: CellContainer<C>,
    pub new: CellContainer<C>,
}

impl<C: CellFamily> std::fmt::Debug for MerkleUpdate<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MerkleUpdate")
            .field("old_hash", &self.old_hash)
            .field("new_hash", &self.new_hash)
            .field("old_depth", &self.old_depth)
            .field("new_depth", &self.new_depth)
            .field("old", &self.old.as_ref().debug_root())
            .field("new", &self.new.as_ref().debug_root())
            .finish()
    }
}

impl<C: CellFamily> Eq for MerkleUpdate<C> {}
impl<C: CellFamily> PartialEq for MerkleUpdate<C> {
    fn eq(&self, other: &Self) -> bool {
        self.old_hash == other.old_hash
            && self.new_hash == other.new_hash
            && self.old_depth == other.old_depth
            && self.new_depth == other.new_depth
            && self.old.as_ref() == other.old.as_ref()
            && self.new.as_ref() == other.new.as_ref()
    }
}

impl<C: CellFamily> Default for MerkleUpdate<C> {
    fn default() -> Self {
        let empty_cell = C::empty_cell();
        Self {
            old_hash: EMPTY_CELL_HASH,
            new_hash: EMPTY_CELL_HASH,
            old_depth: 0,
            new_depth: 0,
            old: empty_cell.clone(),
            new: empty_cell,
        }
    }
}

impl<C: CellFamily> Load<'_, C> for MerkleUpdate<C> {
    fn load_from(s: &mut CellSlice<C>) -> Option<Self> {
        if !s.has_remaining(Self::BITS, Self::REFS) {
            return None;
        }

        if s.get_u8(0)? != CellType::MerkleUpdate.to_byte() {
            return None;
        }

        let res = Self {
            old_hash: s.get_u256(8)?,
            new_hash: s.get_u256(8 + 256)?,
            old_depth: s.get_u16(8 + 256 * 2)?,
            new_depth: s.get_u16(8 + 256 * 2 + 16)?,
            old: s.get_reference_cloned(0)?,
            new: s.get_reference_cloned(1)?,
        };
        if res.old.as_ref().hash(0) == &res.old_hash
            && res.old.as_ref().depth(0) == res.old_depth
            && res.new.as_ref().hash(0) == &res.new_hash
            && res.new.as_ref().depth(0) == res.new_depth
            && s.try_advance(Self::BITS, Self::REFS)
        {
            Some(res)
        } else {
            None
        }
    }
}

impl<C: CellFamily> Store<C> for MerkleUpdate<C> {
    fn store_into(&self, b: &mut CellBuilder<C>) -> bool {
        if !b.has_capacity(Self::BITS, Self::REFS) {
            return false;
        }
        let old_level_mask = self.old.as_ref().level_mask();
        let new_level_mask = self.new.as_ref().level_mask();
        b.set_level_mask((old_level_mask | new_level_mask).virtualize(1));
        b.set_exotic(true);
        b.store_u8(CellType::MerkleUpdate.to_byte())
            && b.store_u256(&self.old_hash)
            && b.store_u256(&self.new_hash)
            && b.store_u16(self.old_depth)
            && b.store_u16(self.new_depth)
            && b.store_reference(self.old.clone())
            && b.store_reference(self.new.clone())
    }
}

impl<C: CellFamily> MerkleUpdate<C> {
    pub const BITS: u16 = 8 + (256 + 16) * 2;
    pub const REFS: u8 = 2;
}

#[cfg(test)]
mod tests {
    use crate::{RcCellBuilder, RcCellFamily};

    use super::*;

    #[test]
    fn correct_store_load() {
        let default = MerkleUpdate::<RcCellFamily>::default();

        let mut builder = RcCellBuilder::new();
        assert!(default.store_into(&mut builder));
        let cell = builder.build().unwrap();

        let parsed = MerkleUpdate::load_from(&mut cell.as_slice()).unwrap();
        assert_eq!(default, parsed);
    }
}
