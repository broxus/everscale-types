use crate::cell::*;
use crate::dict::Dict;
use crate::util::*;

use super::{BlockId, BlockSignature};
use crate::models::shard::ValidatorBaseInfo;

/// Typed block proof.
#[derive(CustomClone, CustomDebug, CustomEq)]
pub struct BlockProof<C: CellFamily> {
    /// Id of the related block.
    pub proof_for: BlockId,
    /// Merkle proof cell.
    pub root: CellContainer<C>,
    /// Optional references for the masterchain block.
    pub signatures: Option<BlockSignatures<C>>,
}

impl<C: CellFamily> BlockProof<C> {
    const TAG: u8 = 0xc3;
}

impl<C: CellFamily> Store<C> for BlockProof<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        let child_cell = match &self.signatures {
            Some(signatures) => {
                let mut builder = CellBuilder::<C>::new();
                if !signatures.store_into(&mut builder, finalizer) {
                    return false;
                }

                if let Some(cell) = builder.build_ext(finalizer) {
                    Some(cell)
                } else {
                    return false;
                }
            }
            None => None,
        };

        builder.store_u8(Self::TAG)
            && self.proof_for.store_into(builder, finalizer)
            && builder.store_reference(self.root.clone())
            && match child_cell {
                Some(cell) => builder.store_bit_one() && builder.store_reference(cell),
                None => builder.store_bit_zero(),
            }
    }
}

impl<'a, C: CellFamily> Load<'a, C> for BlockProof<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        if slice.load_u8()? != Self::TAG {
            return None;
        }
        Some(Self {
            proof_for: BlockId::load_from(slice)?,
            root: slice.load_reference_cloned()?,
            signatures: if slice.load_bit()? {
                Some(slice.load_reference()?.parse::<BlockSignatures<C>>()?)
            } else {
                None
            },
        })
    }
}

/// Masterchain block signatures.
#[derive(CustomClone, CustomDebug, CustomEq, Store, Load)]
#[tlb(tag = "#11")]
pub struct BlockSignatures<C: CellFamily> {
    /// Brief validator basic info.
    pub validator_info: ValidatorBaseInfo,
    /// Total number of signatures.
    pub signature_count: u32,
    /// Total validators weight.
    pub total_weight: u64,
    /// Block signatures from all signers.
    pub signatures: Dict<C, u16, BlockSignature>,
}
