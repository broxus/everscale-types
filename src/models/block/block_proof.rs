use crate::cell::*;
use crate::dict::Dict;
use crate::error::Error;
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
    fn store_into(
        &self,
        builder: &mut CellBuilder<C>,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Result<(), Error> {
        let child_cell = match &self.signatures {
            Some(signatures) => {
                let mut builder = CellBuilder::<C>::new();
                ok!(signatures.store_into(&mut builder, finalizer));
                Some(ok!(builder.build_ext(finalizer)))
            }
            None => None,
        };

        ok!(builder.store_u8(Self::TAG));
        ok!(self.proof_for.store_into(builder, finalizer));
        ok!(builder.store_reference(self.root.clone()));
        match child_cell {
            Some(cell) => {
                ok!(builder.store_bit_one());
                builder.store_reference(cell)
            }
            None => builder.store_bit_zero(),
        }
    }
}

impl<'a, C: CellFamily> Load<'a, C> for BlockProof<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Result<Self, Error> {
        match slice.load_u8() {
            Ok(Self::TAG) => {}
            Ok(_) => return Err(Error::InvalidTag),
            Err(e) => return Err(e),
        }

        Ok(Self {
            proof_for: ok!(BlockId::load_from(slice)),
            root: ok!(slice.load_reference_cloned()),
            signatures: if ok!(slice.load_bit()) {
                match slice.load_reference() {
                    Ok(cell) => Some(ok!(cell.parse::<BlockSignatures<C>>())),
                    Err(e) => return Err(e),
                }
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
