//! Blockchain config and params.

use crate::cell::*;
use crate::dict::Dict;
use crate::util::DisplayHash;

/// Blockchain config.
#[derive(Clone, Eq, PartialEq)]
pub struct BlockchainConfig<C: CellFamily> {
    /// Configuration contract address.
    pub address: CellHash,
    /// Configuration parameters.
    pub params: Dict<C, u32, CellContainer<C>>,
}

impl<C: CellFamily> std::fmt::Debug for BlockchainConfig<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BlockchainConfig")
            .field("address", &DisplayHash(&self.address))
            .field("params", &self.params)
            .finish()
    }
}

impl<C: CellFamily> Store<C> for BlockchainConfig<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, _: &mut dyn Finalizer<C>) -> bool {
        let params_root = match self.params.root() {
            Some(root) => root.clone(),
            None => return false,
        };
        builder.store_u256(&self.address) && builder.store_reference(params_root)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for BlockchainConfig<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            address: slice.load_u256()?,
            params: Dict::from(Some(slice.load_reference_cloned()?)),
        })
    }
}
