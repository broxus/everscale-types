use everscale_types_proc::*;

use crate::cell::*;
use crate::dict::*;
use crate::num::*;

use crate::models::currency::CurrencyCollection;
use crate::models::ShardAccount;

/// A dictionary of account states.
#[derive(CustomDebug, CustomClone, CustomEq)]
pub struct ShardAccounts<C: CellFamily>(AugDict<C, CellHash, DepthBalanceInfo<C>, ShardAccount<C>>);

impl<C: CellFamily> Store<C> for ShardAccounts<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.0.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for ShardAccounts<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self(AugDict::load_from(slice)?))
    }
}

/// Intermediate balance info.
#[derive(CustomDebug, CustomClone, CustomEq)]
pub struct DepthBalanceInfo<C: CellFamily> {
    /// Depth for which the balance was calculated.
    pub split_depth: SplitDepth,
    /// Total balance for a subtree.
    pub balance: CurrencyCollection<C>,
}

impl<C: CellFamily> Store<C> for DepthBalanceInfo<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.split_depth.store_into(builder, finalizer)
            && self.balance.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for DepthBalanceInfo<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        Some(Self {
            split_depth: SplitDepth::load_from(slice)?,
            balance: CurrencyCollection::load_from(slice)?,
        })
    }
}
