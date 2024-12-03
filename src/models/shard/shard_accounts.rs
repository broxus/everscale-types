use crate::cell::*;
use crate::dict::{AugDict, AugDictExtra};
use crate::error::*;

use crate::models::currency::CurrencyCollection;
use crate::models::ShardAccount;

/// A dictionary of account states.
pub type ShardAccounts = AugDict<HashBytes, DepthBalanceInfo, ShardAccount>;

/// Intermediate balance info.
#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct DepthBalanceInfo {
    /// Total number of accounts in a subtree.
    pub count: u32,
    /// Total balance for a subtree.
    pub balance: CurrencyCollection,
}

impl DepthBalanceInfo {
    /// Returns `true`.
    #[inline]
    pub const fn is_valid(&self) -> bool {
        true
    }
}

impl AugDictExtra for DepthBalanceInfo {
    fn comp_add(
        left: &mut CellSlice,
        right: &mut CellSlice,
        b: &mut CellBuilder,
        cx: &mut dyn CellContext,
    ) -> Result<(), Error> {
        let left = ok!(Self::load_from(left));
        let right = ok!(Self::load_from(right));
        Self {
            count: left
                .count
                .checked_add(right.count)
                .ok_or(Error::IntOverflow)?,
            balance: ok!(left.balance.checked_add(&right.balance)),
        }
        .store_into(b, cx)
    }
}

impl Store for DepthBalanceInfo {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        context: &mut dyn CellContext,
    ) -> Result<(), Error> {
        if !self.is_valid() {
            return Err(Error::IntOverflow);
        }
        ok!(builder.store_u32(self.count));
        self.balance.store_into(builder, context)
    }
}

impl<'a> Load<'a> for DepthBalanceInfo {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let result = Self {
            count: ok!(slice.load_u32()),
            balance: ok!(CurrencyCollection::load_from(slice)),
        };
        if result.is_valid() {
            Ok(result)
        } else {
            Err(Error::IntOverflow)
        }
    }
}
