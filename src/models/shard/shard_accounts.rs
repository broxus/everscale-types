use std::borrow::Borrow;

use crate::cell::*;
use crate::dict::{self, AugDict, AugDictSkipValue};
use crate::error::*;

use crate::models::currency::CurrencyCollection;
use crate::models::ShardAccount;

/// A dictionary of account states.
#[derive(Debug, Clone, Eq, PartialEq, Store, Load)]
pub struct ShardAccounts(AugDict<HashBytes, DepthBalanceInfo, ShardAccount>);

impl ShardAccounts {
    /// Returns the account state corresponding to the key.
    pub fn get<'a: 'b, 'b, Q>(&'a self, key: Q) -> Result<Option<ShardAccount>, Error>
    where
        Q: Borrow<HashBytes> + 'b,
    {
        fn get_impl(dict: &ShardAccounts, key: &HashBytes) -> Result<Option<ShardAccount>, Error> {
            match dict.get_raw(key) {
                Ok(Some(mut value)) => {
                    if DepthBalanceInfo::skip_value(&mut value) {
                        match ShardAccount::load_from(&mut value) {
                            Ok(value) => Ok(Some(value)),
                            Err(e) => Err(e),
                        }
                    } else {
                        Err(Error::CellUnderflow)
                    }
                }
                Ok(None) => Ok(None),
                Err(e) => Err(e),
            }
        }

        get_impl(self, key.borrow())
    }

    /// Returns the raw value (with augmentation) corresponding to the key.
    pub fn get_raw<'a: 'b, 'b, Q>(&'a self, key: Q) -> Result<Option<CellSlice<'a>>, Error>
    where
        Q: Borrow<HashBytes> + 'b,
    {
        self.0.dict().get_raw(key)
    }

    /// Returns `true` if the dictionary contains a state for the specified account id.
    pub fn contains_account<Q>(&self, key: Q) -> Result<bool, Error>
    where
        Q: Borrow<HashBytes>,
    {
        self.0.dict().contains_key(key)
    }

    /// Gets an iterator over the entries of the shard accounts (without augmentation),
    /// sorted by account id. The iterator element is `Result<(HashBytes, ShardAccount)>`.
    ///
    /// If the dict is invalid, finishes after the first invalid element, returning an error.
    pub fn iter(&self) -> ShardAccountsIter<'_> {
        ShardAccountsIter::new(self.0.dict().root())
    }

    /// Gets an iterator over the raw entries of the shard accounts, sorted by account id.
    /// The iterator element is `Result<(HashBytes, CellSlice)>`.
    ///
    /// If the dict is invalid, finishes after the first invalid element, returning an error.
    pub fn raw_iter(&self) -> ShardAccountsRawIter<'_> {
        ShardAccountsRawIter::new(self.0.dict().root())
    }
}

/// Intermediate balance info.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct DepthBalanceInfo {
    /// Depth for which the balance was calculated.
    pub split_depth: u8,
    /// Total balance for a subtree.
    pub balance: CurrencyCollection,
}

impl DepthBalanceInfo {
    const SPLIT_DEPTH_BITS: u16 = 5;

    /// Returns `true` if the split depth is valid.
    #[inline]
    pub const fn is_valid(&self) -> bool {
        self.split_depth <= 30
    }
}

impl Store for DepthBalanceInfo {
    fn store_into(
        &self,
        builder: &mut CellBuilder,
        finalizer: &mut dyn Finalizer,
    ) -> Result<(), Error> {
        if !self.is_valid() {
            return Err(Error::IntOverflow);
        }
        ok!(builder.store_small_uint(self.split_depth, Self::SPLIT_DEPTH_BITS));
        self.balance.store_into(builder, finalizer)
    }
}

impl<'a> Load<'a> for DepthBalanceInfo {
    fn load_from(slice: &mut CellSlice<'a>) -> Result<Self, Error> {
        let result = Self {
            split_depth: ok!(slice.load_small_uint(Self::SPLIT_DEPTH_BITS)),
            balance: ok!(CurrencyCollection::load_from(slice)),
        };
        if result.is_valid() {
            Ok(result)
        } else {
            Err(Error::IntOverflow)
        }
    }
}

impl<'a> AugDictSkipValue<'a> for DepthBalanceInfo {
    fn skip_value(slice: &mut CellSlice<'a>) -> bool {
        slice.try_advance(5, 0) && CurrencyCollection::skip_value(slice)
    }
}

/// An iterator over the entries of a [`ShardAccounts`] (without augmentation).
///
/// This struct is created by the [`iter`] method on [`ShardAccounts`].
/// See its documentation for more.
///
/// [`iter`]: ShardAccounts::iter
#[derive(Clone)]
pub struct ShardAccountsIter<'a> {
    inner: dict::RawIter<'a>,
}

impl<'a> ShardAccountsIter<'a> {
    fn new(dict: &'a Option<Cell>) -> Self {
        Self {
            inner: dict::RawIter::new(dict, 256),
        }
    }
}

impl<'a> Iterator for ShardAccountsIter<'a> {
    type Item = Result<(HashBytes, ShardAccount), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.inner.next()? {
            Ok((key, mut value)) => {
                let e = if DepthBalanceInfo::skip_value(&mut value) {
                    match ShardAccount::load_from(&mut value) {
                        Ok(value) => {
                            return Some(Ok((
                                HashBytes(key.raw_data()[..32].try_into().unwrap()),
                                value,
                            )))
                        }
                        Err(e) => e,
                    }
                } else {
                    Error::CellUnderflow
                };

                Err(self.inner.finish(e))
            }
            Err(e) => Err(e),
        })
    }
}

/// An iterator over the raw entries of a [`ShardAccounts`].
///
/// This struct is created by the [`raw_iter`] method on [`ShardAccounts`].
/// See its documentation for more.
///
/// [`raw_iter`]: ShardAccounts::raw_iter
#[derive(Clone)]
pub struct ShardAccountsRawIter<'a> {
    inner: dict::RawIter<'a>,
}

impl<'a> ShardAccountsRawIter<'a> {
    fn new(dict: &'a Option<Cell>) -> Self {
        Self {
            inner: dict::RawIter::new(dict, 256),
        }
    }
}

impl<'a> Iterator for ShardAccountsRawIter<'a> {
    type Item = Result<(HashBytes, CellSlice<'a>), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.inner.next()? {
            Ok((key, value)) => Ok((HashBytes(key.raw_data()[..32].try_into().unwrap()), value)),
            Err(e) => Err(e),
        })
    }
}
