use std::borrow::Borrow;

use crate::cell::*;
use crate::dict::{self, AugDict, AugDictSkipValue};
use crate::error::*;
use crate::util::{CustomClone, CustomDebug, CustomEq};

use crate::models::currency::CurrencyCollection;
use crate::models::ShardAccount;

/// A dictionary of account states.
#[derive(CustomDebug, CustomClone, CustomEq, Store, Load)]
pub struct ShardAccounts<C: CellFamily>(AugDict<C, CellHash, DepthBalanceInfo<C>, ShardAccount<C>>);

impl<C> ShardAccounts<C>
where
    for<'c> C: CellFamily + 'c,
{
    /// Returns the account state corresponding to the key.
    ///
    /// Key is serialized using the default finalizer.
    pub fn get<'a: 'b, 'b, Q>(&'a self, key: Q) -> Result<Option<ShardAccount<C>>, Error>
    where
        Q: Borrow<CellHash> + 'b,
        C: DefaultFinalizer,
    {
        self.get_ext(key, &mut C::default_finalizer())
    }

    /// Returns the account state corresponding to the key.
    ///
    /// Key is serialized using the provided finalizer.
    pub fn get_ext<'a: 'b, 'b, Q>(
        &'a self,
        key: Q,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Result<Option<ShardAccount<C>>, Error>
    where
        Q: Borrow<CellHash> + 'b,
    {
        fn get_ext_impl<C>(
            dict: &ShardAccounts<C>,
            key: &CellHash,
            finalizer: &mut dyn Finalizer<C>,
        ) -> Result<Option<ShardAccount<C>>, Error>
        where
            for<'c> C: CellFamily + 'c,
        {
            match dict.get_raw_ext(key, finalizer) {
                Ok(Some(mut value)) => {
                    if DepthBalanceInfo::skip_value(&mut value) {
                        if let Some(value) = ShardAccount::<C>::load_from(&mut value) {
                            return Ok(Some(value));
                        }
                    }
                    Err(Error::CellUnderflow)
                }
                Ok(None) => Ok(None),
                Err(e) => Err(e),
            }
        }

        get_ext_impl(self, key.borrow(), finalizer)
    }

    /// Returns the raw value (with augmentation) corresponding to the key.
    ///
    /// Key is serialized using the default finalizer.
    pub fn get_raw<'a: 'b, 'b, Q>(&'a self, key: Q) -> Result<Option<CellSlice<'a, C>>, Error>
    where
        Q: Borrow<CellHash> + 'b,
        C: DefaultFinalizer,
    {
        self.0.dict().get_raw_ext(key, &mut C::default_finalizer())
    }

    /// Returns the raw value (with augmentation) corresponding to the key.
    ///
    /// Key is serialized using the provided finalizer.
    pub fn get_raw_ext<'a: 'b, 'b, Q>(
        &'a self,
        key: Q,
        finalizer: &mut dyn Finalizer<C>,
    ) -> Result<Option<CellSlice<'a, C>>, Error>
    where
        Q: Borrow<CellHash>,
    {
        self.0.dict().get_raw_ext(key, finalizer)
    }

    /// Returns `true` if the dictionary contains a state for the specified account id.
    pub fn contains_account<Q>(&self, key: Q) -> Result<bool, Error>
    where
        Q: Borrow<CellHash>,
        C: DefaultFinalizer,
    {
        self.0.dict().contains_key(key)
    }

    /// Gets an iterator over the entries of the shard accounts (without augmentation),
    /// sorted by account id. The iterator element is `Result<(CellHash, ShardAccount<C>)>`.
    ///
    /// If the dict is invalid, finishes after the first invalid element, returning an error.
    pub fn iter(&self) -> ShardAccountsIter<'_, C> {
        ShardAccountsIter::new(self.0.dict().root())
    }

    /// Gets an iterator over the raw entries of the shard accounts, sorted by account id.
    /// The iterator element is `Result<(CellHash, CellSlice<C>)>`.
    ///
    /// If the dict is invalid, finishes after the first invalid element, returning an error.
    pub fn raw_iter(&self) -> ShardAccountsRawIter<'_, C> {
        ShardAccountsRawIter::new(self.0.dict().root())
    }
}

/// Intermediate balance info.
#[derive(CustomDebug, CustomClone, CustomEq)]
pub struct DepthBalanceInfo<C: CellFamily> {
    /// Depth for which the balance was calculated.
    pub split_depth: u8,
    /// Total balance for a subtree.
    pub balance: CurrencyCollection<C>,
}

impl<C: CellFamily> DepthBalanceInfo<C> {
    const SPLIT_DEPTH_BITS: u16 = 5;

    /// Returns `true` if the split depth is valid.
    #[inline]
    pub const fn is_valid(&self) -> bool {
        self.split_depth <= 30
    }
}

impl<C: CellFamily> Store<C> for DepthBalanceInfo<C> {
    fn store_into(&self, builder: &mut CellBuilder<C>, finalizer: &mut dyn Finalizer<C>) -> bool {
        self.is_valid()
            && builder.store_small_uint(self.split_depth, Self::SPLIT_DEPTH_BITS)
            && self.balance.store_into(builder, finalizer)
    }
}

impl<'a, C: CellFamily> Load<'a, C> for DepthBalanceInfo<C> {
    fn load_from(slice: &mut CellSlice<'a, C>) -> Option<Self> {
        let result = Self {
            split_depth: slice.load_small_uint(Self::SPLIT_DEPTH_BITS)?,
            balance: CurrencyCollection::load_from(slice)?,
        };
        result.is_valid().then_some(result)
    }
}

impl<'a, C: CellFamily> AugDictSkipValue<'a, C> for DepthBalanceInfo<C> {
    fn skip_value(slice: &mut CellSlice<'a, C>) -> bool {
        slice.try_advance(5, 0) && CurrencyCollection::<C>::skip_value(slice)
    }
}

/// An iterator over the entries of a [`ShardAccounts`] (without augmentation).
///
/// This struct is created by the [`iter`] method on [`ShardAccounts`].
/// See its documentation for more.
///
/// [`iter`]: ShardAccounts::iter
#[derive(CustomClone)]
pub struct ShardAccountsIter<'a, C: CellFamily> {
    inner: dict::RawIter<'a, C>,
}

impl<'a, C> ShardAccountsIter<'a, C>
where
    for<'c> C: CellFamily + 'c,
{
    fn new(dict: &'a Option<CellContainer<C>>) -> Self {
        Self {
            inner: dict::RawIter::new(dict, 256),
        }
    }
}

impl<'a, C> Iterator for ShardAccountsIter<'a, C>
where
    for<'c> C: CellFamily + 'c,
{
    type Item = Result<(CellHash, ShardAccount<C>), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.inner.next()? {
            Ok((key, mut value)) => {
                if DepthBalanceInfo::skip_value(&mut value) {
                    if let Some(value) = ShardAccount::<C>::load_from(&mut value) {
                        return Some(Ok((key.raw_data()[..32].try_into().unwrap(), value)));
                    }
                }

                Err(self.inner.finish(Error::CellUnderflow))
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
#[derive(CustomClone)]
pub struct ShardAccountsRawIter<'a, C: CellFamily> {
    inner: dict::RawIter<'a, C>,
}

impl<'a, C> ShardAccountsRawIter<'a, C>
where
    for<'c> C: CellFamily + 'c,
{
    fn new(dict: &'a Option<CellContainer<C>>) -> Self {
        Self {
            inner: dict::RawIter::new(dict, 256),
        }
    }
}

impl<'a, C> Iterator for ShardAccountsRawIter<'a, C>
where
    for<'c> C: CellFamily + 'c,
{
    type Item = Result<(CellHash, CellSlice<'a, C>), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.inner.next()? {
            Ok((key, value)) => Ok((key.raw_data()[..32].try_into().unwrap(), value)),
            Err(e) => Err(e),
        })
    }
}
