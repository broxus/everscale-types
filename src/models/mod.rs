//! Blockchain models.

pub use account::*;
pub use block::*;
pub use config::*;
pub use currency::*;
pub use global_version::*;
pub use message::*;
pub use shard::*;
pub use transaction::*;
pub use vm::*;

pub mod account;
pub mod block;
pub mod config;
pub mod currency;
pub mod global_version;
pub mod message;
pub mod shard;
pub mod transaction;
pub mod vm;

#[cfg(feature = "sync")]
#[doc(hidden)]
mod __checks {
    use super::*;

    assert_impl_all!(crate::cell::Lazy<Message>: Send, Sync);
    assert_impl_all!(Account: Send, Sync);
    assert_impl_all!(Block: Send, Sync);
    assert_impl_all!(Message: Send, Sync);
    assert_impl_all!(Transaction: Send, Sync);
}
