//! Common ABI implementation.

use std::str::FromStr;

pub use self::contract::{
    Contract, Event, EventBuilder, ExternalInput, Function, FunctionBuilder, UnsignedBody,
    UnsignedExternalMessage,
};
pub use self::signature::{extend_signature_with_id, sign_with_signature_id};
pub use self::traits::{
    FromAbi, FromPlainAbi, IntoAbi, IntoPlainAbi, WithAbiType, WithPlainAbiType,
};
pub use self::ty::{AbiHeaderType, AbiType, NamedAbiType, PlainAbiType};
pub use self::value::{AbiHeader, AbiValue, NamedAbiValue, PlainAbiValue};

pub mod error;

mod contract;
mod signature;
mod traits;
mod ty;
mod value;

#[cfg(test)]
mod tests;

/// ABI version.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct AbiVersion {
    /// Major version component.
    pub major: u8,
    /// Minor version component.
    pub minor: u8,
}

impl AbiVersion {
    /// A legacy ABI version.
    pub const V1_0: Self = Self::new(1, 0);
    /// A base version of an ABI 2.
    pub const V2_0: Self = Self::new(2, 0);
    /// A base version with strings and refs.
    pub const V2_1: Self = Self::new(2, 1);
    /// Same as 2.1 but with a more compact address serialization.
    pub const V2_2: Self = Self::new(2, 2);
    /// Same as 2.2 but uses an address during signing.
    pub const V2_3: Self = Self::new(2, 3);

    /// Creates an ABI version from components.
    pub const fn new(major: u8, minor: u8) -> Self {
        Self { major, minor }
    }
}

impl FromStr for AbiVersion {
    type Err = error::ParseAbiVersionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (major, minor) = ok!(s
            .split_once('.')
            .ok_or(error::ParseAbiVersionError::InvalidFormat));

        Ok(Self {
            major: ok!(major
                .parse()
                .map_err(error::ParseAbiVersionError::InvalidComponent)),
            minor: ok!(minor
                .parse()
                .map_err(error::ParseAbiVersionError::InvalidComponent)),
        })
    }
}

impl std::fmt::Display for AbiVersion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.major, self.minor)
    }
}
