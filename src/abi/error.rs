//! ABI related error types.

/// Error type for ABI version parsing related errors.
#[derive(Debug, Clone, thiserror::Error)]
pub enum ParseAbiVersionError {
    /// Expected a dot separated major and minor components.
    #[error("invalid format")]
    InvalidFormat,
    /// Failed to parse version component as number.
    #[error("invalid component")]
    InvalidComponent(#[source] std::num::ParseIntError),
}

/// Error type for ABI type parsing related errors.
#[derive(Debug, Clone, thiserror::Error)]
pub enum ParseAbiTypeError {
    /// Error while parsing array type.
    #[error("invalid array type")]
    InvalidArrayType,
    /// Error while parsing array length.
    #[error("invalid array length")]
    InvalidArrayLength(#[source] std::num::ParseIntError),
    /// Error while parsing integer bit length.
    #[error("invalid integer bit length")]
    InvalidBitLen(#[source] std::num::ParseIntError),
    /// Error while parsing varint or fixedbytes byte length.
    #[error("invalid byte length")]
    InvalidByteLen(#[source] std::num::ParseIntError),
    /// Expected type to be terminated with ')'.
    #[error("unterminated inner type")]
    UnterminatedInnerType,
    /// Expected value type for map.
    #[error("map value type not found")]
    ValueTypeNotFound,
    /// Invalid ABI type.
    #[error("unknown type")]
    UnknownType,
}

/// Error type for named ABI type parsing related errors.
#[derive(Debug, Clone, thiserror::Error)]
pub enum ParseNamedAbiTypeError {
    /// Error while parsing ABI type.
    #[error("invalid type `{ty}`: {error}")]
    InvalidType {
        /// Parsed ABI type.
        ty: Box<str>,
        /// ABI type parsing error.
        #[source]
        error: ParseAbiTypeError,
    },
    /// Components array was not expected.
    #[error("unexpected components for `{ty}`")]
    UnexpectedComponents {
        /// Parsed ABI type.
        ty: Box<str>,
    },
    /// Expected components array for tuple.
    #[error("expected components for `{ty}`")]
    ExpectedComponents {
        /// Parsed ABI type.
        ty: Box<str>,
    },
}

/// Error type for ABI values unpacking related errors.
#[derive(Debug, Clone, thiserror::Error)]
pub enum AbiError {
    /// Expected a different value type.
    #[error("expected ABI type `{expected}`, got `{ty}`")]
    TypeMismatch {
        /// A full signature of the expected type.
        expected: Box<str>,
        /// A full signature of the received type.
        ty: Box<str>,
    },
}
