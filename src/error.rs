//! Common error types.

/// Error type for cell related errors.
#[derive(Debug, Copy, Clone, thiserror::Error)]
pub enum Error {
    /// There were not enough bits or refs in the cell slice.
    #[error("cell underflow")]
    CellUnderflow,
    /// There were not enough bits or refs capacity in the cell builder.
    #[error("cell overflow")]
    CellOverflow,
    /// Something tried to load a pruned branch cell.
    #[error("pruned branch access")]
    PrunedBranchAccess,
}

/// Error type for address parsing related errors.
#[derive(Debug, Copy, Clone, thiserror::Error)]
pub enum ParseAddrError {
    /// Tried to parse an empty string.
    #[error("cannot parse address from an empty string")]
    Empty,
    /// Workchain id is too large.
    #[error("workchain id is too large to fit in target type")]
    InvalidWorkchain,
    /// Invalid account id hex.
    #[error("cannot parse account id")]
    InvalidAccountId,
    /// Too many address parts.
    #[error("unexpected address part")]
    UnexpectedPart,
}

/// Error type for block id parsing related errors.
#[derive(Debug, Clone, Copy, thiserror::Error)]
pub enum ParseBlockIdError {
    /// Tried to parse an empty string.
    #[error("cannot parse block id from an empty string")]
    Empty,
    /// Workchain id is too large.
    #[error("cannot parse workchain id")]
    InvalidWorkchain,
    /// Invalid workchain or shard prefix.
    #[error("invalid shard id")]
    InvalidShardIdent,
    /// Invalid block seqno.
    #[error("cannot parse block seqno")]
    InvalidSeqno,
    /// Invalid root hash hex.
    #[error("cannot parse root hash")]
    InvalidRootHash,
    /// Invalid file hash hex.
    #[error("cannot parse file hash")]
    InvalidFileHash,
    /// Too many block id parts.
    #[error("unexpected block id part")]
    UnexpectedPart,
}
