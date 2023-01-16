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

#[derive(Debug, Copy, Clone, thiserror::Error)]
pub enum ParseAddrError {
    #[error("cannot parse address from an empty string")]
    Empty,
    #[error("workchain id is too large to fit in target type")]
    InvalidWorkchain,
    #[error("cannot parse account id")]
    InvalidAccountId,
    #[error("unexpected address part")]
    UnexpectedPart,
}
