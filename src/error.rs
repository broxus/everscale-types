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
