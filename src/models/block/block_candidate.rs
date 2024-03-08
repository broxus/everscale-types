use crate::cell::*;

use super::BlockId;

/// Block candidate for validation
#[derive(Debug, Default, Clone, Copy, Eq, Hash, PartialEq, Ord, PartialOrd, Store)]
pub struct BlockCandidate {
    pub root_hash: HashBytes,
    pub file_hash: HashBytes,
}

impl From<BlockId> for BlockCandidate {
    fn from(block_id: BlockId) -> Self {
        Self {
            root_hash: block_id.root_hash,
            file_hash: block_id.file_hash,
        }
    }
}
