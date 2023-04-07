//! The `everscale-types` prelude.
//!
//! This brings into scope a number of traits and commonly used type aliases.

pub use crate::boc::Boc;
pub use crate::cell::rc::{RcCell, RcCellFamily};
pub use crate::cell::sync::{ArcCell, ArcCellFamily};
pub use crate::cell::{
    Cell, CellBuilder, CellDescriptor, CellFamily, CellHash, CellSlice, CellType, Load, Store,
    UsageTree, UsageTreeMode,
};
pub use crate::dict::{Dict, RawDict};

/// BOC (Bag Of Cells) helper for the `Arc` family of cells.
pub type ArcBoc = Boc<ArcCellFamily>;
/// BOC (Bag Of Cells) helper for the `Rc` family of cells.
pub type RcBoc = Boc<RcCellFamily>;

/// Cell builder for the `Arc` family of cells.
pub type ArcCellBuilder = CellBuilder<ArcCellFamily>;
/// Cell builder for the `Rc` family of cells.
pub type RcCellBuilder = CellBuilder<RcCellFamily>;

/// A read-only view for the `Arc` family of cells.
pub type ArcCellSlice<'a> = CellSlice<'a, ArcCellFamily>;
/// A read-only view for the `Rc` family of cells.
pub type RcCellSlice<'a> = CellSlice<'a, RcCellFamily>;

/// Usage tree for the `Arc` family of cells.
pub type ArcUsageTree = UsageTree<ArcCellFamily>;
/// Usage tree for the `Rc` family of cells.
pub type RcUsageTree = UsageTree<RcCellFamily>;

/// A typed ordinary dictionary with fixed length keys for the `Arc` family of cells.
pub type ArcDict<K, V> = Dict<ArcCellFamily, K, V>;
/// A typed ordinary dictionary with fixed length keys for the `Rc` family of cells.
pub type RcDict<K, V> = Dict<RcCellFamily, K, V>;

/// An ordinary dictionary with fixed length keys for the `Arc` family of cells.
pub type ArcRawDict<const N: u16> = RawDict<ArcCellFamily, N>;
/// An ordinary dictionary with fixed length keys for the `Rc` family of cells.
pub type RcRawDict<const N: u16> = RawDict<RcCellFamily, N>;
