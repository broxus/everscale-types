use everscale_types::cell::{DefaultFinalizer, Finalizer};
use std::ops::BitOr;

use crate::cell::{Cell, CellParts};
use crate::prelude::DynCell;

/// Cell may be re
#[derive(Copy, Clone)]
pub struct LoadCellMode(u8);

impl LoadCellMode {
    /// Do nothing, return value as it is
    pub const NOOP: LoadCellMode = LoadCellMode(0b_0000_0000);
    /// Resolve exotic cells such as libraries or merkle stuff
    pub const RESOLVE: LoadCellMode = LoadCellMode(0b_0000_0001);
    /// Sometimes gas should not be used, eg we read cell the second time as an implementation detail
    pub const USE_GAS: LoadCellMode = LoadCellMode(0b_0000_0010);

    /// Determine the flag from combination of others
    pub fn contains(&self, other: Self) -> bool {
        (self.0 & other.0) == other.0
    }
}

impl BitOr<LoadCellMode> for LoadCellMode {
    type Output = Self;

    fn bitor(self, rhs: LoadCellMode) -> Self::Output {
        LoadCellMode(self.0 | rhs.0)
    }
}

/// Gas accounting and resolving exotic cells
pub trait CellContext: Finalizer {
    /// Errors defined on user side will be returned from some methods implemented in this crate
    type Error: From<crate::error::Error>;

    /// Resolve cloned cell consuming gas
    fn load_cell(&mut self, cell: Cell, mode: LoadCellMode) -> Result<Cell, Self::Error>;

    /// Resolve dyn cell consuming gas
    fn load_dyn_cell<'a>(
        &mut self,
        dyn_cell: &'a DynCell,
        mode: LoadCellMode,
    ) -> Result<&'a DynCell, Self::Error>;
}

/// No-op dummy
impl CellContext for () {
    type Error = crate::error::Error;

    fn load_cell(&mut self, cell: Cell, _: LoadCellMode) -> Result<Cell, Self::Error> {
        Ok(cell)
    }

    fn load_dyn_cell<'a>(
        &mut self,
        dyn_cell: &'a DynCell,
        _: LoadCellMode,
    ) -> Result<&'a DynCell, Self::Error> {
        Ok(dyn_cell)
    }
}

impl Finalizer for () {
    fn finalize_cell(&mut self, cell: CellParts<'_>) -> Result<Cell, crate::error::Error> {
        Cell::default_finalizer().finalize_cell(cell)
    }
}
