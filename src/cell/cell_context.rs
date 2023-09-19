use crate::cell::{Cell, CellFamily, CellParts, DefaultFinalizer, DynCell, Finalizer};
use crate::error::Error;

/// Cell family with a noop cell context.
pub trait DefaultCellContext: CellFamily {
    /// The default cell context type.
    type CellContext: CellContext;

    /// Creates a default cell context.
    fn default_cell_context() -> Self::CellContext;
}

/// Dictionary insertion mode.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(u8)]
pub enum LoadMode {
    /// Do not modify the default behavior.
    Noop = 0b00,
    /// Count the cost of loading the cell.
    UseGas = 0b01,
    /// Resolve exotic cells such as libraries or merkle stuff.
    Resolve = 0b10,
    /// Both `UseGas` and `Resolve`.
    Full = 0b11,
}

impl LoadMode {
    /// Returns `true` if this mode requires gas accounting.
    #[inline]
    pub const fn use_gas(self) -> bool {
        self as u8 & 0b01 != 0
    }

    /// Returns `true` if exotic cells are resolved in this mode.
    #[inline]
    pub const fn resolve(self) -> bool {
        self as u8 & 0b10 != 0
    }
}

/// Gas accounting and resolcing exotic cells.
pub trait CellContext: Finalizer {
    /// Upcasts `dyn CellContext` to `dyn Finalizer`.
    fn as_finalizer(&mut self) -> &mut dyn Finalizer;

    /// Resolve an owned cell.
    fn load_cell(&mut self, cell: Cell, mode: LoadMode) -> Result<Cell, Error>;

    /// Resolve a cell reference.
    fn load_dyn_cell<'a>(
        &mut self,
        cell: &'a DynCell,
        mode: LoadMode,
    ) -> Result<&'a DynCell, Error>;
}

/// Default cell context without gas accounting and cells resolution.
///
/// NOTE: Wraps default cell finalizer to reduce generated code size.
#[derive(Default)]
#[repr(transparent)]
pub struct NoopCellContext(<Cell as DefaultFinalizer>::Finalizer);

impl Finalizer for NoopCellContext {
    #[inline]
    fn finalize_cell(&mut self, cell: CellParts<'_>) -> Result<Cell, Error> {
        self.0.finalize_cell(cell)
    }
}

impl CellContext for NoopCellContext {
    #[inline]
    fn as_finalizer(&mut self) -> &mut dyn Finalizer {
        // SAFETY: NoopCellContext is #[repr(transparent)]
        unsafe { &mut *(self as *mut Self as *mut <Cell as DefaultFinalizer>::Finalizer) }
    }

    #[inline]
    fn load_cell(&mut self, cell: Cell, _: LoadMode) -> Result<Cell, Error> {
        Ok(cell)
    }

    #[inline]
    fn load_dyn_cell<'a>(&mut self, cell: &'a DynCell, _: LoadMode) -> Result<&'a DynCell, Error> {
        Ok(cell)
    }
}

impl DefaultCellContext for Cell {
    type CellContext = NoopCellContext;

    #[inline]
    fn default_cell_context() -> Self::CellContext {
        NoopCellContext(Cell::default_finalizer())
    }
}
