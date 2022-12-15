use std::mem::MaybeUninit;
use std::ops::Deref;

use bumpalo::Bump;

use crate::cell::finalizer::{CellParts, Finalizer};
use crate::cell::{
    Cell, CellContainer, CellDescriptor, CellFamily, CellHash, CellTreeStats, EMPTY_CELL_HASH,
    MAX_REF_COUNT,
};

#[derive(Clone, Copy)]
pub struct PtrCellFamily<'a> {
    data: &'a [u8],
}

impl<'a> PtrCellFamily<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        Self { data }
    }

    pub fn create_finalizer(&self) -> PtrCellFinalizer<'a> {
        PtrCellFinalizer {
            _data: self.data,
            cells: Default::default(),
            hashes: Default::default(),
            with_hashes: 0,
            total_wased: 0,
        }
    }
}

impl<'a> CellFamily for PtrCellFamily<'a> {
    type Container<T: ?Sized> = PtrCell<'a>;

    fn empty_cell() -> CellContainer<Self> {
        PtrCell(&EMPTY_CELL as *const _)
    }
}

pub struct PtrCellFinalizer<'a> {
    _data: &'a [u8],
    cells: Bump,
    hashes: Bump,
    with_hashes: usize,
    total_wased: u64,
}

impl std::fmt::Debug for PtrCellFinalizer<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PtrCellFinalizer")
            .field("cells", &format!("{} bytes", self.cells.allocated_bytes()))
            .field(
                "hashes",
                &format!("{} bytes", self.hashes.allocated_bytes()),
            )
            .field("with_hashes", &self.with_hashes)
            .field("total_wased", &self.total_wased)
            .finish()
    }
}

impl<'a> Finalizer<PtrCellFamily<'a>> for PtrCellFinalizer<'a> {
    fn finalize_cell(
        &mut self,
        ctx: CellParts<PtrCellFamily<'a>>,
    ) -> Option<CellContainer<PtrCellFamily<'a>>> {
        if ctx.descriptor.store_hashes() {
            self.with_hashes += 1;
            self.total_wased += (2 + 32) * ctx.descriptor.hash_count() as u64;
        }

        let ctx: CellParts<PtrCellFamily<'static>> = unsafe { std::mem::transmute(ctx) };
        let hashes = ctx.compute_hashes()?;
        let hashes = self.hashes.alloc_slice_copy(&hashes);

        let cell = self.cells.alloc(GenericCell::<'a> {
            bit_len: ctx.bit_len,
            stats: ctx.stats,
            hashes: unsafe { std::mem::transmute(hashes) },
            descriptor: ctx.descriptor,
            references: unsafe { ctx.references.into_inner() },
            data: unsafe { std::mem::transmute(ctx.data) },
        });
        Some(PtrCell(cell as *const _))
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct PtrCell<'a>(*const GenericCell<'a>);

impl<'a> Deref for PtrCell<'a> {
    type Target = dyn Cell<PtrCellFamily<'a>> + 'a;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<'a> AsRef<dyn Cell<PtrCellFamily<'a>> + 'a> for PtrCell<'a> {
    #[inline]
    fn as_ref(&self) -> &(dyn Cell<PtrCellFamily<'a>> + 'a) {
        unsafe { &*self.0 }
    }
}

struct GenericCell<'a> {
    bit_len: u16,
    stats: CellTreeStats,
    hashes: &'a [CellHashExt],
    descriptor: CellDescriptor,
    references: [MaybeUninit<PtrCell<'a>>; MAX_REF_COUNT],
    data: &'a [u8],
}

impl<'a> GenericCell<'a> {
    fn get_reference(&self, i: u8) -> Option<&PtrCell<'a>> {
        if i < self.descriptor.reference_count() {
            // SAFETY: Item is initialized
            let child = unsafe { self.references.get_unchecked(i as usize).assume_init_ref() };
            Some(child)
        } else {
            None
        }
    }
}

unsafe impl Sync for GenericCell<'static> {}

impl<'a> Cell<PtrCellFamily<'a>> for GenericCell<'a> {
    fn descriptor(&self) -> CellDescriptor {
        self.descriptor
    }

    fn data(&self) -> &[u8] {
        self.data
    }

    fn bit_len(&self) -> u16 {
        self.bit_len
    }

    fn reference(&self, index: u8) -> Option<&dyn Cell<PtrCellFamily<'a>>> {
        let ptr = self.get_reference(index)?;
        Some(ptr.as_ref())
    }

    fn reference_cloned(&self, index: u8) -> Option<CellContainer<PtrCellFamily<'a>>> {
        self.get_reference(index).copied()
    }

    fn hash(&self, mut index: u8) -> &CellHash {
        let level_mask = self.descriptor.level_mask();
        index = level_mask.hash_index(index);
        if self.descriptor.is_exotic()
            && self.descriptor.reference_count() == 0
            && !level_mask.is_empty()
        {
            let level = level_mask.level();
            if index != level {
                let offset = 2 + index as usize * 32;
                // SAFETY: Cell was created from a well-formed parts, so data is big enough
                return unsafe { &*(self.data.as_ptr().add(offset) as *const [u8; 32]) };
            } else {
                index = 0;
            }
        }

        let descr = unsafe { self.hashes.get_unchecked(index as usize) };
        &descr.0
    }

    fn depth(&self, mut index: u8) -> u16 {
        let level_mask = self.descriptor.level_mask();
        index = level_mask.hash_index(index);
        if self.descriptor.is_exotic()
            && self.descriptor.reference_count() == 0
            && !level_mask.is_empty()
        {
            let level = level_mask.level();
            if index != level {
                let offset = 2 + (level as usize * 32) + index as usize * 2;
                // SAFETY: Cell was created from a well-formed parts, so data is big enough
                let depth = unsafe { *(self.data.as_ptr().add(offset) as *const [u8; 2]) };
                return u16::from_be_bytes(depth);
            } else {
                index = 0;
            }
        }

        let descr = unsafe { self.hashes.get_unchecked(index as usize) };
        descr.1
    }

    fn stats(&self) -> CellTreeStats {
        self.stats
    }
}

static EMPTY_CELL: GenericCell<'static> = GenericCell {
    bit_len: 0,
    stats: CellTreeStats {
        bit_count: 0,
        cell_count: 1,
    },
    hashes: &[EMPTY_CELL_HASH_EXT],
    descriptor: CellDescriptor::new([0, 0]),
    references: [std::mem::MaybeUninit::uninit(); 4],
    data: &[],
};
static EMPTY_CELL_HASH_EXT: CellHashExt = (EMPTY_CELL_HASH, 0);

type CellHashExt = (CellHash, u16);
