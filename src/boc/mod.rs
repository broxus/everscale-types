#[derive(Copy, Clone, Eq, PartialEq)]
pub enum BocTag {
    Indexed,
    IndexedCrc32,
    Generic,
}

impl BocTag {
    pub const BOC_INDEXED_TAG: [u8; 4] = [0x68, 0xff, 0x65, 0xf3];
    pub const BOC_INDEXED_CRC32_TAG: [u8; 4] = [0xac, 0xc3, 0xa7, 0x28];
    pub const BOC_GENERIC_TAG: [u8; 4] = [0xb5, 0xee, 0x9c, 0x72];

    pub const fn to_bytes(self) -> [u8; 4] {
        match self {
            Self::Indexed => Self::BOC_INDEXED_TAG,
            Self::IndexedCrc32 => Self::BOC_INDEXED_CRC32_TAG,
            Self::Generic => Self::BOC_GENERIC_TAG,
        }
    }
}

/*


   pub fn deserialize(src: &[u8]) -> Option<Arc<Self>> {
       let mut index = Index {
           value_len: src.len(),
           offset: 0,
       };

       index.require(6)?;
       let flags = src[4];

       let has_index;
       let has_crc;
       let has_cache_bits;
       let ref_size;
       let supports_multiple_roots;
       match &src[0..4] {
           BOC_INDEXED_TAG => {
               has_index = false;
               has_crc = false;
               has_cache_bits = false;
               ref_size = flags as usize;
               supports_multiple_roots = false;
           }
           BOC_INDEXED_CRC32_TAG => {
               has_index = true;
               has_crc = true;
               has_cache_bits = false;
               ref_size = flags as usize;
               supports_multiple_roots = false;
           }
           BOC_GENERIC_TAG => {
               has_index = flags & 0b1000_0000 != 0;
               has_crc = flags & 0b0100_0000 != 0;
               has_cache_bits = flags & 0b0010_0000 != 0;
               ref_size = (flags & 0b0000_0111) as usize;
               supports_multiple_roots = true;
           }
           _ => return None,
       }
       if ref_size == 0 || ref_size > 4 {
           return None;
       }
       let offset_size = src[5] as usize;
       if offset_size == 0 || offset_size > 8 {
           return None;
       }
       index.advance(6);

       index.require(ref_size * 3 + offset_size)?;
       let (cell_count, root_count, absent_count) = unsafe {
           (
               index.read_be_uint_fast(src, ref_size),
               index.read_be_uint_fast(src, ref_size),
               index.read_be_uint_fast(src, ref_size),
           )
       };

       if !supports_multiple_roots && root_count > 1 {
           return None;
       }
       if root_count + absent_count > cell_count {
           return None;
       }

       index.require(offset_size)?;
       let total_cells_size = unsafe { index.read_be_uint_full(src, offset_size) };

       let min_cell_size = 2;
       if total_cells_size < min_cell_size * cell_count as u64 {
           return None;
       }
       let max_cell_size = 2 + 4 * (2 + 32) + 128 + 4 * ref_size as u64;
       if total_cells_size > max_cell_size * cell_count as u64 {
           return None;
       }

       let index_size = has_index as u64 * cell_count as u64 * offset_size as u64;
       index.require((index_size + total_cells_size + has_crc as u64 * 4) as usize)?;

       if has_index {
           index.advance(cell_count * offset_size);
       }

       let mut intermediate = SmallVec::<[IntermediateCell; 32]>::with_capacity(cell_count);
       for _ in 0..cell_count {
           index.require(2)?;
           let start = index.offset;

           let [d1, d2] = unsafe { index.read_descriptor_bytes(src) };
           if d1 == ABSENT_D1 {
               return None;
           }

           // 0b11111111 -> 0b01111111 + 1 = 0b10000000 = byte len 128, max bit len = 1023
           // 0b11111110 -> 0b01111111 = byte len 127, bit len = 1016
           let data_len = ((d2 >> 1) + (d2 & 1)) as usize;
           let ref_count = (d1 & 0b111) as usize;
           if ref_count > 4 {
               return None;
           }

           index.advance(data_len + ref_count * ref_size);
           index.require(0)?;

           intermediate.push(IntermediateCell {
               data: &src[start..index.offset],
           });
       }

       // let mut done_cells = FxHashMap::with_capacity_and_hasher(cell_count, Default::default());
       // for cell in intermediate.iter().rev() {
       //     // let [d1, d2] = unsafe { index.read };
       // }

       Some(todo!())
   }

*/
