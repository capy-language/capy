use cranelift::codegen::ir::Endianness;

pub(crate) trait ExtendWithNumBytes {
    fn extend_with_num_bytes(&mut self, num: u32, bit_width: u8, endianness: Endianness);
}

impl ExtendWithNumBytes for Vec<u8> {
    fn extend_with_num_bytes(&mut self, num: u32, target_bit_width: u8, endianness: Endianness) {
        match (target_bit_width, endianness) {
            (8, Endianness::Big) => self.extend((num as u8).to_be_bytes()),
            (8, Endianness::Little) => self.extend((num as u8).to_le_bytes()),
            (16, Endianness::Big) => self.extend((num as u16).to_be_bytes()),
            (16, Endianness::Little) => self.extend((num as u16).to_le_bytes()),
            #[allow(clippy::unnecessary_cast)]
            (32, Endianness::Big) => self.extend((num as u32).to_be_bytes()),
            #[allow(clippy::unnecessary_cast)]
            (32, Endianness::Little) => self.extend((num as u32).to_le_bytes()),
            (64, Endianness::Big) => self.extend((num as u64).to_be_bytes()),
            (64, Endianness::Little) => self.extend((num as u64).to_le_bytes()),
            _ => unreachable!(),
        }
    }
}
