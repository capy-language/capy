use cranelift::codegen::ir::Endianness;

use crate::compiler::comptime::IntBytes;

pub(crate) trait ExtendWithNumBytes {
    fn extend_with_num_bytes(&mut self, num: u32, bit_width: u8, endianness: Endianness);
}

impl ExtendWithNumBytes for Vec<u8> {
    fn extend_with_num_bytes(&mut self, num: u32, target_bit_width: u8, endianness: Endianness) {
        self.extend((num as u64).into_bytes(endianness, target_bit_width))
    }
}
