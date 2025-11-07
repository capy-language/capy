use cranelift::codegen::ir::Endianness;
use cranelift_module::{DataDescription, DataId, Linkage, Module};
use hir::common::{MemberTy, Ty};
use uid_gen::UIDGenerator;

use crate::{extend::ExtendWithNumBytes, layout, mangle};

use super::{Compiler, GetLayoutInfo, ToTyId, comptime::IntBytes};

fn define(
    module: &mut dyn Module,
    data_desc: &mut DataDescription,
    info_array: DataId,
    bytes: Vec<u8>,
    align: u64,
) {
    data_desc.define(bytes.into_boxed_slice());
    data_desc.set_align(align);
    module
        .define_data(info_array, data_desc)
        .expect("error defining data");
    data_desc.clear();
}

fn define_with_relocs(
    module: &mut dyn Module,
    data_desc: &mut DataDescription,
    info_array: DataId,
    bytes: Vec<u8>,
    align: u64,
    relocs: Vec<Reloc>,
) {
    data_desc.define(bytes.into_boxed_slice());
    data_desc.set_align(align);

    for reloc in relocs {
        let local = module.declare_data_in_data(reloc.data_id, data_desc);

        data_desc.write_data_addr(reloc.reloc_offset, local, reloc.data_offset);
    }

    module
        .define_data(info_array, data_desc)
        .expect("error defining data");

    data_desc.clear();
}

fn define_slice(
    module: &mut dyn Module,
    data_desc: &mut DataDescription,
    info_array: DataId,
    len: u32,
    ptr: DataId,
) {
    let mut bytes = Vec::with_capacity(module.target_config().pointer_bytes() as usize);
    bytes.extend_with_num_bytes(
        len,
        module.target_config().pointer_bits(),
        module.isa().endianness(),
    );
    // zeroed-out pointer, this will be written over later
    bytes.extend(std::iter::repeat_n(
        0,
        module.target_config().pointer_bytes() as usize,
    ));

    data_desc.define(bytes.into_boxed_slice());
    data_desc.set_align(module.target_config().pointer_bytes().min(8) as u64);

    let local = module.declare_data_in_data(ptr, data_desc);

    data_desc.write_data_addr(module.target_config().pointer_bytes() as u32, local, 0);

    module
        .define_data(info_array, data_desc)
        .expect("error defining data");

    data_desc.clear();
}

fn declare(module: &mut dyn Module, name: &str) -> DataId {
    module
        .declare_data(name, Linkage::Local, true, false)
        .expect("error declaring data")
}

#[derive(Debug)]
struct Reloc {
    /// The offset in the greater DataArray, at which this reloc will be placed
    reloc_offset: u32,
    data_id: DataId,
    /// The reloc will point towards `ptr_of(data_id) + data_offset`
    data_offset: i64,
}

#[derive(Debug)]
struct DataArray {
    ptr_align: u64,
    endianness: Endianness,
    /// this is updated as items are added to the data
    max_align: u32,
    count: u32,
    bytes: Vec<u8>,
    relocs: Vec<Reloc>,
}

impl DataArray {
    fn new(ptr_align: u64, endianness: Endianness) -> Self {
        Self {
            ptr_align,
            endianness,
            max_align: 1,
            count: 0,
            bytes: Vec::new(),
            relocs: Vec::new(),
        }
    }

    fn push_num(&mut self, num: u32, target_bit_width: u8) {
        let current_offset = self.bytes.len() as u32;

        let target_align = (target_bit_width / 8).min(8) as u32;
        if target_align > self.max_align {
            self.max_align = target_align;
        }

        let padding = layout::padding_needed_for(current_offset, target_align);
        self.bytes.extend(std::iter::repeat_n(0, padding as usize));

        self.bytes
            .extend((num as u64).into_bytes(self.endianness, target_bit_width))
    }

    fn push_reloc_ptr(&mut self, data_id: DataId, data_offset: i64, ptr_bit_width: u8) {
        let current_offset = self.bytes.len() as u32;

        let target_align = self.ptr_align as u32;
        if target_align > self.max_align {
            self.max_align = target_align;
        }

        let padding = layout::padding_needed_for(current_offset, target_align) as usize;

        let reloc_offset = self.bytes.len() + padding;

        self.bytes.extend(std::iter::repeat_n(
            0,
            padding + (ptr_bit_width / 8) as usize,
        ));

        self.relocs.push(Reloc {
            reloc_offset: reloc_offset as u32,
            data_id,
            data_offset,
        });
    }

    fn len(&self) -> usize {
        self.bytes.len()
    }

    /// Adds padding for the next array item
    fn finish_array_item(&mut self) {
        let current_offset = self.bytes.len() as u32;
        let padding = layout::padding_needed_for(current_offset, self.max_align);
        self.bytes.extend(std::iter::repeat_n(0, padding as usize));

        self.count += 1;
    }

    fn define_array(
        self,
        module: &mut dyn Module,
        data_desc: &mut DataDescription,
        array_id: DataId,
    ) {
        define_with_relocs(
            module,
            data_desc,
            array_id,
            self.bytes,
            self.max_align as u64,
            self.relocs,
        );
    }

    fn define_array_and_slice(
        self,
        module: &mut dyn Module,
        data_desc: &mut DataDescription,
        array_id: DataId,
        slice_id: DataId,
    ) {
        define_with_relocs(
            module,
            data_desc,
            array_id,
            self.bytes,
            self.max_align as u64,
            self.relocs,
        );

        define_slice(module, data_desc, slice_id, self.count, array_id);
    }
}

fn compile_memory_layouts(compiler: &mut Compiler) {
    let Some(layout_arrays) = &compiler.meta_tys.layout_arrays else {
        return;
    };

    let ptr_bit_width = compiler.ptr_ty.bits() as u8;
    let ptr_align = compiler.ptr_ty.bytes().min(8) as u64;
    let endianness = compiler.module.isa().endianness();

    let mut array_mem_data = DataArray::new(ptr_align, endianness);
    let mut distinct_mem_data = DataArray::new(ptr_align, endianness);
    let mut struct_mem_data = DataArray::new(ptr_align, endianness);
    let mut enum_mem_data = DataArray::new(ptr_align, endianness);
    let mut variant_mem_data = DataArray::new(ptr_align, endianness);
    let mut optional_mem_data = DataArray::new(ptr_align, endianness);
    let mut error_union_mem_data = DataArray::new(ptr_align, endianness);

    for ty in &compiler.meta_tys.tys_to_compile {
        let data = match ty.as_ref() {
            Ty::AnonArray { .. } | Ty::ConcreteArray { .. } => &mut array_mem_data,
            Ty::Distinct { .. } => &mut distinct_mem_data,
            Ty::AnonStruct { .. } | Ty::ConcreteStruct { .. } => &mut struct_mem_data,
            Ty::Enum { .. } => &mut enum_mem_data,
            Ty::EnumVariant { .. } => &mut variant_mem_data,
            Ty::Optional { .. } => &mut optional_mem_data,
            Ty::ErrorUnion { .. } => &mut error_union_mem_data,
            _ => continue,
        };

        let size = ty.size();
        let align = ty.align();

        data.push_num(size, ptr_bit_width);
        data.push_num(align, ptr_bit_width);
        data.finish_array_item();
    }

    // add the compiled layout data into the binary

    array_mem_data.define_array_and_slice(
        compiler.module,
        &mut compiler.data_desc,
        layout_arrays.array_layout_array,
        layout_arrays.array_layout_slice,
    );
    distinct_mem_data.define_array_and_slice(
        compiler.module,
        &mut compiler.data_desc,
        layout_arrays.distinct_layout_array,
        layout_arrays.distinct_layout_slice,
    );
    struct_mem_data.define_array_and_slice(
        compiler.module,
        &mut compiler.data_desc,
        layout_arrays.struct_layout_array,
        layout_arrays.struct_layout_slice,
    );
    enum_mem_data.define_array_and_slice(
        compiler.module,
        &mut compiler.data_desc,
        layout_arrays.enum_layout_array,
        layout_arrays.enum_layout_slice,
    );
    variant_mem_data.define_array_and_slice(
        compiler.module,
        &mut compiler.data_desc,
        layout_arrays.variant_layout_array,
        layout_arrays.variant_layout_slice,
    );
    optional_mem_data.define_array_and_slice(
        compiler.module,
        &mut compiler.data_desc,
        layout_arrays.optional_layout_array,
        layout_arrays.optional_layout_slice,
    );
    error_union_mem_data.define_array_and_slice(
        compiler.module,
        &mut compiler.data_desc,
        layout_arrays.error_union_layout_array,
        layout_arrays.error_union_layout_slice,
    );

    // pointer layout is just a single struct

    let mut pointer_layout_data = Vec::with_capacity(compiler.ptr_ty.bytes() as usize * 2);
    pointer_layout_data.extend_with_num_bytes(compiler.ptr_ty.bytes(), ptr_bit_width, endianness);
    pointer_layout_data.extend_with_num_bytes(ptr_align as u32, ptr_bit_width, endianness);
    define(
        compiler.module,
        &mut compiler.data_desc,
        layout_arrays.pointer_layout,
        pointer_layout_data,
        ptr_align,
    );
}

fn compile_type_info(compiler: &mut Compiler) {
    let Some(info_arrays) = &compiler.meta_tys.info_arrays else {
        return;
    };

    let ptr_bit_width = compiler.ptr_ty.bits() as u8;
    let ptr_align = compiler.ptr_ty.bytes().min(8) as u64;
    let endianness = compiler.module.isa().endianness();

    let mut array_info_data = DataArray::new(ptr_align, endianness);
    let mut slice_info_data = DataArray::new(ptr_align, endianness);
    let mut pointer_info_data = DataArray::new(ptr_align, endianness);
    let mut distinct_info_data = DataArray::new(ptr_align, endianness);
    let mut variant_info_data = DataArray::new(ptr_align, endianness);
    let mut struct_info_data = DataArray::new(ptr_align, endianness);
    let mut enum_info_data = DataArray::new(ptr_align, endianness);
    let mut optional_info_data = DataArray::new(ptr_align, endianness);
    let mut error_union_info_data = DataArray::new(ptr_align, endianness);

    let mut member_name_str_uid_gen = UIDGenerator::default();
    let member_info_id = declare(
        compiler.module,
        &mangle::mangle_internal("struct_member_info"),
    );
    let mut member_info_data = DataArray::new(ptr_align, endianness);

    // `Enum_Info` has a `[]type` field
    // this is the array of all those `ty`s
    // todo: maybe pick a more descriptive name, so this doesn't get confused with `variant_info_data`
    let variant_enum_ty_id = declare(
        compiler.module,
        &mangle::mangle_internal("enum_variant_tys"),
    );
    let mut variant_enum_ty_data = DataArray::new(ptr_align, endianness);

    for ty in &compiler.meta_tys.tys_to_compile {
        match ty.as_ref() {
            Ty::AnonArray { size, sub_ty } | Ty::ConcreteArray { size, sub_ty, .. } => {
                array_info_data.push_num(*size as u32, ptr_bit_width);
                array_info_data.push_num(sub_ty.to_previous_type_id(&compiler.meta_tys), 32);
                array_info_data.finish_array_item();
            }
            Ty::Slice { sub_ty } => {
                slice_info_data.push_num(sub_ty.to_previous_type_id(&compiler.meta_tys), 32);
                slice_info_data.finish_array_item();
            }
            Ty::Pointer { sub_ty, mutable } => {
                pointer_info_data.push_num(sub_ty.to_previous_type_id(&compiler.meta_tys), 32);
                pointer_info_data.push_num(*mutable as u32, 8);
                pointer_info_data.finish_array_item();
            }
            Ty::Distinct { sub_ty, .. } => {
                distinct_info_data.push_num(sub_ty.to_previous_type_id(&compiler.meta_tys), 32);
                distinct_info_data.finish_array_item();
            }
            Ty::Enum { variants, .. } => {
                let starting_offset = variant_enum_ty_data.len();
                // member_array_starting_offsets.push(member_array_data.len());

                for variant_ty in variants {
                    variant_enum_ty_data
                        .push_num(variant_ty.to_previous_type_id(&compiler.meta_tys), 32);

                    variant_enum_ty_data.finish_array_item();
                }

                // now that all the members have been defined, we can assemble the actual struct info array

                enum_info_data.push_num(variants.len() as u32, ptr_bit_width);
                enum_info_data.push_reloc_ptr(
                    variant_enum_ty_id,
                    starting_offset as i64,
                    ptr_bit_width,
                );

                let enum_layout = ty.enum_layout().unwrap();
                enum_info_data.push_num(enum_layout.discriminant_offset(), ptr_bit_width);

                enum_info_data.finish_array_item();
            }
            Ty::EnumVariant {
                sub_ty,
                discriminant,
                ..
            } => {
                variant_info_data.push_num(sub_ty.to_previous_type_id(&compiler.meta_tys), 32);
                variant_info_data.push_num(*discriminant as u32, 32);
                variant_info_data.finish_array_item();
            }
            Ty::Optional { sub_ty } => {
                optional_info_data.push_num(sub_ty.to_previous_type_id(&compiler.meta_tys), 32);
                if let Some(enum_layout) = ty.enum_layout() {
                    // `is_non_zero`
                    optional_info_data.push_num(0, 8);
                    // `discriminant_offset`
                    optional_info_data.push_num(enum_layout.discriminant_offset(), ptr_bit_width);
                } else {
                    // `is_non_zero`
                    optional_info_data.push_num(1, 8);
                    // `discriminant_offset`
                    optional_info_data.push_num(0, ptr_bit_width);
                }
                optional_info_data.finish_array_item();
            }
            Ty::ErrorUnion {
                error_ty,
                payload_ty,
            } => {
                error_union_info_data
                    .push_num(error_ty.to_previous_type_id(&compiler.meta_tys), 32);
                error_union_info_data
                    .push_num(payload_ty.to_previous_type_id(&compiler.meta_tys), 32);
                let enum_layout = ty
                    .enum_layout()
                    .expect("error unions should always have an enum layout");
                error_union_info_data.push_num(enum_layout.discriminant_offset(), ptr_bit_width);
                error_union_info_data.finish_array_item();
            }
            Ty::AnonStruct { members } | Ty::ConcreteStruct { members, .. } => {
                let member_offsets = ty.struct_layout().unwrap();
                let member_offsets = member_offsets.offsets();

                let starting_offset = member_info_data.len();
                // member_array_starting_offsets.push(member_array_data.len());

                for (idx, MemberTy { name, ty }) in members.iter().enumerate() {
                    // `name` field

                    // define the string bytes in the binary
                    let mut name_str_bytes = compiler.interner.lookup(name.0).as_bytes().to_vec();
                    name_str_bytes.push(0); // null terminated strings

                    let name_str_id = declare(
                        compiler.module,
                        &format!(
                            ".member_str{}",
                            member_name_str_uid_gen.generate_unique_id()
                        ),
                    );
                    define(
                        compiler.module,
                        &mut compiler.data_desc,
                        name_str_id,
                        name_str_bytes,
                        1,
                    );

                    member_info_data.push_reloc_ptr(name_str_id, 0, ptr_bit_width);

                    // `ty` field

                    member_info_data.push_num(ty.to_previous_type_id(&compiler.meta_tys), 32);

                    // `offset` field

                    member_info_data.push_num(member_offsets[idx], ptr_bit_width);

                    member_info_data.finish_array_item();
                }

                // now that all the members have been defined, we can assemble the actual struct info array

                struct_info_data.push_num(members.len() as u32, ptr_bit_width);
                struct_info_data.push_reloc_ptr(
                    member_info_id,
                    starting_offset as i64,
                    ptr_bit_width,
                );
                struct_info_data.finish_array_item();
            }
            _ => continue,
        }
    }

    // add the compiled info data into the binary

    array_info_data.define_array_and_slice(
        compiler.module,
        &mut compiler.data_desc,
        info_arrays.array_info_array,
        info_arrays.array_info_slice,
    );
    slice_info_data.define_array_and_slice(
        compiler.module,
        &mut compiler.data_desc,
        info_arrays.slice_info_array,
        info_arrays.slice_info_slice,
    );
    pointer_info_data.define_array_and_slice(
        compiler.module,
        &mut compiler.data_desc,
        info_arrays.pointer_info_array,
        info_arrays.pointer_info_slice,
    );
    distinct_info_data.define_array_and_slice(
        compiler.module,
        &mut compiler.data_desc,
        info_arrays.distinct_info_array,
        info_arrays.distinct_info_slice,
    );
    variant_info_data.define_array_and_slice(
        compiler.module,
        &mut compiler.data_desc,
        info_arrays.variant_info_array,
        info_arrays.variant_info_slice,
    );
    struct_info_data.define_array_and_slice(
        compiler.module,
        &mut compiler.data_desc,
        info_arrays.struct_info_array,
        info_arrays.struct_info_slice,
    );
    enum_info_data.define_array_and_slice(
        compiler.module,
        &mut compiler.data_desc,
        info_arrays.enum_info_array,
        info_arrays.enum_info_slice,
    );
    optional_info_data.define_array_and_slice(
        compiler.module,
        &mut compiler.data_desc,
        info_arrays.optional_info_array,
        info_arrays.optional_info_slice,
    );
    error_union_info_data.define_array_and_slice(
        compiler.module,
        &mut compiler.data_desc,
        info_arrays.error_union_info_array,
        info_arrays.error_union_info_slice,
    );

    member_info_data.define_array(compiler.module, &mut compiler.data_desc, member_info_id);
    variant_enum_ty_data.define_array(compiler.module, &mut compiler.data_desc, variant_enum_ty_id);
}

pub(crate) fn compile_meta_builtins(compiler: &mut Compiler) {
    compile_memory_layouts(compiler);
    compile_type_info(compiler);
}
