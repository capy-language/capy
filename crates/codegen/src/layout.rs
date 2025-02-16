use std::{cell::OnceCell, sync::Mutex};

use hir_ty::{InternTyExt, Ty};
use internment::Intern;
use rustc_hash::FxHashMap;

#[derive(Debug)]
pub(crate) struct TyLayouts {
    /// the pointer bit widths that all these type sizes were calculated with
    pointer_bit_width: u32,
    sizes: FxHashMap<Intern<Ty>, u32>,
    alignments: FxHashMap<Intern<Ty>, u32>,
    struct_layouts: FxHashMap<Intern<Ty>, StructLayout>,
    enum_layouts: FxHashMap<Intern<Ty>, EnumLayout>,
}

static LAYOUTS: Mutex<OnceCell<TyLayouts>> = Mutex::new(OnceCell::new());

pub(crate) trait GetLayoutInfo {
    fn size(&self) -> u32;
    fn align(&self) -> u32;
    fn stride(&self) -> u32;
    fn align_shift(&self) -> u8;
    fn struct_layout(&self) -> Option<StructLayout>;
    fn enum_layout(&self) -> Option<EnumLayout>;
}

impl GetLayoutInfo for Intern<Ty> {
    fn size(&self) -> u32 {
        // we could do `get_or_init` here, but the index would panic anyways
        LAYOUTS.lock().unwrap().get().unwrap().sizes[self]
    }

    fn align(&self) -> u32 {
        LAYOUTS.lock().unwrap().get().unwrap().alignments[self]
    }

    /// The amount of left shifts needed to get the right alignment.
    /// This is needed for cranelift.
    ///
    /// `1 << align_shift == align`
    fn align_shift(&self) -> u8 {
        let align = LAYOUTS.lock().unwrap().get().unwrap().alignments[self];
        assert!(align.is_power_of_two());
        // trailing_zeros(n) == log2(n) if and only if n is a power of two
        align.trailing_zeros() as u8
    }

    fn stride(&self) -> u32 {
        let layouts = LAYOUTS.lock().unwrap();
        let layouts = layouts.get().unwrap();
        let mask = layouts.alignments[self] - 1;
        (layouts.sizes[self] + mask) & !mask
    }

    fn struct_layout(&self) -> Option<StructLayout> {
        // since struct layouts only exist for structs and not for distincts or variants
        let absolute_ty = self.absolute_intern_ty(true);

        let layouts = LAYOUTS.lock().ok()?;
        let layouts = layouts.get()?;
        layouts.struct_layouts.get(&absolute_ty).cloned()
    }

    fn enum_layout(&self) -> Option<EnumLayout> {
        // since struct layouts only exist for structs and not for distincts or variants
        let absolute_ty = self.absolute_intern_ty(true);

        let layouts = LAYOUTS.lock().ok()?;
        let layouts = layouts.get()?;
        layouts.enum_layouts.get(&absolute_ty).cloned()
    }
}

/// Calcuates size, alignment, stride, and field offsets of types.
///
/// If called multiple times, new types will be calculated without discarding old results
///
/// Old results will only be dropped if you try to calculate the layout using a different pointer
/// width.
pub(crate) fn calc_layouts(tys: impl Iterator<Item = Intern<Ty>>, pointer_bit_width: u32) {
    let init = || TyLayouts {
        pointer_bit_width,
        sizes: FxHashMap::default(),
        alignments: FxHashMap::default(),
        struct_layouts: FxHashMap::default(),
        enum_layouts: FxHashMap::default(),
    };

    {
        let layouts = LAYOUTS.lock().unwrap();
        let layout = layouts.get_or_init(init);
        if layout.pointer_bit_width != pointer_bit_width {
            layouts.set(init()).unwrap();
        }
    }

    for ty in tys {
        calc_single(ty, pointer_bit_width);
    }

    {
        let mut layouts = LAYOUTS.lock().unwrap();
        let layouts = layouts.get_mut().unwrap();
        layouts.sizes.shrink_to_fit();
        layouts.alignments.shrink_to_fit();
        layouts.struct_layouts.shrink_to_fit();
        layouts.enum_layouts.shrink_to_fit();
    }
}

fn calc_single(ty: Intern<Ty>, pointer_bit_width: u32) {
    {
        let layouts = LAYOUTS.lock().unwrap();
        let layouts = layouts.get().unwrap();
        if layouts.sizes.contains_key(&ty) {
            return;
        }
    }

    let size = match ty.as_ref() {
        Ty::NotYetResolved | Ty::Unknown => 0,
        Ty::IInt(u8::MAX) | Ty::UInt(u8::MAX) => pointer_bit_width / 8,
        Ty::IInt(0) | Ty::UInt(0) => 32 / 8,
        Ty::IInt(bit_width) | Ty::UInt(bit_width) => *bit_width as u32 / 8,
        Ty::Float(0) => 32 / 8,
        Ty::Float(bit_width) => *bit_width as u32 / 8,
        Ty::Bool | Ty::Char => 1, // bools and chars are u8's
        Ty::String => pointer_bit_width / 8,
        Ty::Array { size, sub_ty, .. } => {
            calc_single(*sub_ty, pointer_bit_width);
            sub_ty.stride() * *size as u32
        }
        Ty::Slice { .. } => {
            // a slice is len (usize) + ptr (usize)
            pointer_bit_width / 8 * 2
        }
        Ty::Pointer { .. } => pointer_bit_width / 8,
        Ty::Distinct { sub_ty, .. } => {
            calc_single(*sub_ty, pointer_bit_width);
            sub_ty.size()
        }
        Ty::Function { .. } => pointer_bit_width / 8,
        Ty::Struct { members, .. } => {
            let members = members.iter().map(|member| member.ty).collect::<Vec<_>>();
            for member_ty in &members {
                calc_single(*member_ty, pointer_bit_width);
            }
            let struct_layout = StructLayout::new(members);
            let size = struct_layout.size;

            {
                let mut layouts = LAYOUTS.lock().unwrap();
                layouts
                    .get_mut()
                    .unwrap()
                    .struct_layouts
                    .insert(ty, struct_layout);
            }

            size
        }
        Ty::Enum { variants, .. } => {
            let mut max_variant_size = 0;
            let mut max_variant_align = 1;

            for variant_ty in variants {
                calc_single(*variant_ty, pointer_bit_width);
                let variant_size = variant_ty.size();
                if variant_size > max_variant_size {
                    max_variant_size = variant_size;
                }
                let variant_align = variant_ty.align();
                if variant_align > max_variant_align {
                    max_variant_align = variant_align;
                }
            }

            let enum_layout = EnumLayout {
                // +1 for the discriminant
                size: max_variant_size + 1,
                align: max_variant_align,
                discriminant_offset: max_variant_size,
            };
            let size = enum_layout.size;

            {
                let mut layouts = LAYOUTS.lock().unwrap();
                layouts
                    .get_mut()
                    .unwrap()
                    .enum_layouts
                    .insert(ty, enum_layout);
            }

            size
        }
        Ty::Variant { sub_ty, .. } => {
            calc_single(*sub_ty, pointer_bit_width);
            sub_ty.size()
        }
        Ty::Type => 32 / 8,
        Ty::Any => {
            let mut current_offset = 0;

            let typeid_size = 32 / 8;
            // let typeid_align = typeid_size.min(8);

            let rawptr_size = pointer_bit_width / 8;
            let rawptr_align = rawptr_size.min(8);

            current_offset += typeid_size;
            current_offset += padding_needed_for(current_offset, rawptr_align);

            current_offset += rawptr_size;

            current_offset
        }
        Ty::RawPtr { .. } => pointer_bit_width / 8,
        // a slice is len (usize) + ptr (usize)
        Ty::RawSlice => pointer_bit_width / 8 * 2,
        Ty::Void => 0,
        Ty::NoEval => 0,
        Ty::File(_) => 0,
    };

    let align = match ty.as_ref() {
        Ty::NotYetResolved | Ty::Unknown => 1,
        Ty::IInt(_) | Ty::UInt(_) | Ty::Float(_) => size.min(8),
        Ty::Bool | Ty::Char => 1, // bools and chars are u8's
        Ty::String | Ty::Pointer { .. } | Ty::Function { .. } => size.min(8),
        // the sub_ty was already `calc()`ed just before
        Ty::Array { sub_ty, .. } => sub_ty.align(),
        Ty::Slice { .. } => (size / 2).min(8),
        Ty::Distinct { sub_ty, .. } => sub_ty.align(),
        Ty::Struct { .. } => ty.struct_layout().unwrap().align,
        Ty::Enum { .. } => ty.enum_layout().unwrap().align,
        Ty::Variant { sub_ty, .. } => sub_ty.align(),
        Ty::Type => size,
        Ty::Any => {
            let typeid_size = 32 / 8;
            let typeid_align = typeid_size.min(8);

            let rawptr_size = pointer_bit_width / 8;
            let rawptr_align = rawptr_size.min(8);

            typeid_align.max(rawptr_align)
        }
        Ty::RawPtr { .. } => size.min(8),
        Ty::RawSlice => (size / 2).min(8),
        Ty::Void => 1,
        Ty::NoEval => 1,
        Ty::File(_) => 1,
    };

    {
        let mut layouts = LAYOUTS.lock().unwrap();
        let layouts = layouts.get_mut().unwrap();
        layouts.sizes.insert(ty, size);
        layouts.alignments.insert(ty, align);
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct EnumLayout {
    size: u32,
    align: u32,
    discriminant_offset: u32,
}

impl EnumLayout {
    pub(crate) fn discriminant_offset(&self) -> u32 {
        self.discriminant_offset
    }
}

#[derive(Debug, Clone)]
pub(crate) struct StructLayout {
    size: u32,
    align: u32,
    offsets: Vec<u32>,
}

/// checks if the offset is a multiple of the alignment
///
/// if not, returns the amount of bytes needed
/// to make it a valid offset
pub(crate) fn padding_needed_for(offset: u32, align: u32) -> u32 {
    let misalign = offset % align;
    if misalign > 0 {
        // the amount needed to round up to the next proper offset
        align - misalign
    } else {
        0
    }
}

impl StructLayout {
    pub(crate) fn new(fields: Vec<Intern<Ty>>) -> Self {
        let mut offsets = Vec::with_capacity(fields.len());
        let mut max_align = 1;
        let mut current_offset = 0;

        for field in fields {
            let field_align = field.align();
            if field_align > max_align {
                max_align = field_align;
            }

            current_offset += padding_needed_for(current_offset, field_align);

            offsets.push(current_offset);

            current_offset += field.size();
        }

        Self {
            size: current_offset,
            align: max_align,
            offsets,
        }
    }

    pub(crate) fn offsets(&self) -> &[u32] {
        &self.offsets
    }
}
