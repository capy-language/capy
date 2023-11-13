use std::{cell::OnceCell, sync::Mutex};

use hir_ty::Ty;
use internment::Intern;
use rustc_hash::FxHashMap;

#[derive(Debug)]
pub(crate) struct TyLayouts {
    pointer_bit_width: u32,
    sizes: FxHashMap<Intern<Ty>, u32>,
    alignments: FxHashMap<Intern<Ty>, u32>,
    struct_layouts: FxHashMap<Intern<Ty>, StructLayout>,
}

static mut LAYOUTS: Mutex<OnceCell<TyLayouts>> = Mutex::new(OnceCell::new());

pub(crate) trait GetLayoutInfo {
    fn size(&self) -> u32;
    fn align(&self) -> u32;
    fn stride(&self) -> u32;
    fn struct_layout(&self) -> Option<StructLayout>;
}

impl GetLayoutInfo for Intern<Ty> {
    fn size(&self) -> u32 {
        // we could do `get_or_init` here, but the index would panic anyways
        unsafe { LAYOUTS.lock() }.unwrap().get().unwrap().sizes[self]
    }

    fn align(&self) -> u32 {
        unsafe { LAYOUTS.lock() }.unwrap().get().unwrap().alignments[self]
    }

    fn stride(&self) -> u32 {
        let layouts = unsafe { LAYOUTS.lock() }.unwrap();
        let layouts = layouts.get().unwrap();
        let mask = layouts.alignments[self] - 1;
        (layouts.sizes[self] + mask) & !mask
    }

    fn struct_layout(&self) -> Option<StructLayout> {
        let layouts = unsafe { LAYOUTS.lock() }.ok()?;
        let layouts = layouts.get()?;
        layouts.struct_layouts.get(self).cloned()
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
    };

    {
        let layouts = unsafe { LAYOUTS.lock() }.unwrap();
        let layout = layouts.get_or_init(init);
        if layout.pointer_bit_width != pointer_bit_width {
            layouts.set(init()).unwrap();
        }
    }

    for ty in tys {
        calc_single(ty, pointer_bit_width);
    }

    {
        let mut layouts = unsafe { LAYOUTS.lock() }.unwrap();
        let layouts = layouts.get_mut().unwrap();
        layouts.sizes.shrink_to_fit();
        layouts.alignments.shrink_to_fit();
        layouts.struct_layouts.shrink_to_fit();
    }
}

fn calc_single(ty: Intern<Ty>, pointer_bit_width: u32) {
    {
        let layouts = unsafe { LAYOUTS.lock() }.unwrap();
        let layouts = layouts.get().unwrap();
        if layouts.sizes.get(&ty).is_some() {
            return;
        }
    }

    let size = match ty.as_ref() {
        Ty::NotYetResolved | Ty::Unknown => unreachable!(),
        Ty::IInt(u8::MAX) | Ty::UInt(u8::MAX) => pointer_bit_width / 8,
        Ty::IInt(0) | Ty::UInt(0) => 32 / 8,
        Ty::IInt(bit_width) | Ty::UInt(bit_width) => *bit_width as u32 / 8,
        Ty::Float(0) => 32 / 8,
        Ty::Float(bit_width) => *bit_width as u32 / 8,
        Ty::Bool | Ty::Char => 1, // bools and chars are u8's
        Ty::String => pointer_bit_width / 8,
        Ty::Array { size, sub_ty } => {
            calc_single(*sub_ty, pointer_bit_width);
            sub_ty.stride() * *size as u32
        }
        Ty::Slice { .. } => {
            // a slice is len (usize) + ptr (usize)
            pointer_bit_width / 8 * 2
        }
        Ty::Pointer { .. } => pointer_bit_width / 8,
        Ty::Distinct { sub_ty: ty, .. } => {
            calc_single(*ty, pointer_bit_width);
            ty.size()
        }
        Ty::Function { .. } => pointer_bit_width / 8,
        Ty::Struct { fields, .. } => {
            let fields = fields.iter().map(|(_, ty)| ty).copied().collect::<Vec<_>>();
            for field in &fields {
                calc_single(*field, pointer_bit_width);
            }
            let struct_layout = StructLayout::new(fields);
            let size = struct_layout.size;

            {
                let mut layouts = unsafe { LAYOUTS.lock() }.unwrap();
                layouts
                    .get_mut()
                    .unwrap()
                    .struct_layouts
                    .insert(ty, struct_layout);
            }

            size
        }
        Ty::Type => 32 / 8,
        Ty::Any => 0,
        Ty::Void => 0,
        Ty::File(_) => 0,
    };

    let align = match ty.as_ref() {
        Ty::NotYetResolved | Ty::Unknown => unreachable!(),
        Ty::IInt(_) | Ty::UInt(_) | Ty::Float(_) => size.min(8),
        Ty::Bool | Ty::Char => 1, // bools and chars are u8's
        Ty::String | Ty::Pointer { .. } | Ty::Function { .. } => size,
        // the sub_ty was already `calc()`ed just before
        Ty::Array { sub_ty, .. } => sub_ty.align(),
        Ty::Slice { .. } => size / 2,
        Ty::Distinct { sub_ty: ty, .. } => ty.align(),
        Ty::Struct { .. } => ty.struct_layout().unwrap().align,
        Ty::Type => size,
        Ty::Any => 1,
        Ty::Void => 1,
        Ty::File(_) => 1,
    };

    {
        let mut layouts = unsafe { LAYOUTS.lock() }.unwrap();
        let layouts = layouts.get_mut().unwrap();
        layouts.sizes.insert(ty, size);
        layouts.alignments.insert(ty, align);
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

    pub(crate) fn offsets(&self) -> &Vec<u32> {
        &self.offsets
    }
}
