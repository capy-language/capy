use std::{borrow::Cow, iter};

use hir::common::{
    ComptimeLoc, ConcreteGlobalLoc, ConcreteLambdaLoc, ConcreteLoc, FileName, NaiveGlobalLoc,
    NaiveLambdaLoc, NaiveLoc, get_naive_lambda_global,
};
use interner::Interner;
use itertools::Itertools;

use crate::{builtin::BuiltinFunction, compiler::FunctionToCompile};

pub(crate) trait Mangle {
    fn to_mangled_name(&self, mod_dir: &std::path::Path, interner: &Interner) -> String;
}

fn create_mangled_for_naive_global<'a>(
    mod_dir: &std::path::Path,
    interner: &'a Interner,
    loc: NaiveGlobalLoc,
    final_parts: impl Iterator<Item = MangledPart<'a>>,
) -> String {
    create_mangled_for_file(
        loc.file(),
        mod_dir,
        interner,
        &std::iter::once(MangledPart {
            kind: MangledPartKind::Name,
            text: interner.lookup(loc.name().0).into(),
        })
        .chain(final_parts)
        .collect_vec(),
    )
}

impl Mangle for NaiveGlobalLoc {
    fn to_mangled_name(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        create_mangled_for_naive_global(mod_dir, interner, *self, std::iter::empty())
    }
}

fn create_mangled_for_naive_lambda<'a>(
    mod_dir: &std::path::Path,
    interner: &'a Interner,
    loc: NaiveLambdaLoc,
    final_parts: impl Iterator<Item = MangledPart<'a>>,
) -> String {
    // TODO: what if a lambda is assigned to a global within a block or something
    // e.g.
    // foo :: {
    //     () {}
    // }
    // I don't think that specific example is possible, but could something similar happen?
    if let Some(global) = get_naive_lambda_global(loc) {
        create_mangled_for_naive_global(mod_dir, interner, global, final_parts)
    } else {
        create_mangled_for_file(
            loc.file(),
            mod_dir,
            interner,
            &std::iter::once(MangledPart {
                kind: MangledPartKind::Lambda,
                text: loc.lambda().into_raw().to_string().into(),
            })
            .chain(final_parts)
            .collect_vec(),
        )
    }
}

impl Mangle for NaiveLambdaLoc {
    fn to_mangled_name(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        create_mangled_for_naive_lambda(mod_dir, interner, *self, std::iter::empty())
    }
}

fn create_mangled_for_naive<'a>(
    mod_dir: &std::path::Path,
    interner: &'a Interner,
    loc: NaiveLoc,
    final_parts: impl Iterator<Item = MangledPart<'a>>,
) -> String {
    match loc {
        NaiveLoc::Global(global) => {
            create_mangled_for_naive_global(mod_dir, interner, global, final_parts)
        }
        NaiveLoc::Lambda(lambda) => {
            create_mangled_for_naive_lambda(mod_dir, interner, lambda, final_parts)
        }
    }
}

impl Mangle for NaiveLoc {
    fn to_mangled_name(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        create_mangled_for_naive(mod_dir, interner, *self, std::iter::empty())
    }
}

fn create_mangled_for_concrete_global<'a>(
    mod_dir: &std::path::Path,
    interner: &'a Interner,
    loc: ConcreteGlobalLoc,
    final_parts: impl Iterator<Item = MangledPart<'a>>,
) -> String {
    create_mangled_for_naive_global(
        mod_dir,
        interner,
        loc.to_naive(),
        loc.comptime_args()
            .map(|key| MangledPart {
                kind: MangledPartKind::GenericID,
                text: key.raw_start().to_string().into(),
            })
            .into_iter()
            .chain(final_parts),
    )
}

impl Mangle for ConcreteGlobalLoc {
    fn to_mangled_name(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        create_mangled_for_concrete_global(mod_dir, interner, *self, iter::empty())
    }
}

fn create_mangled_for_concrete_lambda<'a>(
    mod_dir: &std::path::Path,
    interner: &'a Interner,
    loc: ConcreteLambdaLoc,
    final_parts: impl Iterator<Item = MangledPart<'a>>,
) -> String {
    create_mangled_for_naive_lambda(
        mod_dir,
        interner,
        loc.to_naive(),
        loc.comptime_args()
            .map(|key| MangledPart {
                kind: MangledPartKind::GenericID,
                text: key.raw_start().to_string().into(),
            })
            .into_iter()
            .chain(final_parts),
    )
}

impl Mangle for ConcreteLambdaLoc {
    fn to_mangled_name(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        create_mangled_for_concrete_lambda(mod_dir, interner, *self, iter::empty())
    }
}

// todo: I don't like the repeated code in
// `create_mangled_for_concrete_global`
// `create_mangled_for_concrete_lambda`
// `create_mangled_for_concrete`
fn create_mangled_for_concrete<'a>(
    mod_dir: &std::path::Path,
    interner: &'a Interner,
    loc: ConcreteLoc,
    final_parts: impl Iterator<Item = MangledPart<'a>>,
) -> String {
    create_mangled_for_naive(
        mod_dir,
        interner,
        loc.to_naive(),
        loc.comptime_args()
            .map(|key| MangledPart {
                kind: MangledPartKind::GenericID,
                text: key.raw_start().to_string().into(),
            })
            .into_iter()
            .chain(final_parts),
    )
}

impl Mangle for ConcreteLoc {
    fn to_mangled_name(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        create_mangled_for_concrete(mod_dir, interner, *self, iter::empty())
    }
}

impl Mangle for FunctionToCompile {
    fn to_mangled_name(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        self.loc.to_mangled_name(mod_dir, interner)
    }
}

impl Mangle for ComptimeLoc {
    fn to_mangled_name(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        create_mangled_for_concrete(
            mod_dir,
            interner,
            self.loc,
            iter::once(MangledPart {
                kind: MangledPartKind::Comptime,
                text: self.comptime.into_raw().to_string().into(),
            }),
        )
    }
}

impl Mangle for (ComptimeLoc, &str) {
    fn to_mangled_name(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        create_mangled_for_concrete(
            mod_dir,
            interner,
            self.0.loc,
            [
                MangledPart {
                    kind: MangledPartKind::Comptime,
                    text: self.0.comptime.into_raw().to_string().into(),
                },
                MangledPart {
                    kind: MangledPartKind::InternalData,
                    text: self.1.into(),
                },
            ]
            .into_iter(),
        )
    }
}

impl Mangle for BuiltinFunction {
    fn to_mangled_name(&self, _: &std::path::Path, _: &Interner) -> String {
        let regular_name = match self {
            BuiltinFunction::PtrBitcast => Cow::Borrowed("ptr_bitcast"),
            BuiltinFunction::ConcreteBitcast(ty) => Cow::Owned(format!("{ty}_bitcast")),
        };

        mangle_internal(regular_name.as_ref())
    }
}

pub(crate) fn mangle_internal(name: &str) -> String {
    format!("_CI{}{}E", name.len(), name)
}

#[derive(Debug, Clone, Copy)]
enum MangledPartKind {
    Module,
    FileOrFolder,
    Name,
    GenericID,
    Lambda,
    Comptime,
    InternalData,
}

impl MangledPartKind {
    const fn to_code(self) -> char {
        match self {
            MangledPartKind::Module => 'M',
            MangledPartKind::FileOrFolder => 'F',
            MangledPartKind::Name => 'N',
            MangledPartKind::GenericID => 'G',
            MangledPartKind::Lambda => 'L',
            MangledPartKind::Comptime => 'Z',
            MangledPartKind::InternalData => 'I',
        }
    }
}

#[derive(Debug, Clone)]
struct MangledPart<'a> {
    kind: MangledPartKind,
    text: Cow<'a, str>,
}

/// Starts with "_C"
///
/// Followed by a table of contents, showing a single letter code for each part of the name.
/// See full list of letters above.
///
/// For each part, the length appears first, followed by the text itself.
/// If the text itself is just a number, then the length of the text will not appear.
///
/// Ends with "E"
fn create_mangled_for_file(
    file_name: FileName,
    mod_dir: &std::path::Path,
    interner: &Interner,
    final_parts: &[MangledPart],
) -> String {
    let components = file_name.get_components(mod_dir, interner);

    let mut mangled = String::new();

    // letters first

    if components.mod_name.is_some() {
        mangled.push(MangledPartKind::Module.to_code());
    }

    let fs_parts = components.sub_parts.collect_vec();

    for _ in 0..fs_parts.len() {
        mangled.push(MangledPartKind::FileOrFolder.to_code());
    }

    for final_part in final_parts {
        mangled.push(final_part.kind.to_code());
    }

    // now the actual parts

    if let Some(mod_name) = components.mod_name {
        add_part(
            &mut mangled,
            &MangledPart {
                kind: MangledPartKind::Module,
                text: mod_name,
            },
        );
    }

    for file_or_folder in fs_parts {
        add_part(
            &mut mangled,
            &MangledPart {
                kind: MangledPartKind::FileOrFolder,
                text: file_or_folder,
            },
        );
    }

    for final_part in final_parts {
        add_part(&mut mangled, final_part);
    }

    mangled.push('E');

    mangled
}

fn add_part(mangled: &mut String, part: &MangledPart) {
    if part.text.starts_with(|ch: char| ch.is_ascii_digit()) {
        // if the part text starts with a number,
        // then prepend a lowercase version of the code
        mangled.push_str(&(part.text.len() + 1).to_string());
        mangled.push(part.kind.to_code().to_ascii_lowercase());
        mangled.push_str(&part.text);

        // TODO: what happens in the following situation (where both files exist):
        // - "/src/1/file.capy"
        // - "/src/f1/file.capy"
        // similarly, what happens if the folder contains a '.' which gets converted to a dash
        // by `FileName::get_components`:
        // - "/src/program.app/file.capy"
        // - "/src/program-app/file.capy"
    } else {
        // if the part text doesn't start with a number, then print it normally
        mangled.push_str(&part.text.len().to_string());
        mangled.push_str(&part.text);
    }
}
