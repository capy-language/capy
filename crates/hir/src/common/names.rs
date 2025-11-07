use std::{
    borrow::Cow,
    env,
    path::{Component, Path},
};

use text_size::TextRange;

use interner::{Interner, Key};

use super::NaiveGlobalLoc;

pub struct FileNameComponents<'a, T: Iterator<Item = Cow<'a, str>>> {
    pub mod_name: Option<Cow<'a, str>>,
    pub sub_parts: T,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileName(pub Key);

impl FileName {
    pub fn to_string(&self, mod_dir: &Path, interner: &Interner) -> String {
        let mut res = String::new();

        let components = self.get_components(mod_dir, interner);

        if let Some(mod_name) = &components.mod_name {
            res.push_str(&mod_name);
        }

        for (idx, component) in components.sub_parts.enumerate() {
            if idx == 0 && components.mod_name.is_some() {
                res.push_str("::");
            } else if idx > 0 {
                res.push('.');
            }

            res.push_str(&component);
        }

        res
    }

    pub fn debug(&self, interner: &Interner) -> String {
        let file_name = Path::new(interner.lookup(self.0));

        file_name
            .components()
            .last()
            .map(|c| c.as_os_str().to_string_lossy())
            .map(|c| c.strip_suffix(".capy").unwrap_or(&c).to_string())
            .unwrap_or_default()
    }

    pub fn is_mod(&self, mod_dir: &Path, interner: &Interner) -> bool {
        let file_name = Path::new(interner.lookup(self.0));

        file_name.is_sub_dir_of(mod_dir)
    }

    pub fn get_mod_name(&self, mod_dir: &Path, interner: &Interner) -> Option<String> {
        let file_name = Path::new(interner.lookup(self.0));

        file_name.get_sub_dir_divergence(mod_dir)
    }

    /// On top of separating the path into the module name and the file components,
    /// this will also strip any ".capy" at the end of a component,
    /// and will replace any '.' with a '-'
    ///
    /// TODO: maybe replace '.' with '\.'
    pub fn get_components<'a>(
        &'a self,
        mod_dir: &'a Path,
        interner: &'a Interner,
    ) -> FileNameComponents<'a, impl Iterator<Item = Cow<'a, str>>> {
        let file_name = Path::new(interner.lookup(self.0));
        let curr_dir = env::current_dir().unwrap();

        let is_mod = file_name.is_sub_dir_of(mod_dir);

        let relative_path = if is_mod {
            file_name.strip_prefix(mod_dir).unwrap()
        } else if file_name.is_sub_dir_of(&curr_dir) {
            file_name.strip_prefix(&curr_dir).unwrap()
        } else {
            dbg!(mod_dir);
            dbg!(curr_dir);
            dbg!(file_name);
            unreachable!()
        };

        let has_src = relative_path
            .components()
            .filter(|c| !matches!(c, Component::Prefix(_) | Component::RootDir))
            .nth(1)
            .and_then(|c| c.as_os_str().to_str())
            .is_some_and(|c| c == "src");

        let mut components = relative_path
            .components()
            .filter(|c| !matches!(c, Component::Prefix(_) | Component::RootDir))
            .map(|c| c.as_os_str().to_string_lossy())
            .map(|c| {
                if c.contains('.') {
                    let res = c.strip_suffix(".capy").unwrap_or(&c);

                    res.replace('.', "-").into()
                } else {
                    c
                }
            });

        let mod_name = if is_mod { components.next() } else { None };

        if has_src {
            components.next();
        }

        FileNameComponents {
            mod_name,
            sub_parts: components,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FileNameWithRange {
    pub file: FileName,
    pub range: TextRange,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(pub Key);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NameWithRange {
    pub name: Name,
    pub range: TextRange,
}

// short for Fully Qualified Name
// not only the name of whatever we're referring to, but also the file it's contained in.
pub type Fqn = NaiveGlobalLoc;

pub trait SubDir {
    fn is_sub_dir_of(&self, base: &Self) -> bool;

    // get_sub_dir_divergence("/hello/world/foo/bar", "/hello/world/")
    // would return "foo"
    fn get_sub_dir_divergence(&self, base: &Self) -> Option<String>;
}

impl SubDir for Path {
    fn is_sub_dir_of(&self, base: &Self) -> bool {
        let filter = |c: &Component| !matches!(c, Component::Prefix(_));

        let mut sub = self.components().filter(filter);

        base.components()
            .filter(filter)
            .all(|base| sub.next().is_some_and(|sub| sub == base))
    }

    /// This gets the name of the folder at which the sub directory is different
    /// thant the base directory.
    ///
    /// e.g.
    /// base = /users/gandalf/modules/
    /// sub = /users/ganlalf/modules/cool_stuff/hi
    ///
    /// this returns "cool_stuff"
    fn get_sub_dir_divergence(&self, base: &Self) -> Option<String> {
        let filter = |c: &Component| !matches!(c, Component::Prefix(_));

        let mut base = base.components().filter(filter);

        for sub in self.components().filter(filter) {
            match base.next() {
                Some(base) => {
                    if base != sub {
                        return None;
                    }
                }
                None => {
                    if let Component::Normal(name) = sub {
                        return Some(name.to_string_lossy().to_string());
                    } else {
                        return None;
                    }
                }
            }
        }

        None
    }
}

// pub struct FileNameComponents<'a, T: Iterator<Item = Cow<'a, str>>> {
//     pub mod_name: Option<Cow<'a, str>>,
//     pub sub_parts: T,
// }

// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
// pub struct FileName(pub Key);

// impl FileName {
//     pub fn to_string(&self, mod_dir: &Path, interner: &Interner) -> String {
//         let mut res = String::new();

//         let components = self.get_components(mod_dir, interner);

//         if let Some(mod_name) = &components.mod_name {
//             res.push_str(&mod_name);
//         }

//         for (idx, component) in components.sub_parts.enumerate() {
//             if idx == 0 && components.mod_name.is_some() {
//                 res.push_str("::");
//             } else if idx > 0 {
//                 res.push('.');
//             }

//             res.push_str(&component);
//         }

//         res
//     }

//     pub fn debug(&self, interner: &Interner) -> String {
//         interner.lookup(self.0).to_string()
//     }

//     pub fn is_mod(&self, mod_dir: &Path, interner: &Interner) -> bool {
//         let file_name = Path::new(interner.lookup(self.0));

//         file_name.is_sub_dir_of(mod_dir)
//     }

//     pub fn get_mod_name(&self, mod_dir: &Path, interner: &Interner) -> Option<String> {
//         let file_name = Path::new(interner.lookup(self.0));

//         file_name.get_sub_dir_divergence(mod_dir)
//     }

//     /// On top of separating the path into the module name and the file components,
//     /// this will also strip any ".capy" at the end of a component,
//     /// and will replace any '.' with a '-'
//     ///
//     /// TODO: maybe replace '.' with '\.'
//     pub fn get_components<'a>(
//         &'a self,
//         mod_dir: &'a Path,
//         interner: &'a Interner,
//     ) -> FileNameComponents<'a, impl Iterator<Item = Cow<'a, str>>> {
//         let file_name = Path::new(interner.lookup(self.0));
//         let curr_dir = env::current_dir().unwrap();

//         let is_mod = file_name.is_sub_dir_of(mod_dir);

//         let relative_path = if is_mod {
//             file_name.strip_prefix(mod_dir).unwrap()
//         } else if file_name.is_sub_dir_of(&curr_dir) {
//             file_name.strip_prefix(curr_dir).unwrap()
//         } else {
//             unreachable!()
//         };

//         let mut components = relative_path
//             .components()
//             .filter(|c| !matches!(c, Component::Prefix(_) | Component::RootDir))
//             .map(|c| c.as_os_str().to_string_lossy())
//             .map(|c| {
//                 if c.contains('.') {
//                     let res = c.strip_suffix(".capy").unwrap_or(&c);

//                     res.replace('.', "-").into()
//                 } else {
//                     c
//                 }
//             });

//         let mod_name = if is_mod { components.next() } else { None };

//         FileNameComponents {
//             mod_name,
//             sub_parts: components,
//         }
//     }
// }

// #[derive(Debug, Clone, Copy, PartialEq, Eq)]
// pub struct FileNameWithRange {
//     pub file: FileName,
//     pub range: TextRange,
// }

// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
// pub struct Name(pub Key);

// #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
// pub struct NameWithRange {
//     pub name: Name,
//     pub range: TextRange,
// }

// // short for Fully Qualified Name
// // not only the name of whatever we're referring to, but also the file it's contained in.
// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
// pub struct Fqn {
//     pub file: FileName,
//     pub name: Name,
// }

// impl Fqn {
//     pub fn to_string(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
//         format!(
//             r#"{}::{}"#,
//             self.file.to_string(mod_dir, interner),
//             interner.lookup(self.name.0),
//         )
//     }

//     pub fn debug(&self, interner: &Interner) -> String {
//         format!(
//             r#"{}::{}"#,
//             self.file.debug(interner),
//             interner.lookup(self.name.0),
//         )
//     }
// }

// pub trait SubDir {
//     fn is_sub_dir_of(&self, base: &Self) -> bool;

//     // get_sub_dir_divergence("/hello/world/foo/bar", "/hello/world/")
//     // would return "foo"
//     fn get_sub_dir_divergence(&self, base: &Self) -> Option<String>;
// }

// impl SubDir for Path {
//     fn is_sub_dir_of(&self, base: &Self) -> bool {
//         let filter = |c: &Component| !matches!(c, Component::Prefix(_));

//         let mut sub = self.components().filter(filter);

//         base.components()
//             .filter(filter)
//             .all(|base| sub.next().is_some_and(|sub| sub == base))
//     }

//     /// This gets the name of the folder at which the sub directory is different
//     /// thant the base directory.
//     ///
//     /// e.g.
//     /// base = /users/gandalf/modules/
//     /// sub = /users/ganlalf/modules/cool_stuff/hi
//     ///
//     /// this returns "cool_stuff"
//     fn get_sub_dir_divergence(&self, base: &Self) -> Option<String> {
//         let filter = |c: &Component| !matches!(c, Component::Prefix(_));

//         let mut base = base.components().filter(filter);

//         for sub in self.components().filter(filter) {
//             match base.next() {
//                 Some(base) => {
//                     if base != sub {
//                         return None;
//                     }
//                 }
//                 None => {
//                     if let Component::Normal(name) = sub {
//                         return Some(name.to_string_lossy().to_string());
//                     } else {
//                         return None;
//                     }
//                 }
//             }
//         }

//         None
//     }
// }
