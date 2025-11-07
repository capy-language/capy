use interner::Interner;
use internment::Intern;
use la_arena::{Idx, IdxRange};
use rustc_hash::FxHashMap;

use crate::{Comptime, Expr, Lambda, common::get_naive_lambda_global};

use super::{FileName, Name, Ty};

// todo: I want to make this more expansive. `Data` should be removed and
// there should be variants for structs, arrays, etc. This will allow indexing
// and member access at compile-time.
#[derive(Debug, Clone, PartialEq)]
pub enum ComptimeResult {
    Type(Intern<Ty>),
    Integer { num: u64, bit_width: u8 },
    Float { num: f64, bit_width: u8 },
    Data(Box<[u8]>),
    Void,
}

#[derive(Debug, Default)]
pub struct ComptimeResultMap(FxHashMap<ComptimeLoc, ComptimeResult>);

impl std::ops::Index<ComptimeLoc> for ComptimeResultMap {
    type Output = ComptimeResult;

    fn index(&self, fq_comptime: ComptimeLoc) -> &Self::Output {
        &self.0[&fq_comptime]
    }
}

impl ComptimeResultMap {
    pub fn all_blocks(&self) -> impl Iterator<Item = &ComptimeLoc> {
        self.0.keys()
    }

    pub fn all_results(&self) -> impl Iterator<Item = &ComptimeResult> {
        self.0.values()
    }

    pub fn get(&self, fq_comptime: ComptimeLoc) -> Option<&ComptimeResult> {
        self.0.get(&fq_comptime)
    }

    pub fn contains(&self, fq_comptime: ComptimeLoc) -> bool {
        self.0.contains_key(&fq_comptime)
    }

    #[track_caller]
    pub fn insert(&mut self, fq_comptime: ComptimeLoc, result: ComptimeResult) {
        assert!(!self.0.contains_key(&fq_comptime));

        self.0.insert(fq_comptime, result);
    }
}

// A list of comptime results (compile-time known values)
// including types, which, along with a global's name, determine
// its absolute type.
//
// Generics
#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct ComptimeArgs {
    start: Idx<ComptimeResult>,
    end: Idx<ComptimeResult>,
}

impl ComptimeArgs {
    pub fn new(vals: IdxRange<ComptimeResult>) -> Self {
        Self {
            start: vals.start(),
            end: vals.end(),
        }
    }

    pub fn into_value_range(self) -> IdxRange<ComptimeResult> {
        IdxRange::new(self.start..self.end)
    }

    pub fn raw_start(self) -> u32 {
        self.start.into_raw().into_u32()
    }

    pub fn raw_end(self) -> u32 {
        self.end.into_raw().into_u32()
    }
}

// -----------------------------------------------------------
// --- Code Locations Based on Name & Not Monomorphization ---
// -----------------------------------------------------------

/// See `ConcreteLoc` for the reason why these two structs exist
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NaiveLoc {
    Global(NaiveGlobalLoc),
    Lambda(NaiveLambdaLoc),
}

impl NaiveLoc {
    pub fn file(&self) -> FileName {
        match self {
            NaiveLoc::Global(global) => global.file,
            NaiveLoc::Lambda(lambda) => lambda.file,
        }
    }

    pub fn debug(self, interner: &Interner) -> String {
        match self {
            NaiveLoc::Global(global) => global.debug(interner),
            NaiveLoc::Lambda(lambda) => lambda.debug(interner),
        }
    }

    pub fn to_string(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        match self {
            NaiveLoc::Global(global) => global.to_string(mod_dir, interner),
            NaiveLoc::Lambda(lambda) => lambda.to_string(mod_dir, interner),
        }
    }

    pub const fn make_concrete(self, comptime_args: Option<ComptimeArgs>) -> ConcreteLoc {
        match self {
            NaiveLoc::Global(global) => ConcreteLoc::Global(global.make_concrete(comptime_args)),
            NaiveLoc::Lambda(lambda) => ConcreteLoc::Lambda(lambda.make_concrete(comptime_args)),
        }
    }

    pub fn as_global(self) -> Option<NaiveGlobalLoc> {
        match self {
            NaiveLoc::Global(global) => Some(global),
            NaiveLoc::Lambda(_) => None,
        }
    }

    pub fn as_lambda(self) -> Option<NaiveLambdaLoc> {
        match self {
            NaiveLoc::Lambda(lambda) => Some(lambda),
            NaiveLoc::Global(_) => None,
        }
    }
}

impl PartialOrd for NaiveLoc {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NaiveLoc {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        fn resolve_if_possible(loc: &NaiveLoc) -> NaiveLoc {
            match loc {
                NaiveLoc::Global(_) => *loc,
                NaiveLoc::Lambda(lambda) => {
                    get_naive_lambda_global(*lambda).map_or(*loc, |g| g.wrap())
                }
            }
        }

        let cmp_variants =
            |left: &Self, right: &Self, res: &dyn Fn(std::cmp::Ordering) -> std::cmp::Ordering| {
                match (left, right) {
                    (NaiveLoc::Global(l_global), NaiveLoc::Global(r_global)) => {
                        res(l_global.cmp(&r_global))
                    }
                    (NaiveLoc::Lambda(l_lambda), NaiveLoc::Lambda(r_lambda)) => {
                        res(l_lambda.cmp(&r_lambda))
                    }
                    (NaiveLoc::Global(_), NaiveLoc::Lambda(_)) => std::cmp::Ordering::Less,
                    (NaiveLoc::Lambda(_), NaiveLoc::Global(_)) => std::cmp::Ordering::Greater,
                }
            };

        self.file().cmp(&other.file()).then_with(|| {
            cmp_variants(
                &resolve_if_possible(self),
                &resolve_if_possible(other),
                &|ordering| ordering.then_with(|| cmp_variants(self, other, &|ordering| ordering)),
            )
        })
    }
}

impl From<NaiveGlobalLoc> for NaiveLoc {
    fn from(value: NaiveGlobalLoc) -> Self {
        Self::Global(value)
    }
}

impl From<NaiveLambdaLoc> for NaiveLoc {
    fn from(value: NaiveLambdaLoc) -> Self {
        Self::Lambda(value)
    }
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct NaiveGlobalLoc {
    pub file: FileName,
    pub name: Name,
}

impl NaiveGlobalLoc {
    pub fn file(self) -> FileName {
        self.file
    }

    pub fn name(self) -> Name {
        self.name
    }

    pub fn debug(&self, interner: &Interner) -> String {
        format!(
            r#"{}::{}"#,
            self.file.debug(interner),
            interner.lookup(self.name.0),
        )
    }

    pub fn to_string(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        format!(
            r#"{}::{}"#,
            self.file.to_string(mod_dir, interner),
            interner.lookup(self.name.0),
        )
    }

    pub fn wrap(self) -> NaiveLoc {
        NaiveLoc::Global(self)
    }

    pub const fn make_concrete(self, comptime_args: Option<ComptimeArgs>) -> ConcreteGlobalLoc {
        ConcreteGlobalLoc {
            naive_loc: self,
            comptime_args,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct NaiveLambdaLoc {
    pub file: FileName,
    pub expr: Idx<Expr>,
    pub lambda: Idx<Lambda>,
}

impl NaiveLambdaLoc {
    pub fn file(self) -> FileName {
        self.file
    }

    pub fn expr(self) -> Idx<Expr> {
        self.expr
    }

    pub fn lambda(self) -> Idx<Lambda> {
        self.lambda
    }

    pub fn debug(self, interner: &Interner) -> String {
        match get_naive_lambda_global(self) {
            Some(naive_global) => {
                assert_eq!(naive_global.file, self.file);
                format!(
                    "{}::lambda#{}",
                    self.file.debug(interner),
                    interner.lookup(naive_global.name.0),
                )
            }
            None => format!(
                "{}::lambda#{}",
                self.file.debug(interner),
                self.expr.into_raw(),
            ),
        }
    }

    pub fn to_string(self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        match get_naive_lambda_global(self) {
            Some(naive_global) => {
                assert_eq!(naive_global.file, self.file);
                format!(
                    "{}::lambda#{}",
                    self.file.to_string(mod_dir, interner),
                    interner.lookup(naive_global.name.0),
                )
            }
            None => format!(
                "{}::lambda#{}",
                self.file.to_string(mod_dir, interner),
                self.expr.into_raw(),
            ),
        }
    }

    pub fn wrap(self) -> NaiveLoc {
        NaiveLoc::Lambda(self)
    }

    pub const fn make_concrete(self, comptime_args: Option<ComptimeArgs>) -> ConcreteLambdaLoc {
        ConcreteLambdaLoc {
            naive_loc: self,
            comptime_args,
        }
    }
}

// -------------------------------------
// --- Fully Typed and Monomorphized ---
// -------------------------------------

/// Currently, the way things are stored is that each separate "version"
/// of each separate function and global has its own map of its inner expression types.
///
/// E.g. for the following code:
/// ```my_code.capy
/// add :: (comptime T: type) {
///     foo: T = 2;
///     bar: T = 2;
///
///     foo + bar;
/// }
///
/// main :: () {
///     add(i32);
///     add(f64);
/// }
/// ```
///
/// There are four "naive locations"
/// ```text
/// my_code::add
/// my_code::lambda#0 (the lambda in the `add` global)
/// my_code::main
/// my_code::lambda#1 (the lambda in the `main` global)
/// ```
///
/// But there are actually six "concrete" locations,
/// at which you can find a map of expression types
/// ```text
/// my_code::add
/// my_code::lambda#0<i32>
/// my_code::lambda#0<f64>
/// my_code::main
/// my_code::lambda#1
/// ```
/// The reason two maps are created for both the `T = i32` and `T = f64` versions of `add`
/// is because depending on the value of `T`, the types of the inner expressions such as `foo`
/// and `bar` will actually change drastically. All forms of the function need to be stored in order
/// to do codegen.
///
/// TODO! make sure that the above doesn't actually happen, and that it's two version of add
/// instead of three
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConcreteLoc {
    Global(ConcreteGlobalLoc),
    Lambda(ConcreteLambdaLoc),
}

impl ConcreteLoc {
    pub fn file(self) -> FileName {
        match self {
            ConcreteLoc::Global(global) => global.naive_loc.file,
            ConcreteLoc::Lambda(lambda) => lambda.naive_loc.file,
        }
    }

    pub fn comptime_args(self) -> Option<ComptimeArgs> {
        match self {
            ConcreteLoc::Global(global) => global.comptime_args,
            ConcreteLoc::Lambda(lambda) => lambda.comptime_args,
        }
    }

    pub fn debug(self, interner: &Interner) -> String {
        match self {
            ConcreteLoc::Global(global) => global.debug(interner),
            ConcreteLoc::Lambda(lambda) => lambda.debug(interner),
        }
    }

    pub fn to_string(self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        match self {
            ConcreteLoc::Global(global) => global.to_string(mod_dir, interner),
            ConcreteLoc::Lambda(lambda) => lambda.to_string(mod_dir, interner),
        }
    }

    pub fn to_naive(self) -> NaiveLoc {
        match self {
            ConcreteLoc::Global(global) => global.to_naive().into(),
            ConcreteLoc::Lambda(lambda) => lambda.to_naive().into(),
        }
    }

    pub fn as_global(self) -> Option<ConcreteGlobalLoc> {
        match self {
            ConcreteLoc::Global(global) => Some(global),
            ConcreteLoc::Lambda(_) => None,
        }
    }

    pub fn as_lambda(self) -> Option<ConcreteLambdaLoc> {
        match self {
            ConcreteLoc::Lambda(lambda) => Some(lambda),
            ConcreteLoc::Global(_) => None,
        }
    }
}

impl PartialOrd for ConcreteLoc {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ConcreteLoc {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.to_naive()
            .cmp(&other.to_naive())
            .then_with(|| self.comptime_args().cmp(&other.comptime_args()))
    }
}

impl From<ConcreteGlobalLoc> for ConcreteLoc {
    fn from(value: ConcreteGlobalLoc) -> Self {
        Self::Global(value)
    }
}

impl From<ConcreteLambdaLoc> for ConcreteLoc {
    fn from(value: ConcreteLambdaLoc) -> Self {
        Self::Lambda(value)
    }
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct ConcreteGlobalLoc {
    naive_loc: NaiveGlobalLoc,
    comptime_args: Option<ComptimeArgs>,
}

impl ConcreteGlobalLoc {
    pub fn to_naive(self) -> NaiveGlobalLoc {
        self.naive_loc
    }

    pub fn file(self) -> FileName {
        self.naive_loc.file
    }

    pub fn name(self) -> Name {
        self.naive_loc.name
    }

    pub fn comptime_args(self) -> Option<ComptimeArgs> {
        self.comptime_args
    }

    pub fn debug(self, interner: &Interner) -> String {
        match self.comptime_args {
            Some(comptime_args) => format!(
                "{}<{}>",
                self.naive_loc.debug(interner),
                comptime_args.raw_start()
            ),
            None => self.naive_loc.debug(interner),
        }
    }

    pub fn to_string(self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        match self.comptime_args {
            Some(comptime_args) => {
                format!(
                    "{}<{}>",
                    self.naive_loc.to_string(mod_dir, interner),
                    comptime_args.raw_start()
                )
            }
            None => self.naive_loc.to_string(mod_dir, interner),
        }
    }

    pub fn wrap(self) -> ConcreteLoc {
        ConcreteLoc::Global(self)
    }
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct ConcreteLambdaLoc {
    naive_loc: NaiveLambdaLoc,
    comptime_args: Option<ComptimeArgs>,
    // todo: *maybe* this could include a name for aesthetic purposes,
    // but I don't think it's necessary for now
}

impl ConcreteLambdaLoc {
    pub fn to_naive(self) -> NaiveLambdaLoc {
        self.naive_loc
    }

    pub fn file(self) -> FileName {
        self.naive_loc.file
    }

    pub fn expr(self) -> Idx<Expr> {
        self.naive_loc.expr
    }

    pub fn lambda(self) -> Idx<Lambda> {
        self.naive_loc.lambda
    }

    pub fn comptime_args(self) -> Option<ComptimeArgs> {
        self.comptime_args
    }

    pub fn debug(self, interner: &Interner) -> String {
        match self.comptime_args {
            Some(comptime_args) => format!(
                "{}<{}>",
                self.to_naive().debug(interner),
                comptime_args.raw_start()
            ),
            None => self.to_naive().debug(interner),
        }
    }

    pub fn to_string(self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        match self.comptime_args {
            Some(comptime_args) => format!(
                "{}<{}>",
                self.to_naive().to_string(mod_dir, interner),
                comptime_args.raw_start()
            ),
            None => self.to_naive().to_string(mod_dir, interner),
        }
    }

    pub fn wrap(self) -> ConcreteLoc {
        ConcreteLoc::Lambda(self)
    }
}

// -------------------------------------

/// Unlike lambda's and functions, comptimes are pretty much just blocks.
/// They don't really inherently store code that's meant to be unaccessable to the outside world.
/// So comptimes are stored in lambda and global concrete locations.
#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct ComptimeLoc {
    pub loc: ConcreteLoc,
    pub expr: Idx<Expr>,
    pub comptime: Idx<Comptime>,
}
