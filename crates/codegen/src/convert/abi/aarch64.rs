// TODO: other kinds of aarch64 abis then apple

use hir_ty::Ty;
use internment::Intern;

use super::PassMode;

/// "A Homogeneous Floating-point Aggregate (HFA) is a Homogeneous Aggregate with a Fundamental Data Type that is a Floating-Point type and at most four uniquely addressable members."
pub fn is_hfa(ty: Intern<Ty>) -> Option<PassMode> {
    todo!()
}