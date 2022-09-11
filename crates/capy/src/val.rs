
use std::fmt;

use crate::{stmt::Stmt, lambda::Lambda};

#[derive(Debug, Clone, PartialEq)]
pub enum Val {
    Number(i32),
    Lambda(Lambda),
    Null,
}

impl Val {
    pub(crate) fn lambda(self) -> Result<Lambda, String> {
        if let Val::Lambda(lambda) = self { Ok(lambda) } else { Err("expected lambda".to_string()) }
    }

    fn number(self) -> Result<i32, String> {
        if let Val::Number(number) = self { Ok(number) } else { Err("expected number".to_string()) }
    }
}

impl fmt::Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Number(n) => write!(f, "{}", n),
            Self::Lambda(Lambda { params, body }) => write!(f, "({}) {{}}", params.join(", ")),
            Self::Null => write!(f, "Null"),
        }
    }
}