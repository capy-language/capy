mod binding_def;
mod expr;
mod val;
mod stmt;
mod env;
mod utils;

pub use env::Env;
pub use val::Val;

pub struct Parse(stmt::Stmt);

fn parse(s: &str) -> Result<Parse, String> {
    let (s, stmt) = stmt::Stmt::new(s)?;

    if s.is_empty() {
        Ok(Parse(stmt))
    } else {
        Err("input was not consumed fully by parser".to_string())
    }
}

impl Parse {
    pub fn eval(&self, env: &mut Env) -> Result<Val, String> {
        self.0.eval(env)
    }
}
