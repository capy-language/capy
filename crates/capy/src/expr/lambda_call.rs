
use super::*;

#[derive(Debug, PartialEq, Clone)]
pub struct LambdaCall {
    pub callee: String,
    pub args: Vec<Expr>,
}

impl LambdaCall {
    pub(crate) fn new(s: &str) -> Result<(&str, Self), String> {
        let (s, callee) = utils::extract_ident(s)?;
        let (s, _) = utils::extract_whitespace(s);

        let s = utils::tag("(", s)?;
        let (s, _) = utils::extract_whitespace(s);

        let (s, args) = utils::comma_sequence(Expr::new_non_lambda, s)?;
        let (s, _) = utils::extract_whitespace(s);

        let s = utils::tag(")", s)?;

        Ok((
            s,
            Self {
                callee: callee.to_string(),
                args,
            },
        ))
    }

    pub fn eval(&self, env: &Env) -> Result<Val, String> {
        let mut child_env = env.create_child();

        let Lambda { params, body } = env.get_binding_value(&self.callee)?.lambda()?;

        if params.len() != self.args.len() {
            return Err(format!(
                "expected {} arguments, got {}",
                params.len(), self.args.len(),
            ))
        }
        
        for (param_name, arg_expr) in params.into_iter().zip(&self.args) {
            let arg_val = arg_expr.eval(&child_env)?;
            child_env.store_binding(param_name, arg_val);
        }
        
        body.eval(&mut child_env)
    }
}

#[cfg(test)]
mod tests {
    use crate::stmt::Stmt;

    use super::*;

    #[test]
    fn parse_call_with_no_params() {
       assert_eq!(
           LambdaCall::new("greet_user()"),
           Ok((
               "",
               LambdaCall {
                   callee: "greet_user".to_string(),
                   args: Vec::new(),
               }
           ))
       );
    }

    #[test]
    fn parse_call_with_one_param() {
        assert_eq!(
            LambdaCall::new("square(5)"),
            Ok((
                "",
                LambdaCall {
                    callee: "square".to_string(),
                    args: vec![
                        Expr::Number(Number(5)),
                    ],
                }
            ))
        );
    }

    #[test]
    fn parse_call_with_multiple_params() {
        assert_eq!(
            LambdaCall::new("sum(1, 2)"),
            Ok((
                "",
                LambdaCall {
                    callee: "sum".to_string(),
                    args: vec![
                        Expr::Number(Number(1)),
                        Expr::Number(Number(2)),
                    ],
                }
            ))
        );
    }

    #[test]
    fn eval_call() {
        let mut env = Env::default();

        env.store_binding(
            "id".to_string(),
            Val::Lambda(Lambda {
                params: vec!["x".to_string()],
                body: Box::new(Stmt::Expr(Expr::BindingUsage(BindingUsage {
                    name: "x".to_string()
                })))
            })
        );
        assert_eq!(
            LambdaCall {
                callee: "id".to_string(),
                args: vec![Expr::Number(Number(10))]
            }
            .eval(&env),
            Ok(Val::Number(10))
        );
    }

    #[test]
    fn eval_non_existent_call() {
        assert_eq!(
            LambdaCall {
                callee: "i_dont_exist".to_string(),
                args: vec![Expr::Number(Number(1))]
            }
            .eval(&Env::default()),
            Err("binding with name 'i_dont_exist' does not exist".to_string())
        );
    }

    #[test]
    fn eval_with_too_few_args() {
        let mut env = Env::default();

        env.store_binding(
            "sum".to_string(),
            Val::Lambda(Lambda {
                params: vec![
                    "x".to_string(),
                    "y".to_string()
                ],
                body: Box::new(Stmt::Expr(Expr::Operation { 
                    lhs: Box::new(Expr::BindingUsage(BindingUsage {
                        name: "x".to_string()
                    })),
                    rhs: Box::new(Expr::BindingUsage(BindingUsage {
                        name: "y".to_string()
                    })),
                    op: Op::Add
                }))
            })
        );
        assert_eq!(
            LambdaCall {
                callee: "sum".to_string(),
                args: vec![Expr::Number(Number(2))],
            }
            .eval(&env),
            Err("expected 2 arguments, got 1".to_string())
        );
    }

    #[test]
    fn eval_with_too_many_args() {
        let mut env = Env::default();

        env.store_binding(
            "sum".to_string(),
            Val::Lambda(Lambda {
                params: vec![
                    "x".to_string(),
                    "y".to_string()
                ],
                body: Box::new(Stmt::Expr(Expr::Operation { 
                    lhs: Box::new(Expr::BindingUsage(BindingUsage {
                        name: "x".to_string()
                    })),
                    rhs: Box::new(Expr::BindingUsage(BindingUsage {
                        name: "y".to_string()
                    })),
                    op: Op::Add
                }))
            })
        );
        assert_eq!(
            LambdaCall {
                callee: "sum".to_string(),
                args: vec![
                    Expr::Number(Number(2)),
                    Expr::Number(Number(3)),
                    Expr::Number(Number(4)),
                ],
            }
            .eval(&env),
            Err("expected 2 arguments, got 3".to_string())
        );
    }
}