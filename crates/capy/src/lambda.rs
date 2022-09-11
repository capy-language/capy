use crate::{stmt::Stmt, utils};


#[derive(Debug, PartialEq, Clone)]
pub struct Lambda {
    pub(crate) params: Vec<String>,
    pub(crate) body: Box<Stmt>,
}

impl Lambda {
    pub(crate) fn new(s: &str) -> Result<(&str, Self), String> {
        let s = utils::tag("(", s)?;
        let (s, _) = utils::extract_whitespace(s);

        let mut s = s;
        let mut params = Vec::new();
        let mut used_comma = true;

        while let Ok((new_s, param)) = utils::extract_ident(s) {
            if !used_comma {
                return Err("expected comma to separate parameters".to_string());
            }

            params.push(param.to_string());

            let (new_s, _) = utils::extract_whitespace(new_s);

            let new_s = utils::tag(",", new_s).unwrap_or_else(|_| {
                used_comma = false;
                new_s
            });

            let (new_s, _) = utils::extract_whitespace(new_s);
            s = new_s;
        }

        let s = utils::tag(")", s)?;
        let (s, _) = utils::extract_whitespace(s);

        let (s, body) = Stmt::new(s)?;

        Ok((s, Lambda { 
            params,
            body: Box::new(body),
        }))
    }
}

#[cfg(test)]
mod tests {
    use crate::expr::{Expr, binding_usage::BindingUsage, block::Block};

    use super::*;

    #[test]
    fn parse_empty_lambda() {
        assert_eq!(
            Lambda::new("( ) { }"),
            Ok((
                "",
                Lambda {
                    params: Vec::new(),
                    body: Box::new(Stmt::Expr(Expr::Block(Block { stmts: Vec::new() }))),
                }
            ))
        );
    }

    #[test]
    fn parse_lambda_with_one_param() {
        assert_eq!(
            Lambda::new("( x ) { x }"),
            Ok((
                "",
                Lambda {
                    params: vec![
                        "x".to_string()
                    ],
                    body: Box::new(Stmt::Expr(Expr::Block(Block { 
                        stmts: vec![
                            Stmt::Expr(Expr::BindingUsage(BindingUsage {
                                name: "x".to_string()
                            }))
                        ] 
                    }))),
                }
            ))
        );
    }

    #[test]
    fn parse_lambda_with_multiple_params() {
        // assert_eq!(
        //     Lambda::new("( x , y ) { x + y }"),
        //     Ok((
        //         "",
        //         Lambda {
        //             params: vec![
        //                 "x".to_string(),
        //                 "y".to_string(),
        //                 "z".to_string()
        //             ],
        //             body: Box::new(Stmt::Expr(Expr::Block(Block { 
        //                 stmts: vec![
        //                     Stmt::Expr(Expr::Operation {
        //                         lhs: Expr::BindingUsage(BindingUsage {
        //                             name: "x".to_string()
        //                         }),
        //                         rhs: Expr::BindingUsage(BindingUsage {
        //                             name: "y".to_string()
        //                         }),
        //                         op: Op::Add
        //                     })
        //                 ] 
        //             }))),
        //         }
        //     ))
        // );
    }

}