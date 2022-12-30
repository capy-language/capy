use std::io::{self, Write};

use parser::parse;

fn main() -> io::Result<()> {
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    //let mut stderr = io::stderr();

    let mut input = String::new();

    loop {
        write!(stdout, "> ")?;
        stdout.flush()?;

        stdin.read_line(&mut input)?;

        let parse = parse(&input);
        writeln!(stdout, "{}", parse.debug_tree())?;

        let syntax = parse.syntax();

        for error in ast::validation::validate(&syntax) {
            println!("{}", error);
        }

        let root = ast::Root::cast(syntax).unwrap();

        let ast_vals = root
            .stmts()
            .filter_map(|stmt| if let ast::Stmt::VariableDef(var_def) = stmt {
                Some(var_def.value())
            } else if let ast::Stmt::Return(ret) = stmt {
                Some(ret.value())
            } else {
                None
            })
            .collect::<Vec<_>>();
        dbg!(ast_vals);

        dbg!(hir::lower(root));

        input.clear();
    }
}
