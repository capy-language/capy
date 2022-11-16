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

        let root = ast::Root::cast(parse.syntax()).unwrap();

        dbg!(root
            .stmts()
            .filter_map(|stmt| if let ast::Stmt::VariableDef(var_def) = stmt {
                Some(var_def.value())
            } else {
                None
            })
            .collect::<Vec<_>>());

        dbg!(hir::lower(root));

        input.clear();
    }
}
