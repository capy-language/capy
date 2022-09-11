
use std::{io::{self, Write}, process::exit};

fn main() -> io::Result<()> {
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut stderr = io::stderr();

    let mut input = String::new();
    let mut env = capy::Env::default();

    loop {
        write!(stdout, "> ")?;
        stdout.flush()?;

        stdin.read_line(&mut input)?;
        
        match run(&input.trim(), &mut env) {
            Ok(Some(val)) => writeln!(stdout, "{}", val)?,
            Ok(None) => {},
            Err(msg) => writeln!(stderr, "{}", msg)?,
        }

        input.clear();
    }
}

fn run(input: &str, env: &mut capy::Env) -> Result<Option<capy::Val>, String> {
    if input == "exit()" {
        println!("goodbye");
        exit(0);
    }
    let parse = capy::parse(input).map_err(|msg| format!("Parse Error: {}", msg))?;

    let evaluated = parse
        .eval(env)
        .map_err(|msg| format!("Evaluation Error: {}", msg))?;
    if evaluated == capy::Val::Null {
        Ok(None)
    } else {
        Ok(Some(evaluated))
    }
}
