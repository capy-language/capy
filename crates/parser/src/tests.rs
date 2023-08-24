use crate::Parse;
use core::panic;
use expect_test::expect_file;
use std::collections::HashMap;
use std::ffi::OsStr;
use std::{env, fs, thread};
use token::Tokens;

#[derive(Debug, PartialEq)]
enum RunResult {
    Ok,
    Panic,
    Hung,
}

#[test]
fn source_file() {
    run_parser_tests("source_file", crate::parse_source_file)
}

#[test]
fn repl_line() {
    run_parser_tests("repl_line", crate::parse_repl_line)
}

fn run_parser_tests(tests_dir: &str, parsing_fn: fn(&Tokens, &str) -> Parse) {
    let tests_dir = {
        let current_dir = env::current_dir().unwrap();
        current_dir.join(format!("src/tests/{}", tests_dir))
    };

    let mut test_results = HashMap::new();

    for file in fs::read_dir(tests_dir).unwrap() {
        let path = file.as_ref().unwrap().path();
        let file_name = path.file_name().unwrap().to_owned();

        if path.extension() != Some(OsStr::new("test")) {
            continue;
        }

        let timer = timer::Timer::new();
        let (tx, rx) = std::sync::mpsc::channel::<RunResult>();

        let tx_ = tx.clone();
        let _guard = timer.schedule_with_delay(chrono::Duration::seconds(1), move || {
            tx_.send(RunResult::Hung).unwrap();
        });

        let tx_ = tx.clone();
        thread::spawn(move || {
            let panic = std::panic::catch_unwind(|| {
                let test_content = fs::read_to_string(&path).unwrap().replace("\r", "");
                let (input, _expected_parse) = test_content.split_once("\n===\n").unwrap();

                let actual_parse = {
                    let tokens = &lexer::lex(input);
                    parsing_fn(&tokens, input)
                };

                let expected_test_content = format!("{}\n===\n{:?}\n", input, actual_parse);

                expect_file![path].assert_eq(&expected_test_content);

                //drop(timer);
            })
            .is_err();

            tx_.send(if panic {
                RunResult::Panic
            } else {
                RunResult::Ok
            })
            .unwrap();
        });

        let result = rx.recv().unwrap();

        test_results.insert(file_name, result);
    }

    let longest_name = test_results
        .keys()
        .map(|path| path.len() - ".test".len())
        .max()
        .unwrap();

    const ANSI_RESET: &str = "\x1B[0m";
    const ANSI_RED: &str = "\x1B[31m";
    const ANSI_GREEN: &str = "\x1B[32m";

    let mut fails = 0;
    for (path, result) in test_results {
        let (color, name) = match result {
            RunResult::Ok => (ANSI_GREEN, "ok"),
            RunResult::Panic => (ANSI_RED, "FAILED"),
            RunResult::Hung => (ANSI_RED, "HUNG"),
        };
        println!(
            "{: <longest_name$} ... {}{}{}",
            path.to_str().unwrap().split_once(".").unwrap().0,
            color,
            name,
            ANSI_RESET
        );
        if result != RunResult::Ok {
            fails += 1;
        }
    }
    println!();
    if fails == 1 {
        panic!("1 parser test failed");
    } else if fails > 1 {
        panic!("{} parser tests failed", fails);
    }
}
