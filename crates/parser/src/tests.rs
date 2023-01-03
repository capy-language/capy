use crate::Parse;
use expect_test::expect_file;
use std::collections::HashMap;
use std::ffi::OsStr;
use std::{env, fs};
use token::Tokens;

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

    let mut did_any_test_fail = false;
    let mut test_results = HashMap::new();

    for file in fs::read_dir(tests_dir).unwrap() {
        let path = file.unwrap().path();
        let file_name = path.file_name().unwrap().to_owned();

        if path.extension() != Some(OsStr::new("test")) {
            continue;
        }

        let did_panic = std::panic::catch_unwind(|| {
            let test_content = fs::read_to_string(&path)
                .unwrap()
                .replace("\r", "");
            let (input, _expected_parse) = test_content.split_once("\n===\n").unwrap();

            let actual_parse = {
                let tokens = &lexer::lex(input);
                parsing_fn(&tokens, input)
            };

            let expected_test_content = format!("{}\n===\n{:?}\n", input, actual_parse);

            expect_file![path].assert_eq(&expected_test_content);
        })
        .is_err();

        if did_panic {
            did_any_test_fail = true;
        }

        test_results.insert(file_name, did_panic);
    }

    if did_any_test_fail {
        let longest_name = 
            test_results
            .keys()
            .map(|path| path.len() - ".test".len())
            .max()
            .unwrap();

        const ANSI_RESET: &str = "\x1B[0m";
        const ANSI_RED: &str = "\x1B[31m";
        const ANSI_GREEN: &str = "\x1B[32m";

        let mut fails = 0;
        for (path, failed) in test_results {
            println!(
                "{: <longest_name$} ... {}{}{}",
                path.to_str().unwrap().split_once(".").unwrap().0,
                if failed { ANSI_RED } else { ANSI_GREEN },
                if failed { "FAILED" } else { "ok" },
                ANSI_RESET);
            if failed {
                fails += 1;
            }
        }
        println!();
        panic!("{} parser tests failed", fails);
    }
}