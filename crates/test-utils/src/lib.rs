use rustc_hash::FxHashMap;

pub fn split_multi_module_test_data(input: &str) -> FxHashMap<&str, &str> {
    const MARKER_COMMENT_START: &str = "#- ";

    let has_no_marker_comments = !input.contains(MARKER_COMMENT_START);
    if has_no_marker_comments {
        let mut modules = FxHashMap::default();
        modules.insert("main", input);
        return modules;
    }

    let mut module_idxs = FxHashMap::default();
    let mut current_module_name = None;
    let mut line_idxs = input.match_indices('\n').map(|(idx, _)| idx + 1).peekable();

    while let Some(line_start) = line_idxs.next() {
        let line_end = match line_idxs.peek() {
            Some(end) => *end,
            None => break,
        };

        let line = &input[line_start..line_end];
        if let Some(idx) = line.find(MARKER_COMMENT_START) {
            let module_name_start = idx + MARKER_COMMENT_START.len();
            let module_name_end = line.len() - 1; // remove newline

            let module_name = &line[module_name_start..module_name_end];

            module_idxs.insert(module_name, line_end..line_end);
            current_module_name = Some(module_name);
        }

        module_idxs.get_mut(&current_module_name.unwrap()).unwrap().end = line_end;
    }

    module_idxs.into_iter().map(|(module_name, range)| (module_name, &input[range])).collect()
}
