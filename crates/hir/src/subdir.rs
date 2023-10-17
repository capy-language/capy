use std::path::{Component, Path};

pub trait SubDir {
    fn is_sub_dir_of(&self, base: &Self) -> bool;

    // get_sub_dir_divergence("/hello/world/foo/bar", "/hello/world/")
    // would return "foo"
    fn get_sub_dir_divergence(&self, base: &Self) -> Option<String>;
}

impl SubDir for Path {
    fn is_sub_dir_of(&self, base: &Self) -> bool {
        let filter = |c: &Component| !matches!(c, Component::Prefix(_));

        let mut sub = self.components().filter(filter);

        base.components()
            .filter(filter)
            .all(|base| sub.next().map_or(false, |sub| sub == base))
    }

    fn get_sub_dir_divergence(&self, base: &Self) -> Option<String> {
        let filter = |c: &Component| !matches!(c, Component::Prefix(_));

        let mut base = base.components().filter(filter);

        for sub in self.components().filter(filter) {
            match base.next() {
                Some(base) => {
                    if base != sub {
                        return None;
                    }
                }
                None => {
                    if let Component::Normal(name) = sub {
                        return Some(name.to_string_lossy().to_string());
                    } else {
                        return None;
                    }
                }
            }
        }

        None
    }
}
