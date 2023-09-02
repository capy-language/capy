#[derive(Default)]
pub struct UIDGenerator {
    inner: u32,
}

impl UIDGenerator {
    pub fn generate_unique_id(&mut self) -> u32 {
        let id = self.inner;
        self.inner += 1;
        id
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let mut uid_gen = UIDGenerator::default();

        assert_eq!(uid_gen.generate_unique_id(), 0);
        assert_eq!(uid_gen.generate_unique_id(), 1);
    }
}
