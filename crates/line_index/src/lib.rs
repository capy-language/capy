use std::iter;
use std::ops::{Index, Sub};
use text_size::TextSize;

#[derive(Debug, Clone, PartialEq, Default)]
pub struct LineIndex {
    line_starts: Vec<TextSize>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LineNr(pub u32);

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ColNr(pub u32);

impl LineIndex {
    pub fn new(text: &str) -> Self {
        Self {
            line_starts: iter::once(TextSize::from(0))
                .chain(text.match_indices('\n').map(|(idx, _)| TextSize::from(idx as u32 + 1)))
                .collect(),
        }
    }

    pub fn line_col(&self, offset: TextSize) -> (LineNr, ColNr) {
        let line = self.line_starts.partition_point(|&it| it <= offset) - 1;
        let line = LineNr(line as u32);

        let line_start_offset = self[line];
        let col = ColNr(u32::from(offset - line_start_offset));

        (line, col)
    }
}

impl Index<LineNr> for LineIndex {
    type Output = TextSize;

    fn index(&self, index: LineNr) -> &Self::Output {
        &self.line_starts[index.0 as usize]
    }
}

impl Sub for LineNr {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self(self.0 - rhs.0)
    }
}

impl Sub for ColNr {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self(self.0 - rhs.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check<const LEN: usize>(text: &str, line_starts: [u32; LEN]) {
        assert_eq!(
            LineIndex::new(text),
            LineIndex { line_starts: line_starts.into_iter().map(TextSize::from).collect() }
        );
    }

    #[test]
    fn empty() {
        check("", [0]);
    }

    #[test]
    fn one() {
        check("\n", [0, 1]);
    }

    #[test]
    fn trailing() {
        check("foo\n", [0, 4]);
    }

    #[test]
    fn two() {
        check("foo\nbar", [0, 4]);
    }
}