use rustc_hash::FxHashMap;

use crate::{Definition, FileName, Fqn, Index, RangeInfo};

#[derive(Default, Debug)]
pub struct WorldIndex(FxHashMap<FileName, Index>);

impl WorldIndex {
    pub fn get_definition(&self, fqn: Fqn) -> Result<Definition, GetDefinitionError> {
        match self.0.get(&fqn.file) {
            Some(index) => match index.get_definition(fqn.name) {
                Some(def) => Ok(def),
                None => Err(GetDefinitionError::UnknownDefinition),
            },
            None => Err(GetDefinitionError::UnknownFile),
        }
    }

    pub fn range_info(&self, fqn: Fqn) -> &RangeInfo {
        &self.0[&fqn.file].range_info[&fqn.name]
    }

    pub fn get_all_files(&self) -> Vec<(FileName, &Index)> {
        self.0.iter().map(|(file, index)| (*file, index)).collect()
    }

    pub fn get_file(&self, file: FileName) -> Option<&Index> {
        self.0.get(&file)
    }

    pub fn add_file(&mut self, file: FileName, index: Index) {
        assert!(self.0.insert(file, index).is_none());
    }

    pub fn update_file(&mut self, file: FileName, index: Index) {
        *self.0.get_mut(&file).unwrap() = index;
    }

    pub fn ranges(&self) -> impl Iterator<Item = (Fqn, &RangeInfo)> {
        self.0.iter().flat_map(|(file, index)| {
            index
                .ranges()
                .map(|(name, range)| (Fqn { file: *file, name }, range))
        })
    }
}

#[derive(Debug)]
pub enum GetDefinitionError {
    UnknownFile,
    UnknownDefinition,
}
