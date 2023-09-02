use rustc_hash::FxHashMap;

use crate::{Definition, FileName, Fqn, Index, RangeInfo};

#[derive(Default)]
pub struct WorldIndex(FxHashMap<FileName, Index>);

impl WorldIndex {
    pub fn get_definition(&self, fqn: Fqn) -> Result<&Definition, GetDefinitionError> {
        match self.0.get(&fqn.module) {
            Some(index) => match index.get_definition(fqn.name) {
                Some(def) => Ok(def),
                None => Err(GetDefinitionError::UnknownDefinition),
            },
            None => Err(GetDefinitionError::UnknownModule),
        }
    }

    pub fn range_info(&self, fqn: Fqn) -> &RangeInfo {
        &self.0[&fqn.module].range_info[&fqn.name]
    }

    pub fn get_all_modules(&self) -> Vec<(FileName, &Index)> {
        self.0
            .iter()
            .map(|(module, index)| (*module, index))
            .collect()
    }

    pub fn get_module(&self, module: FileName) -> Option<&Index> {
        self.0.get(&module)
    }

    pub fn add_module(&mut self, module: FileName, index: Index) {
        assert!(self.0.insert(module, index).is_none());
    }

    pub fn update_module(&mut self, module: FileName, index: Index) {
        *self.0.get_mut(&module).unwrap() = index;
    }

    pub fn ranges(&self) -> impl Iterator<Item = (Fqn, &RangeInfo)> {
        self.0.iter().flat_map(|(module, index)| {
            index.ranges().map(|(name, range)| {
                (
                    Fqn {
                        module: *module,
                        name,
                    },
                    range,
                )
            })
        })
    }
}

#[derive(Debug)]
pub enum GetDefinitionError {
    UnknownModule,
    UnknownDefinition,
}
