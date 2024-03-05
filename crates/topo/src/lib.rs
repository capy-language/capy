// I was using `topological_sort::TopilogicalSort` but it didn't have all the features I needed so
// I implemented it myself

use std::{collections::hash_map::Entry, hash::Hash};

use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Debug)]
pub struct CycleErr;

#[derive(Debug, Clone)]
struct Dependencies<T> {
    num_children: usize,
    parents: FxHashSet<T>,
}

impl<T: Hash + Eq> Dependencies<T> {
    fn new() -> Dependencies<T> {
        Dependencies {
            num_children: 0,
            parents: Default::default(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TopoSort<T> {
    top: FxHashMap<T, Dependencies<T>>,
}

impl<T> Default for TopoSort<T> {
    fn default() -> Self {
        TopoSort {
            top: FxHashMap::default(),
        }
    }
}

impl<T: Hash + Eq + Clone> TopoSort<T> {
    /// Creates new empty TopoSort
    #[inline]
    pub fn new() -> Self {
        Default::default()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.top.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.top.is_empty()
    }

    /// Registers a dependency
    ///
    /// `parent` depends upon `child`.
    ///
    /// e.g.
    ///
    /// * "capy" (parent) depends upon "cranelift" (child)
    /// * "main" (parent) depends upon "foo" (child)
    pub fn insert_dep<P, Q>(&mut self, parent: P, child: Q)
    where
        P: Into<T>,
        Q: Into<T>,
    {
        let parent = parent.into();
        let child = child.into();

        match self.top.entry(child) {
            Entry::Vacant(e) => {
                let mut dep = Dependencies::<T>::new();
                dep.parents.insert(parent.clone());
                e.insert(dep);
            }
            Entry::Occupied(e) => {
                if !e.into_mut().parents.insert(parent.clone()) {
                    // Already registered
                    return;
                }
            }
        }

        self.top
            .entry(parent)
            .or_insert_with(Dependencies::<T>::new)
            .num_children += 1;
    }

    #[inline]
    pub fn insert_deps<P, I, Q>(&mut self, parent: P, children: I)
    where
        P: Into<T> + Clone,
        I: IntoIterator<Item = Q>,
        Q: Into<T>,
    {
        for child in children {
            self.insert_dep(parent.clone(), child);
        }
    }

    /// Inserts a lone element without adding any dependencies from or to it.
    ///
    /// Returns true if the item already existed in the `TopoSort`
    pub fn insert<U>(&mut self, item: U) -> bool
    where
        U: Into<T>,
    {
        match self.top.entry(item.into()) {
            Entry::Vacant(e) => {
                let dep = Dependencies::<T>::new();
                e.insert(dep);
                true
            }
            Entry::Occupied(_) => false,
        }
    }

    pub fn extend<I, U>(&mut self, items: I)
    where
        I: IntoIterator<Item = U>,
        U: Into<T>,
    {
        self.top.extend(
            items
                .into_iter()
                .map(Into::into)
                .map(|item| (item, Dependencies::<T>::new())),
        );
    }

    /// Removes the first item with no open dependencies.
    pub fn pop(&mut self) -> Option<Result<T, CycleErr>> {
        self.peek().map(|key| key.cloned()).map(|key| {
            if let Ok(key) = &key {
                self.remove(key);
            }

            key
        })
    }

    /// Removes all items that have no open dependencies.
    pub fn pop_all(&mut self) -> Result<Vec<T>, CycleErr> {
        self.peek_all()
            .map(|keys| keys.into_iter().cloned().collect())
            .map(|keys| {
                for key in &keys {
                    self.remove(key);
                }

                keys
            })
    }

    /// Returns a reference to the first item with no dependencies.
    pub fn peek(&self) -> Option<Result<&T, CycleErr>> {
        let result = self
            .top
            .iter()
            .filter(|&(_, v)| v.num_children == 0)
            .map(|(k, _)| k)
            .next();

        if let Some(result) = result {
            Some(Ok(result))
        } else if self.is_empty() {
            None
        } else {
            Some(Err(CycleErr))
        }
    }

    /// Returns a reference to all the items with no open dependencies.
    pub fn peek_all(&self) -> Result<Vec<&T>, CycleErr> {
        let result: Vec<_> = self
            .top
            .iter()
            .filter(|&(_, v)| v.num_children == 0)
            .map(|(k, _)| k)
            .collect();

        if !self.is_empty() && result.is_empty() {
            Err(CycleErr)
        } else {
            Ok(result)
        }
    }

    /// Returns true if the only items left are all cyclic.
    #[inline]
    pub fn in_cycle(&self) -> bool {
        !self.is_empty() && self.top.values().all(|v| v.num_children != 0)
    }

    /// Removes the first item with a cyclic dependency.
    ///
    /// If there are no cyclic dependencies, or there are still some non-cyclic
    /// dependencies, returns None.
    pub fn pop_cyclic(&mut self) -> Option<T> {
        if self.in_cycle() {
            let result = self.top.keys().next().unwrap().clone();

            self.remove(&result);

            Some(result)
        } else {
            None
        }
    }

    /// Removes all items with a cyclic dependency.
    ///
    /// If there are no cyclic dependencies, or there are still some non-cyclic
    /// dependencies, returns None.
    pub fn pop_all_cyclic(&mut self) -> Option<Vec<T>> {
        if self.in_cycle() {
            let result = self.top.keys().cloned().collect();

            self.top.clear();

            Some(result)
        } else {
            None
        }
    }

    /// Returns a reference to the first item with a cyclic dependency.
    ///
    /// If there are no cyclic dependencies, or there are still some non-cyclic
    /// dependencies, returns None.
    pub fn peek_cyclic(&self) -> Option<&T> {
        if self.in_cycle() {
            self.top.keys().next()
        } else {
            None
        }
    }

    /// Returns a reference to all the items with cyclic dependency.
    ///
    /// If there are no cyclic dependencies, or there are still some non-cyclic
    /// dependencies, returns None.
    pub fn peek_all_cyclic(&self) -> Option<Vec<&T>> {
        if self.in_cycle() {
            Some(self.top.keys().collect())
        } else {
            None
        }
    }

    /// Removes a dependency from the list, returns true if the dependency existed
    pub fn remove(&mut self, child: &T) -> bool {
        let result = self.top.remove(child);

        if let Some(ref p) = result {
            for s in &p.parents {
                if let Some(y) = self.top.get_mut(s) {
                    y.num_children -= 1;
                }
            }

            true
        } else {
            false
        }
    }

    #[inline]
    pub fn clear(&mut self) {
        self.top.clear();
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use crate::TopoSort;

    #[test]
    fn it_works() {
        let mut topo = TopoSort::<&str>::default();

        topo.insert_dep("burger", "patty");

        topo.insert_dep("steak", "flank");
        topo.insert_dep("patty", "beef");
        topo.insert_dep("meatballs", "beef");

        topo.insert_dep("flank", "cow");
        topo.insert_dep("beef", "cow");

        assert_eq!(
            vec!["cow"],
            topo.pop_all().unwrap().into_iter().sorted().collect_vec()
        );

        assert_eq!(
            vec!["beef", "flank"],
            topo.pop_all().unwrap().into_iter().sorted().collect_vec()
        );

        assert_eq!(
            vec!["meatballs", "patty", "steak"],
            topo.pop_all().unwrap().into_iter().sorted().collect_vec()
        );

        assert_eq!(
            vec!["burger"],
            topo.pop_all().unwrap().into_iter().sorted().collect_vec()
        );

        assert!(topo.pop_all().unwrap().is_empty());
    }
}
