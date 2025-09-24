//! Simple helper for lexical scopes used by [`crate::check()`] and [`crate::compile()`].
use std::collections::{BTreeMap, btree_map::Entry};

#[derive(Debug, Clone)]
pub(crate) struct Env<T: Clone>(pub(crate) Vec<BTreeMap<String, T>>);

impl<T: Clone + std::fmt::Debug> Env<T> {
    pub(crate) fn new() -> Self {
        Self(vec![BTreeMap::new()])
    }

    pub(crate) fn get(&self, identifier: &str) -> Option<T> {
        for bindings in self.0.iter().rev() {
            if let Some(v) = bindings.get(identifier) {
                return Some(v.clone());
            }
        }
        None
    }

    pub(crate) fn let_in_current_scope(&mut self, identifier: String, binding: T) {
        self.0.last_mut().unwrap().insert(identifier, binding);
    }

    pub(crate) fn assign_mut(&mut self, identifier: String, binding: T) {
        for scope in self.0.iter_mut().rev() {
            if let Entry::Occupied(mut e) = scope.entry(identifier.clone()) {
                e.insert(binding);
                return;
            }
        }
        panic!("Could not find existing binding for '{identifier}'");
    }

    pub(crate) fn push(&mut self) {
        self.0.push(BTreeMap::new());
    }

    pub(crate) fn pop(&mut self) {
        self.0.pop().unwrap();
    }
}
