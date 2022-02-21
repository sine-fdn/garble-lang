//! Simple helper for lexical scopes used by [`crate::check`] and [`crate::compile`].
use std::collections::HashMap;

pub(crate) struct Env<T: Clone>(Vec<HashMap<String, T>>);

impl<T: Clone> Env<T> {
    pub(crate) fn new() -> Self {
        Self(vec![HashMap::new()])
    }

    pub(crate) fn get(&self, identifier: &str) -> Option<T> {
        for bindings in self.0.iter().rev() {
            if let Some(v) = bindings.get(identifier) {
                return Some(v.clone());
            }
        }
        None
    }

    pub(crate) fn set(&mut self, identifier: String, binding: T) {
        self.0.last_mut().unwrap().insert(identifier, binding);
    }

    pub(crate) fn push(&mut self) {
        self.0.push(HashMap::new());
    }

    pub(crate) fn pop(&mut self) {
        self.0.pop().unwrap();
    }
}
