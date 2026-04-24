use super::expr::*;
use std::collections::{HashMap, HashSet};

/// Information about a constructor for iota reduction.
/// This is an outer-layer extension: the kernel core does not know about
/// inductive types, but the frontend can register recursor metadata so that
/// the type checker can perform iota reduction.
#[derive(Debug, Clone)]
pub struct ConstructorInfo {
    pub name: Name,
    pub num_args: usize,
    /// Indices of arguments whose type references the inductive type.
    pub recursive_args: Vec<usize>,
}

/// Information about a recursor for iota reduction.
#[derive(Debug, Clone)]
pub struct RecursorInfo {
    pub inductive_name: Name,
    pub constructors: Vec<ConstructorInfo>,
}

/// Kernel extension state holds metadata for outer-layer features that the
/// type checker needs to know about (e.g. quotient primitives, inductive
/// recursors).  These are not part of the TTobs core; they are registered
/// by the frontend (REPL) after constructing the corresponding axioms.
#[derive(Debug, Clone)]
pub struct KernelExt {
    /// Recursor metadata for iota reduction.
    recursors: HashMap<Name, RecursorInfo>,
    /// Quotient primitive constant names.
    quot_primitives: HashSet<Name>,
}

impl KernelExt {
    pub fn new() -> Self {
        KernelExt {
            recursors: HashMap::new(),
            quot_primitives: HashSet::new(),
        }
    }

    pub fn register_recursor(&mut self, rec_name: Name, info: RecursorInfo) {
        self.recursors.insert(rec_name, info);
    }

    pub fn register_quot(&mut self, name: Name) {
        self.quot_primitives.insert(name);
    }

    pub fn is_quot(&self, name: &Name) -> bool {
        self.quot_primitives.contains(name)
    }

    pub fn get_recursor_info(&self, name: &Name) -> Option<&RecursorInfo> {
        self.recursors.get(name)
    }
}
