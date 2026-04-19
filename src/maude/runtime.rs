use super::ast::*;
use std::collections::{HashMap, HashSet};

/// A Maude runtime environment that manages loaded modules,
/// sort hierarchies, and operator tables.
pub struct Runtime {
    pub modules: HashMap<String, Module>,
    /// Sort graph: sort -> set of supersorts
    pub sort_graph: HashMap<Sort, HashSet<Sort>>,
    /// Combined operators from all loaded modules
    pub operators: HashMap<String, Vec<OpDecl>>,
}

impl Runtime {
    pub fn new() -> Self {
        let mut rt = Runtime {
            modules: HashMap::new(),
            sort_graph: HashMap::new(),
            operators: HashMap::new(),
        };
        // Load built-in modules
        rt.load_module(super::builtins::bool_module());
        rt.load_module(super::builtins::nat_module());
        rt.load_module(super::builtins::qid_module());
        rt.load_module(super::builtins::string_module());
        rt
    }

    pub fn load_module(&mut self, module: Module) {
        let name = module.name().to_string();
        // Build sort graph
        for sort in module.sorts() {
            self.sort_graph.entry(sort.clone()).or_default();
        }
        for (s1, s2) in module.subsorts() {
            self.sort_graph.entry(s1.clone()).or_default().insert(s2.clone());
        }
        // Compute transitive closure
        let sorts: Vec<Sort> = self.sort_graph.keys().cloned().collect();
        for k in 0..sorts.len() {
            for i in 0..sorts.len() {
                for j in 0..sorts.len() {
                    let si = sorts[i].clone();
                    let sj = sorts[j].clone();
                    let sk = sorts[k].clone();
                    if self.sort_graph.get(&si).map_or(false, |s| s.contains(&sk))
                        && self.sort_graph.get(&sk).map_or(false, |s| s.contains(&sj))
                    {
                        self.sort_graph.entry(si).or_default().insert(sj);
                    }
                }
            }
        }
        // Register operators
        for op in module.ops() {
            self.operators.entry(op.name.clone()).or_default().push(op.clone());
        }
        self.modules.insert(name, module);
    }

    /// Check if sort1 is a subsort of sort2
    pub fn is_subsort(&self, sort1: &Sort, sort2: &Sort) -> bool {
        if sort1 == sort2 { return true; }
        self.sort_graph.get(sort1).map_or(false, |s| s.contains(sort2))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_runtime_loads_builtins() {
        let rt = Runtime::new();
        assert!(rt.modules.contains_key("BOOL"));
        assert!(rt.modules.contains_key("NAT"));
        assert!(rt.modules.contains_key("QID"));
        assert!(rt.modules.contains_key("STRING"));
    }

    #[test]
    fn test_is_subsort_reflexive() {
        let rt = Runtime::new();
        assert!(rt.is_subsort(&Sort("Nat".to_string()), &Sort("Nat".to_string())));
    }

    #[test]
    fn test_is_subsort_direct() {
        let rt = Runtime::new();
        // Zero is a subsort of Nat
        assert!(rt.is_subsort(&Sort("Zero".to_string()), &Sort("Nat".to_string())));
    }

    #[test]
    fn test_is_subsort_not_supersort() {
        let rt = Runtime::new();
        // Nat is NOT a subsort of Zero
        assert!(!rt.is_subsort(&Sort("Nat".to_string()), &Sort("Zero".to_string())));
    }

    #[test]
    fn test_is_subsort_transitive() {
        let rt = Runtime::new();
        // Zero -> Nat, so Zero is a subsort of Nat
        assert!(rt.is_subsort(&Sort("Zero".to_string()), &Sort("Nat".to_string())));
    }

    #[test]
    fn test_operators_registered() {
        let rt = Runtime::new();
        assert!(rt.operators.contains_key("true"));
        assert!(rt.operators.contains_key("false"));
        assert!(rt.operators.contains_key("_and_"));
        assert!(rt.operators.contains_key("0"));
        assert!(rt.operators.contains_key("s_"));
        assert!(rt.operators.contains_key("_+_"));
    }
}
