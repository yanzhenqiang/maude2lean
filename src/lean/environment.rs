use super::declaration::*;
use super::expr::*;
use std::collections::HashMap;

/// Lean environment stores all constant declarations
#[derive(Debug, Clone)]
pub struct Environment {
    constants: HashMap<Name, ConstantInfo>,
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            constants: HashMap::new(),
        }
    }

    /// Find a constant by name
    pub fn find(&self, name: &Name) -> Option<&ConstantInfo> {
        self.constants.get(name)
    }

    /// Get a constant by name (panics if not found)
    pub fn get(&self, name: &Name) -> &ConstantInfo {
        self.constants.get(name).expect("Constant not found")
    }

    /// Check if a constant exists
    pub fn contains(&self, name: &Name) -> bool {
        self.constants.contains_key(name)
    }

    /// Insert a constant info directly
    pub fn insert_constant(&mut self, name: Name, info: ConstantInfo) {
        self.constants.insert(name, info);
    }

    /// Add a declaration to the environment
    pub fn add(&mut self, decl: Declaration) -> Result<(), String> {
        match decl {
            Declaration::Axiom(val) => {
                let info = ConstantInfo::AxiomInfo(val.clone());
                self.check_name(&val.constant_val.name)?;
                self.constants.insert(val.constant_val.name, info);
                Ok(())
            }
            Declaration::Definition(val) => {
                let info = ConstantInfo::DefinitionInfo(val.clone());
                self.check_name(&val.constant_val.name)?;
                self.check_duplicated_univ_params(&val.constant_val.level_params)?;
                self.constants.insert(val.constant_val.name, info);
                Ok(())
            }
            Declaration::MutualDefinition(defs) => {
                for val in defs {
                    let info = ConstantInfo::DefinitionInfo(val.clone());
                    self.check_name(&val.constant_val.name)?;
                    self.check_duplicated_univ_params(&val.constant_val.level_params)?;
                    self.constants.insert(val.constant_val.name, info);
                }
                Ok(())
            }
        }
    }

    fn check_name(&self, name: &Name) -> Result<(), String> {
        if self.constants.contains_key(name) {
            Err(format!("Constant '{}' already declared", name.to_string()))
        } else {
            Ok(())
        }
    }

    fn check_duplicated_univ_params(&self, params: &Vec<Name>) -> Result<(), String> {
        let mut seen = HashMap::new();
        for p in params {
            if seen.contains_key(p) {
                return Err(format!("Duplicate universe parameter '{}'", p.to_string()));
            }
            seen.insert(p.clone(), true);
        }
        Ok(())
    }

    /// Iterate over all constants
    pub fn for_each_constant<F>(&self, mut f: F)
    where
        F: FnMut(&ConstantInfo),
    {
        for (_, info) in &self.constants {
            f(info);
        }
    }

    pub fn num_constants(&self) -> usize {
        self.constants.len()
    }
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_axiom() {
        let mut env = Environment::new();
        let decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("Nat"),
                level_params: vec![],
                ty: Expr::U(Level::Zero),
            },
            is_unsafe: false,
        });
        env.add(decl).unwrap();
        assert!(env.contains(&Name::new("Nat")));
    }

    #[test]
    fn test_add_definition() {
        let mut env = Environment::new();
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);

        // Add Nat : U_0
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("Nat"),
                level_params: vec![],
                ty: Expr::U(Level::Zero),
            },
            is_unsafe: false,
        })).unwrap();

        // Add zero : Nat
        env.add(Declaration::Definition(DefinitionVal {
            constant_val: ConstantVal {
                name: Name::new("zero"),
                level_params: vec![],
                ty: nat.clone(),
            },
            value: zero.clone(),
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
        })).unwrap();

        assert!(env.contains(&Name::new("Nat")));
        assert!(env.contains(&Name::new("zero")));
    }

    #[test]
    fn test_duplicate_name() {
        let mut env = Environment::new();
        let decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("Nat"),
                level_params: vec![],
                ty: Expr::U(Level::Zero),
            },
            is_unsafe: false,
        });
        env.add(decl.clone()).unwrap();
        assert!(env.add(decl).is_err());
    }
}
