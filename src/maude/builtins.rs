use super::ast::*;

/// Built-in module definitions for Maude.
/// These are modules that are natively implemented rather than defined in Maude syntax.

/// Create the BOOL module
pub fn bool_module() -> Module {
    Module::Functional {
        name: "BOOL".to_string(),
        imports: vec![],
        sorts: vec![Sort("Bool".to_string())],
        subsorts: vec![],
        ops: vec![
            OpDecl { name: "true".to_string(), arity: vec![], coarity: Sort("Bool".to_string()), attrs: vec![] },
            OpDecl { name: "false".to_string(), arity: vec![], coarity: Sort("Bool".to_string()), attrs: vec![] },
            OpDecl { name: "_and_".to_string(), arity: vec![Sort("Bool".to_string()), Sort("Bool".to_string())], coarity: Sort("Bool".to_string()), attrs: vec![OpAttr::Assoc, OpAttr::Comm, OpAttr::Id(Term::Constant("true".to_string(), Sort("Bool".to_string())))] },
            OpDecl { name: "_or_".to_string(), arity: vec![Sort("Bool".to_string()), Sort("Bool".to_string())], coarity: Sort("Bool".to_string()), attrs: vec![OpAttr::Assoc, OpAttr::Comm, OpAttr::Id(Term::Constant("false".to_string(), Sort("Bool".to_string())))] },
            OpDecl { name: "not_".to_string(), arity: vec![Sort("Bool".to_string())], coarity: Sort("Bool".to_string()), attrs: vec![] },
            OpDecl { name: "_xor_".to_string(), arity: vec![Sort("Bool".to_string()), Sort("Bool".to_string())], coarity: Sort("Bool".to_string()), attrs: vec![OpAttr::Assoc, OpAttr::Comm] },
            OpDecl { name: "_implies_".to_string(), arity: vec![Sort("Bool".to_string()), Sort("Bool".to_string())], coarity: Sort("Bool".to_string()), attrs: vec![] },
        ],
        equations: vec![
            // not true = false
            Equation { label: None, lhs: Term::Application { op: "not_".to_string(), args: vec![Term::Constant("true".to_string(), Sort("Bool".to_string()))], sort: Sort("Bool".to_string()) }, rhs: Term::Constant("false".to_string(), Sort("Bool".to_string())), condition: None },
            // not false = true
            Equation { label: None, lhs: Term::Application { op: "not_".to_string(), args: vec![Term::Constant("false".to_string(), Sort("Bool".to_string()))], sort: Sort("Bool".to_string()) }, rhs: Term::Constant("true".to_string(), Sort("Bool".to_string())), condition: None },
            // true and X = X
            Equation { label: None, lhs: Term::Application { op: "_and_".to_string(), args: vec![Term::Constant("true".to_string(), Sort("Bool".to_string())), Term::Variable("X".to_string(), Sort("Bool".to_string()))], sort: Sort("Bool".to_string()) }, rhs: Term::Variable("X".to_string(), Sort("Bool".to_string())), condition: None },
            // false and X = false
            Equation { label: None, lhs: Term::Application { op: "_and_".to_string(), args: vec![Term::Constant("false".to_string(), Sort("Bool".to_string())), Term::Variable("X".to_string(), Sort("Bool".to_string()))], sort: Sort("Bool".to_string()) }, rhs: Term::Constant("false".to_string(), Sort("Bool".to_string())), condition: None },
            // true or X = true
            Equation { label: None, lhs: Term::Application { op: "_or_".to_string(), args: vec![Term::Constant("true".to_string(), Sort("Bool".to_string())), Term::Variable("X".to_string(), Sort("Bool".to_string()))], sort: Sort("Bool".to_string()) }, rhs: Term::Constant("true".to_string(), Sort("Bool".to_string())), condition: None },
            // false or X = X
            Equation { label: None, lhs: Term::Application { op: "_or_".to_string(), args: vec![Term::Constant("false".to_string(), Sort("Bool".to_string())), Term::Variable("X".to_string(), Sort("Bool".to_string()))], sort: Sort("Bool".to_string()) }, rhs: Term::Variable("X".to_string(), Sort("Bool".to_string())), condition: None },
            // true xor true = false
            Equation { label: None, lhs: Term::Application { op: "_xor_".to_string(), args: vec![Term::Constant("true".to_string(), Sort("Bool".to_string())), Term::Constant("true".to_string(), Sort("Bool".to_string()))], sort: Sort("Bool".to_string()) }, rhs: Term::Constant("false".to_string(), Sort("Bool".to_string())), condition: None },
            // false xor X = X
            Equation { label: None, lhs: Term::Application { op: "_xor_".to_string(), args: vec![Term::Constant("false".to_string(), Sort("Bool".to_string())), Term::Variable("X".to_string(), Sort("Bool".to_string()))], sort: Sort("Bool".to_string()) }, rhs: Term::Variable("X".to_string(), Sort("Bool".to_string())), condition: None },
        ],
        memberships: vec![],
    }
}

/// Create the NAT module (simplified)
pub fn nat_module() -> Module {
    Module::Functional {
        name: "NAT".to_string(),
        imports: vec![Import { mode: ImportMode::Protecting, module: "BOOL".to_string() }],
        sorts: vec![Sort("Zero".to_string()), Sort("NzNat".to_string()), Sort("Nat".to_string())],
        subsorts: vec![
            (Sort("Zero".to_string()), Sort("Nat".to_string())),
            (Sort("NzNat".to_string()), Sort("Nat".to_string())),
        ],
        ops: vec![
            OpDecl { name: "0".to_string(), arity: vec![], coarity: Sort("Zero".to_string()), attrs: vec![] },
            OpDecl { name: "s_".to_string(), arity: vec![Sort("Nat".to_string())], coarity: Sort("NzNat".to_string()), attrs: vec![] },
            OpDecl { name: "_+_".to_string(), arity: vec![Sort("Nat".to_string()), Sort("Nat".to_string())], coarity: Sort("Nat".to_string()), attrs: vec![OpAttr::Assoc, OpAttr::Comm, OpAttr::Id(Term::Constant("0".to_string(), Sort("Zero".to_string())))] },
            OpDecl { name: "_*_".to_string(), arity: vec![Sort("Nat".to_string()), Sort("Nat".to_string())], coarity: Sort("Nat".to_string()), attrs: vec![OpAttr::Assoc, OpAttr::Comm, OpAttr::Id(Term::Constant("s_".to_string(), Sort("Zero".to_string())))] },
        ],
        equations: vec![
            // 0 + X = X
            Equation { label: None, lhs: Term::Application { op: "_+_".to_string(), args: vec![Term::Constant("0".to_string(), Sort("Zero".to_string())), Term::Variable("X".to_string(), Sort("Nat".to_string()))], sort: Sort("Nat".to_string()) }, rhs: Term::Variable("X".to_string(), Sort("Nat".to_string())), condition: None },
            // s X + Y = s (X + Y)
            Equation { label: None, lhs: Term::Application { op: "_+_".to_string(), args: vec![Term::Application { op: "s_".to_string(), args: vec![Term::Variable("X".to_string(), Sort("Nat".to_string()))], sort: Sort("NzNat".to_string()) }, Term::Variable("Y".to_string(), Sort("Nat".to_string()))], sort: Sort("Nat".to_string()) }, rhs: Term::Application { op: "s_".to_string(), args: vec![Term::Application { op: "_+_".to_string(), args: vec![Term::Variable("X".to_string(), Sort("Nat".to_string())), Term::Variable("Y".to_string(), Sort("Nat".to_string()))], sort: Sort("Nat".to_string()) }], sort: Sort("NzNat".to_string()) }, condition: None },
            // 0 * X = 0
            Equation { label: None, lhs: Term::Application { op: "_*_".to_string(), args: vec![Term::Constant("0".to_string(), Sort("Zero".to_string())), Term::Variable("X".to_string(), Sort("Nat".to_string()))], sort: Sort("Nat".to_string()) }, rhs: Term::Constant("0".to_string(), Sort("Zero".to_string())), condition: None },
            // s X * Y = Y + (X * Y)
            Equation { label: None, lhs: Term::Application { op: "_*_".to_string(), args: vec![Term::Application { op: "s_".to_string(), args: vec![Term::Variable("X".to_string(), Sort("Nat".to_string()))], sort: Sort("NzNat".to_string()) }, Term::Variable("Y".to_string(), Sort("Nat".to_string()))], sort: Sort("Nat".to_string()) }, rhs: Term::Application { op: "_+_".to_string(), args: vec![Term::Variable("Y".to_string(), Sort("Nat".to_string())), Term::Application { op: "_*_".to_string(), args: vec![Term::Variable("X".to_string(), Sort("Nat".to_string())), Term::Variable("Y".to_string(), Sort("Nat".to_string()))], sort: Sort("Nat".to_string()) }], sort: Sort("Nat".to_string()) }, condition: None },
        ],
        memberships: vec![],
    }
}

/// Create the QID module
pub fn qid_module() -> Module {
    Module::Functional {
        name: "QID".to_string(),
        imports: vec![],
        sorts: vec![Sort("Qid".to_string())],
        subsorts: vec![],
        ops: vec![],
        equations: vec![],
        memberships: vec![],
    }
}

/// Create the STRING module
pub fn string_module() -> Module {
    Module::Functional {
        name: "STRING".to_string(),
        imports: vec![Import { mode: ImportMode::Protecting, module: "BOOL".to_string() }],
        sorts: vec![Sort("String".to_string())],
        subsorts: vec![],
        ops: vec![
            OpDecl { name: "_+_".to_string(), arity: vec![Sort("String".to_string()), Sort("String".to_string())], coarity: Sort("String".to_string()), attrs: vec![OpAttr::Assoc, OpAttr::Id(Term::StringLiteral("".to_string()))] },
        ],
        equations: vec![],
        memberships: vec![],
    }
}

/// Create the CONFIGURATION module (used by K Framework)
pub fn configuration_module() -> Module {
    Module::System {
        name: "CONFIGURATION".to_string(),
        imports: vec![],
        sorts: vec![Sort("Configuration".to_string()), Sort("State".to_string())],
        subsorts: vec![],
        ops: vec![
            OpDecl { name: "<_>_".to_string(), arity: vec![Sort("State".to_string()), Sort("State".to_string())], coarity: Sort("Configuration".to_string()), attrs: vec![] },
        ],
        equations: vec![],
        memberships: vec![],
        rules: vec![],
    }
}
