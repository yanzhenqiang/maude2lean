use super::ast::*;
use std::collections::HashMap;

/// A Maude rewriting engine.
/// Supports equational reduction and rule rewriting.
pub struct RewriteEngine {
    // Will be populated with equations, rules, and module info
}

impl RewriteEngine {
    pub fn new() -> Self {
        RewriteEngine {}
    }

    /// Reduce a term using equations (bottom-up / innermost strategy).
    /// First recursively reduces subterms, then tries top-level equations.
    pub fn reduce(&self, term: &Term, equations: &[Equation]) -> Term {
        // Reduce subterms first (bottom-up)
        let reduced = self.reduce_subterms(term, equations);

        // Try top-level equations on the fully reduced term
        for eq in equations {
            if let Some(subst) = match_term(&eq.lhs, &reduced) {
                let new_term = eq.rhs.substitute(&subst);
                return self.reduce(&new_term, equations);
            }
        }

        reduced
    }

    /// Recursively reduce the arguments of an application term.
    fn reduce_subterms(&self, term: &Term, equations: &[Equation]) -> Term {
        match term {
            Term::Application { op, args, sort } => {
                let new_args: Vec<Term> = args
                    .iter()
                    .map(|a| self.reduce(a, equations))
                    .collect();
                Term::Application {
                    op: op.clone(),
                    args: new_args,
                    sort: sort.clone(),
                }
            }
            other => other.clone(),
        }
    }

    /// Apply rewrite rules to a term (one step, top-down strategy).
    /// First tries rules at the top level, then recursively on subterms.
    pub fn rewrite(&self, term: &Term, rules: &[Rule]) -> Term {
        // Try top-level rules first
        for rule in rules {
            if let Some(subst) = match_term(&rule.lhs, term) {
                return rule.rhs.substitute(&subst);
            }
        }

        // If no top-level rule matches, try on subterms
        match term {
            Term::Application { op, args, sort } => {
                for (i, arg) in args.iter().enumerate() {
                    let rewritten = self.rewrite(arg, rules);
                    if rewritten != *arg {
                        let mut new_args = args.clone();
                        new_args[i] = rewritten;
                        return Term::Application {
                            op: op.clone(),
                            args: new_args,
                            sort: sort.clone(),
                        };
                    }
                }
                term.clone()
            }
            other => other.clone(),
        }
    }

    /// Fully reduce using equations, then apply one step of rule rewriting.
    pub fn reduce_then_rewrite(&self, term: &Term, equations: &[Equation], rules: &[Rule]) -> Term {
        let reduced = self.reduce(term, equations);
        self.rewrite(&reduced, rules)
    }
}

/// Try to match a pattern against a term.
/// Returns a substitution if successful.
pub fn match_term(pattern: &Term, term: &Term) -> Option<HashMap<String, Term>> {
    let mut subst = HashMap::new();
    if match_term_inner(pattern, term, &mut subst) {
        Some(subst)
    } else {
        None
    }
}

fn match_term_inner(pattern: &Term, term: &Term, subst: &mut HashMap<String, Term>) -> bool {
    match (pattern, term) {
        (Term::Variable(name, _), t) => {
            if let Some(existing) = subst.get(name) {
                existing == t
            } else {
                subst.insert(name.clone(), t.clone());
                true
            }
        }
        (Term::Constant(name1, _), Term::Constant(name2, _)) => name1 == name2,
        (Term::NatLiteral(n1), Term::NatLiteral(n2)) => n1 == n2,
        (Term::StringLiteral(s1), Term::StringLiteral(s2)) => s1 == s2,
        (Term::Qid(q1), Term::Qid(q2)) => q1 == q2,
        (
            Term::Application { op: op1, args: args1, .. },
            Term::Application { op: op2, args: args2, .. },
        ) => {
            if op1 != op2 || args1.len() != args2.len() {
                return false;
            }
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                if !match_term_inner(a1, a2, subst) {
                    return false;
                }
            }
            true
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_match_term_variable() {
        let pattern = Term::Variable("X".to_string(), Sort("Nat".to_string()));
        let term = Term::Constant("0".to_string(), Sort("Nat".to_string()));
        let subst = match_term(&pattern, &term).unwrap();
        assert_eq!(subst.get("X"), Some(&term));
    }

    #[test]
    fn test_match_term_constant() {
        let pattern = Term::Constant("true".to_string(), Sort("Bool".to_string()));
        let term = Term::Constant("true".to_string(), Sort("Bool".to_string()));
        let subst = match_term(&pattern, &term).unwrap();
        assert!(subst.is_empty());
    }

    #[test]
    fn test_match_term_constant_fail() {
        let pattern = Term::Constant("true".to_string(), Sort("Bool".to_string()));
        let term = Term::Constant("false".to_string(), Sort("Bool".to_string()));
        assert!(match_term(&pattern, &term).is_none());
    }

    #[test]
    fn test_match_term_application() {
        let pattern = Term::Application {
            op: "not_".to_string(),
            args: vec![Term::Variable("X".to_string(), Sort("Bool".to_string()))],
            sort: Sort("Bool".to_string()),
        };
        let term = Term::Application {
            op: "not_".to_string(),
            args: vec![Term::Constant("true".to_string(), Sort("Bool".to_string()))],
            sort: Sort("Bool".to_string()),
        };
        let subst = match_term(&pattern, &term).unwrap();
        assert_eq!(subst.get("X"), Some(&Term::Constant("true".to_string(), Sort("Bool".to_string()))));
    }

    #[test]
    fn test_reduce_not_true() {
        let eqs = vec![
            Equation {
                label: None,
                lhs: Term::Application {
                    op: "not_".to_string(),
                    args: vec![Term::Constant("true".to_string(), Sort("Bool".to_string()))],
                    sort: Sort("Bool".to_string()),
                },
                rhs: Term::Constant("false".to_string(), Sort("Bool".to_string())),
                condition: None,
            },
        ];
        let engine = RewriteEngine::new();
        let term = Term::Application {
            op: "not_".to_string(),
            args: vec![Term::Constant("true".to_string(), Sort("Bool".to_string()))],
            sort: Sort("Bool".to_string()),
        };
        let result = engine.reduce(&term, &eqs);
        assert_eq!(result, Term::Constant("false".to_string(), Sort("Bool".to_string())));
    }

    #[test]
    fn test_reduce_and_true() {
        let eqs = vec![
            Equation {
                label: None,
                lhs: Term::Application {
                    op: "_and_".to_string(),
                    args: vec![
                        Term::Constant("true".to_string(), Sort("Bool".to_string())),
                        Term::Variable("X".to_string(), Sort("Bool".to_string())),
                    ],
                    sort: Sort("Bool".to_string()),
                },
                rhs: Term::Variable("X".to_string(), Sort("Bool".to_string())),
                condition: None,
            },
        ];
        let engine = RewriteEngine::new();
        let term = Term::Application {
            op: "_and_".to_string(),
            args: vec![
                Term::Constant("true".to_string(), Sort("Bool".to_string())),
                Term::Constant("false".to_string(), Sort("Bool".to_string())),
            ],
            sort: Sort("Bool".to_string()),
        };
        let result = engine.reduce(&term, &eqs);
        assert_eq!(result, Term::Constant("false".to_string(), Sort("Bool".to_string())));
    }

    #[test]
    fn test_reduce_nested_not() {
        // not(not(true)) -> not(false) -> true
        let eqs = vec![
            Equation {
                label: None,
                lhs: Term::Application {
                    op: "not_".to_string(),
                    args: vec![Term::Constant("true".to_string(), Sort("Bool".to_string()))],
                    sort: Sort("Bool".to_string()),
                },
                rhs: Term::Constant("false".to_string(), Sort("Bool".to_string())),
                condition: None,
            },
            Equation {
                label: None,
                lhs: Term::Application {
                    op: "not_".to_string(),
                    args: vec![Term::Constant("false".to_string(), Sort("Bool".to_string()))],
                    sort: Sort("Bool".to_string()),
                },
                rhs: Term::Constant("true".to_string(), Sort("Bool".to_string())),
                condition: None,
            },
        ];
        let engine = RewriteEngine::new();
        let term = Term::Application {
            op: "not_".to_string(),
            args: vec![Term::Application {
                op: "not_".to_string(),
                args: vec![Term::Constant("true".to_string(), Sort("Bool".to_string()))],
                sort: Sort("Bool".to_string()),
            }],
            sort: Sort("Bool".to_string()),
        };
        let result = engine.reduce(&term, &eqs);
        assert_eq!(result, Term::Constant("true".to_string(), Sort("Bool".to_string())));
    }

    #[test]
    fn test_reduce_and_with_nested_not() {
        // and(true, not(true)) -> and(true, false) -> false
        let eqs = vec![
            Equation {
                label: None,
                lhs: Term::Application {
                    op: "not_".to_string(),
                    args: vec![Term::Constant("true".to_string(), Sort("Bool".to_string()))],
                    sort: Sort("Bool".to_string()),
                },
                rhs: Term::Constant("false".to_string(), Sort("Bool".to_string())),
                condition: None,
            },
            Equation {
                label: None,
                lhs: Term::Application {
                    op: "_and_".to_string(),
                    args: vec![
                        Term::Constant("true".to_string(), Sort("Bool".to_string())),
                        Term::Variable("X".to_string(), Sort("Bool".to_string())),
                    ],
                    sort: Sort("Bool".to_string()),
                },
                rhs: Term::Variable("X".to_string(), Sort("Bool".to_string())),
                condition: None,
            },
        ];
        let engine = RewriteEngine::new();
        let term = Term::Application {
            op: "_and_".to_string(),
            args: vec![
                Term::Constant("true".to_string(), Sort("Bool".to_string())),
                Term::Application {
                    op: "not_".to_string(),
                    args: vec![Term::Constant("true".to_string(), Sort("Bool".to_string()))],
                    sort: Sort("Bool".to_string()),
                },
            ],
            sort: Sort("Bool".to_string()),
        };
        let result = engine.reduce(&term, &eqs);
        assert_eq!(result, Term::Constant("false".to_string(), Sort("Bool".to_string())));
    }

    #[test]
    fn test_reduce_nat_add() {
        // NAT equations: 0 + X = X, s(X) + Y = s(X + Y)
        let eqs = vec![
            Equation {
                label: None,
                lhs: Term::Application {
                    op: "_+_".to_string(),
                    args: vec![
                        Term::Constant("z".to_string(), Sort("Nat".to_string())),
                        Term::Variable("X".to_string(), Sort("Nat".to_string())),
                    ],
                    sort: Sort("Nat".to_string()),
                },
                rhs: Term::Variable("X".to_string(), Sort("Nat".to_string())),
                condition: None,
            },
            Equation {
                label: None,
                lhs: Term::Application {
                    op: "_+_".to_string(),
                    args: vec![
                        Term::Application {
                            op: "s".to_string(),
                            args: vec![Term::Variable("X".to_string(), Sort("Nat".to_string()))],
                            sort: Sort("Nat".to_string()),
                        },
                        Term::Variable("Y".to_string(), Sort("Nat".to_string())),
                    ],
                    sort: Sort("Nat".to_string()),
                },
                rhs: Term::Application {
                    op: "s".to_string(),
                    args: vec![Term::Application {
                        op: "_+_".to_string(),
                        args: vec![
                            Term::Variable("X".to_string(), Sort("Nat".to_string())),
                            Term::Variable("Y".to_string(), Sort("Nat".to_string())),
                        ],
                        sort: Sort("Nat".to_string()),
                    }],
                    sort: Sort("Nat".to_string()),
                },
                condition: None,
            },
        ];
        let engine = RewriteEngine::new();
        // s(z) + s(z) -> s(z + s(z)) -> s(s(z))
        let term = Term::Application {
            op: "_+_".to_string(),
            args: vec![
                Term::Application {
                    op: "s".to_string(),
                    args: vec![Term::Constant("z".to_string(), Sort("Nat".to_string()))],
                    sort: Sort("Nat".to_string()),
                },
                Term::Application {
                    op: "s".to_string(),
                    args: vec![Term::Constant("z".to_string(), Sort("Nat".to_string()))],
                    sort: Sort("Nat".to_string()),
                },
            ],
            sort: Sort("Nat".to_string()),
        };
        let result = engine.reduce(&term, &eqs);
        let expected = Term::Application {
            op: "s".to_string(),
            args: vec![Term::Application {
                op: "s".to_string(),
                args: vec![Term::Constant("z".to_string(), Sort("Nat".to_string()))],
                sort: Sort("Nat".to_string()),
            }],
            sort: Sort("Nat".to_string()),
        };
        assert_eq!(result, expected);
    }
}
