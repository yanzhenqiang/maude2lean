use super::expr::*;
use super::environment::Environment;
use crate::maude::ast::*;
use crate::maude::parser::Parser;
use crate::maude::rewrite::RewriteEngine;
use std::rc::Rc;

/// Convert a Lean `Expr` to a Maude `Term`.
/// Uses the operator signatures from `lean_kernel.maude`.
pub fn expr_to_term(e: &Expr) -> Term {
    match e {
        Expr::BVar(n) => Term::Application {
            op: "bvar".to_string(),
            args: vec![Term::NatLiteral(*n)],
            sort: Sort("Expr".to_string()),
        },
        Expr::Const(name, _levels) => {
            // For constructors, use the kernel.maude encoding
            if name.0 == vec!["zero".to_string()] {
                Term::Constant("zeroE".to_string(), Sort("Expr".to_string()))
            } else if name.0 == vec!["succ".to_string()] {
                // succ is usually applied to an argument in the Rust kernel,
                // but if it appears bare, encode as const(succ)
                Term::Application {
                    op: "const".to_string(),
                    args: vec![name_to_term(name)],
                    sort: Sort("Expr".to_string()),
                }
            } else if name.0 == vec!["nil".to_string()] {
                Term::Constant("nilE".to_string(), Sort("Expr".to_string()))
            } else if name.0 == vec!["cons".to_string()] {
                Term::Application {
                    op: "const".to_string(),
                    args: vec![name_to_term(name)],
                    sort: Sort("Expr".to_string()),
                }
            } else {
                Term::Application {
                    op: "const".to_string(),
                    args: vec![name_to_term(name)],
                    sort: Sort("Expr".to_string()),
                }
            }
        }
        Expr::App(f, a) => {
            // Flatten succ and cons applications into kernel.maude operators
            if let Expr::Const(name, _) = f.as_ref() {
                if name.0 == vec!["succ".to_string()] {
                    return Term::Application {
                        op: "succE".to_string(),
                        args: vec![expr_to_term(a)],
                        sort: Sort("Expr".to_string()),
                    };
                }
            }
            if let Expr::App(f2, a2) = f.as_ref() {
                if let Expr::Const(name, _) = f2.as_ref() {
                    if name.0 == vec!["cons".to_string()] {
                        return Term::Application {
                            op: "consE".to_string(),
                            args: vec![expr_to_term(a2), expr_to_term(a)],
                            sort: Sort("Expr".to_string()),
                        };
                    }
                }
            }
            Term::Application {
                op: "app".to_string(),
                args: vec![expr_to_term(f), expr_to_term(a)],
                sort: Sort("Expr".to_string()),
            }
        }
        Expr::Lambda(_name, _bi, ty, body) => Term::Application {
            op: "lam".to_string(),
            args: vec![expr_to_term(ty), expr_to_term(body)],
            sort: Sort("Expr".to_string()),
        },
        Expr::Pi(_name, _bi, ty, body) => {
            // Pi is not in lean_kernel.maude yet; encode as app(app(pi, ty), body)
            Term::Application {
                op: "app".to_string(),
                args: vec![
                    Term::Application {
                        op: "app".to_string(),
                        args: vec![
                            Term::Application {
                                op: "const".to_string(),
                                args: vec![Term::Constant("Pi".to_string(), Sort("Name".to_string()))],
                                sort: Sort("Expr".to_string()),
                            },
                            expr_to_term(ty),
                        ],
                        sort: Sort("Expr".to_string()),
                    },
                    expr_to_term(body),
                ],
                sort: Sort("Expr".to_string()),
            }
        }
        Expr::Let(_name, ty, value, body, _) => Term::Application {
            op: "letE".to_string(),
            args: vec![expr_to_term(ty), expr_to_term(value), expr_to_term(body)],
            sort: Sort("Expr".to_string()),
        },
        Expr::Sort(_level) => {
            // Encode as const(Sort) for now
            Term::Application {
                op: "const".to_string(),
                args: vec![Term::Constant("Sort".to_string(), Sort("Name".to_string()))],
                sort: Sort("Expr".to_string()),
            }
        }
        Expr::Lit(lit) => match lit {
            Literal::Nat(n) => Term::NatLiteral(*n),
            Literal::String(s) => Term::StringLiteral(s.clone()),
        },
        _ => {
            // Fallback: encode as a constant with the debug representation
            Term::Constant(
                format!("{:?}", e),
                Sort("Expr".to_string()),
            )
        }
    }
}

fn name_to_term(name: &Name) -> Term {
    Term::Constant(name.to_string(), Sort("Name".to_string()))
}

/// Convert a Maude `Term` back to a Lean `Expr`.
/// This is the inverse of `expr_to_term` for the supported subset.
pub fn term_to_expr(t: &Term) -> Expr {
    match t {
        Term::Application { op, args, .. } if op == "bvar" => {
            if let Some(Term::NatLiteral(n)) = args.get(0) {
                Expr::BVar(*n)
            } else {
                Expr::Const(Name::new("invalid_bvar"), vec![])
            }
        }
        Term::Application { op, args, .. } if op == "const" => {
            if let Some(name_term) = args.get(0) {
                let name = term_to_name(name_term);
                Expr::mk_const(name, vec![])
            } else {
                Expr::Const(Name::new("invalid_const"), vec![])
            }
        }
        Term::Application { op, args, .. } if op == "app" && args.len() == 2 => {
            let f = term_to_expr(&args[0]);
            let a = term_to_expr(&args[1]);
            Expr::mk_app(f, a)
        }
        Term::Application { op, args, .. } if op == "lam" && args.len() == 2 => {
            let ty = Rc::new(term_to_expr(&args[0]));
            let body = Rc::new(term_to_expr(&args[1]));
            Expr::Lambda(Name::new("x"), BinderInfo::Default, ty, body)
        }
        Term::Application { op, args, .. } if op == "letE" && args.len() == 3 => {
            let ty = Rc::new(term_to_expr(&args[0]));
            let value = Rc::new(term_to_expr(&args[1]));
            let body = Rc::new(term_to_expr(&args[2]));
            Expr::Let(Name::new("x"), ty, value, body, false)
        }
        Term::Constant(name, _) if name == "zeroE" => {
            Expr::mk_const(Name::new("zero"), vec![])
        }
        Term::Application { op, args, .. } if op == "succE" && args.len() == 1 => {
            let arg = term_to_expr(&args[0]);
            Expr::mk_app(Expr::mk_const(Name::new("succ"), vec![]), arg)
        }
        Term::Constant(name, _) if name == "nilE" => {
            Expr::mk_const(Name::new("nil"), vec![])
        }
        Term::Application { op, args, .. } if op == "consE" && args.len() == 2 => {
            let a = term_to_expr(&args[0]);
            let l = term_to_expr(&args[1]);
            Expr::mk_app(
                Expr::mk_app(Expr::mk_const(Name::new("cons"), vec![]), a),
                l,
            )
        }
        Term::NatLiteral(n) => Expr::Lit(Literal::Nat(*n)),
        Term::StringLiteral(s) => Expr::Lit(Literal::String(s.clone())),
        _ => {
            // Fallback
            Expr::Const(Name::new(&format!("maude_term_{}", t)), vec![])
        }
    }
}

fn term_to_name(t: &Term) -> Name {
    match t {
        Term::Constant(name, _) => Name::new(name),
        Term::Qid(q) => Name::new(q),
        _ => Name::new("invalid_name"),
    }
}

/// Load the standard Lean kernel equations from `lean_kernel.maude`.
/// Returns the combined list of equations from LeanSubst and LeanReduce modules.
pub fn load_lean_kernel_equations() -> Result<Vec<Equation>, String> {
    let content = include_str!("../../lean_kernel.maude");
    let mut parser = Parser::new(content).map_err(|e| format!("Lexer error: {}", e))?;
    let (modules, _) = parser.parse_script().map_err(|e| format!("Parse error: {}", e))?;

    let mut equations = Vec::new();
    for module in &modules {
        match module {
            Module::Functional { equations: eqs, .. } => {
                equations.extend_from_slice(eqs);
            }
            Module::System { equations: eqs, .. } => {
                equations.extend_from_slice(eqs);
            }
        }
    }
    Ok(equations)
}

/// Reduce a Lean expression using the Maude rewrite engine.
/// This translates the expression to a Maude term, applies the standard
/// Lean kernel reduction equations (beta, zeta, iota), and translates back.
pub fn reduce_expr(e: &Expr) -> Result<Expr, String> {
    let equations = load_lean_kernel_equations()?;
    let term = expr_to_term(e);
    let engine = RewriteEngine::new();
    let reduced = engine.reduce(&term, &equations);
    Ok(term_to_expr(&reduced))
}

/// Reduce a Lean expression using the Maude rewrite engine, with delta reduction
/// from the given environment. Definitions and theorems in the environment are
/// added as equations, so they are unfolded during reduction.
pub fn reduce_expr_with_env(e: &Expr, env: &Environment) -> Result<Expr, String> {
    let mut equations = load_lean_kernel_equations()?;

    // Add delta equations for definitions and theorems
    env.for_each_constant(|info| {
        if info.is_definition() || info.is_theorem() {
            if let Some(val) = info.get_value(false) {
                equations.push(Equation {
                    label: None,
                    lhs: Term::Application {
                        op: "const".to_string(),
                        args: vec![name_to_term(info.name())],
                        sort: Sort("Expr".to_string()),
                    },
                    rhs: expr_to_term(val),
                    condition: None,
                });
            }
        }
    });

    let term = expr_to_term(e);
    let engine = RewriteEngine::new();
    let reduced = engine.reduce(&term, &equations);
    Ok(term_to_expr(&reduced))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lean::declaration::*;
    use crate::lean::environment::Environment;

    #[test]
    fn test_expr_to_term_bvar() {
        let e = Expr::BVar(0);
        let t = expr_to_term(&e);
        assert_eq!(
            t,
            Term::Application {
                op: "bvar".to_string(),
                args: vec![Term::NatLiteral(0)],
                sort: Sort("Expr".to_string()),
            }
        );
    }

    #[test]
    fn test_expr_to_term_const() {
        let e = Expr::mk_const(Name::new("Nat"), vec![]);
        let t = expr_to_term(&e);
        assert_eq!(
            t,
            Term::Application {
                op: "const".to_string(),
                args: vec![Term::Constant("Nat".to_string(), Sort("Name".to_string()))],
                sort: Sort("Expr".to_string()),
            }
        );
    }

    #[test]
    fn test_expr_to_term_app() {
        let e = Expr::mk_app(Expr::mk_const(Name::new("f"), vec![]), Expr::mk_const(Name::new("a"), vec![]));
        let t = expr_to_term(&e);
        match t {
            Term::Application { op, args, .. } => {
                assert_eq!(op, "app");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected app"),
        }
    }

    #[test]
    fn test_expr_to_term_zero() {
        let e = Expr::mk_const(Name::new("zero"), vec![]);
        let t = expr_to_term(&e);
        assert_eq!(t, Term::Constant("zeroE".to_string(), Sort("Expr".to_string())));
    }

    #[test]
    fn test_expr_to_term_succ() {
        let e = Expr::mk_app(Expr::mk_const(Name::new("succ"), vec![]), Expr::mk_const(Name::new("zero"), vec![]));
        let t = expr_to_term(&e);
        assert_eq!(
            t,
            Term::Application {
                op: "succE".to_string(),
                args: vec![Term::Constant("zeroE".to_string(), Sort("Expr".to_string()))],
                sort: Sort("Expr".to_string()),
            }
        );
    }

    #[test]
    fn test_roundtrip() {
        let e = Expr::mk_app(
            Expr::Lambda(
                Name::new("x"),
                BinderInfo::Default,
                Rc::new(Expr::mk_const(Name::new("Nat"), vec![])),
                Rc::new(Expr::BVar(0)),
            ),
            Expr::mk_const(Name::new("zero"), vec![]),
        );
        let t = expr_to_term(&e);
        let e2 = term_to_expr(&t);
        // Note: roundtrip loses binder names and types for lambda domain
        // but structure is preserved
        match e2 {
            Expr::App(f, a) => {
                match f.as_ref() {
                    Expr::Lambda(_, _, _, body) => {
                        assert_eq!(body.as_ref(), &Expr::BVar(0));
                    }
                    _ => panic!("Expected Lambda"),
                }
                assert_eq!(a.as_ref(), &Expr::mk_const(Name::new("zero"), vec![]));
            }
            _ => panic!("Expected App"),
        }
    }

    #[test]
    fn test_reduce_beta() {
        // (λx. x) zero  ~>  zero
        let e = Expr::mk_app(
            Expr::Lambda(
                Name::new("x"),
                BinderInfo::Default,
                Rc::new(Expr::mk_const(Name::new("Nat"), vec![])),
                Rc::new(Expr::BVar(0)),
            ),
            Expr::mk_const(Name::new("zero"), vec![]),
        );
        let result = reduce_expr(&e).unwrap();
        assert_eq!(result, Expr::mk_const(Name::new("zero"), vec![]));
    }

    #[test]
    fn test_reduce_let() {
        // let x := zero in x  ~>  zero
        let e = Expr::Let(
            Name::new("x"),
            Rc::new(Expr::mk_const(Name::new("Nat"), vec![])),
            Rc::new(Expr::mk_const(Name::new("zero"), vec![])),
            Rc::new(Expr::BVar(0)),
            false,
        );
        let result = reduce_expr(&e).unwrap();
        assert_eq!(result, Expr::mk_const(Name::new("zero"), vec![]));
    }

    #[test]
    fn test_reduce_nat_recursor_zero() {
        // Nat.rec (λ_. Nat) zero (λn ih. succ ih) zero  ~>  zero
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let succ = Expr::mk_const(Name::new("succ"), vec![]);

        let motive = Expr::mk_lambda(Name::new("_"), nat.clone(), nat.clone());
        let succ_minor = Expr::Lambda(
            Name::new("n"),
            BinderInfo::Default,
            Rc::new(nat.clone()),
            Rc::new(Expr::Lambda(
                Name::new("ih"),
                BinderInfo::Default,
                Rc::new(nat.clone()),
                Rc::new(Expr::mk_app(succ.clone(), Expr::BVar(0))),
            )),
        );

        let nat_rec = Expr::mk_const(Name::new("recNat"), vec![]);
        let e = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(Expr::mk_app(nat_rec, motive), zero.clone()),
                succ_minor,
            ),
            zero.clone(),
        );
        let result = reduce_expr(&e).unwrap();
        assert_eq!(result, zero);
    }

    #[test]
    fn test_reduce_nat_recursor_succ() {
        // Nat.rec (λ_. Nat) zero (λn ih. succ ih) (succ zero)  ~>  succ zero
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let succ = Expr::mk_const(Name::new("succ"), vec![]);

        let motive = Expr::mk_lambda(Name::new("_"), nat.clone(), nat.clone());
        let succ_minor = Expr::Lambda(
            Name::new("n"),
            BinderInfo::Default,
            Rc::new(nat.clone()),
            Rc::new(Expr::Lambda(
                Name::new("ih"),
                BinderInfo::Default,
                Rc::new(nat.clone()),
                Rc::new(Expr::mk_app(succ.clone(), Expr::BVar(0))),
            )),
        );

        let nat_rec = Expr::mk_const(Name::new("recNat"), vec![]);
        let one = Expr::mk_app(succ.clone(), zero.clone());
        let e = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(Expr::mk_app(nat_rec, motive), zero.clone()),
                succ_minor,
            ),
            one.clone(),
        );
        let result = reduce_expr(&e).unwrap();
        assert_eq!(result, one);
    }

    #[test]
    fn test_reduce_list_recursor_nil() {
        // recList Nat (λ_. Nat) zero (λa l ih. succ ih) nil  ~>  zero
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let succ = Expr::mk_const(Name::new("succ"), vec![]);

        let motive = Expr::mk_lambda(Name::new("_"), nat.clone(), nat.clone());
        let nil_case = zero.clone();
        let cons_case = Expr::Lambda(
            Name::new("a"), BinderInfo::Default, Rc::new(nat.clone()),
            Rc::new(Expr::Lambda(
                Name::new("l"), BinderInfo::Default, Rc::new(nat.clone()),
                Rc::new(Expr::Lambda(
                    Name::new("ih"), BinderInfo::Default, Rc::new(nat.clone()),
                    Rc::new(Expr::mk_app(succ.clone(), Expr::BVar(0)))
                ))
            ))
        );

        let list_rec = Expr::mk_const(Name::new("recList"), vec![]);
        let nil = Expr::mk_const(Name::new("nil"), vec![]);
        let e = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_app(list_rec, nat.clone()), motive),
                    nil_case.clone()
                ),
                cons_case
            ),
            nil
        );
        let result = reduce_expr(&e).unwrap();
        assert_eq!(result, zero);
    }

    #[test]
    fn test_reduce_list_recursor_cons() {
        // recList Nat (λ_. Nat) zero (λa l ih. succ ih) (cons zero nil)  ~>  succ zero
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let succ = Expr::mk_const(Name::new("succ"), vec![]);

        let motive = Expr::mk_lambda(Name::new("_"), nat.clone(), nat.clone());
        let nil_case = zero.clone();
        let cons_case = Expr::Lambda(
            Name::new("a"), BinderInfo::Default, Rc::new(nat.clone()),
            Rc::new(Expr::Lambda(
                Name::new("l"), BinderInfo::Default, Rc::new(nat.clone()),
                Rc::new(Expr::Lambda(
                    Name::new("ih"), BinderInfo::Default, Rc::new(nat.clone()),
                    Rc::new(Expr::mk_app(succ.clone(), Expr::BVar(0)))
                ))
            ))
        );

        let list_rec = Expr::mk_const(Name::new("recList"), vec![]);
        let cons = Expr::mk_const(Name::new("cons"), vec![]);
        let nil = Expr::mk_const(Name::new("nil"), vec![]);
        let test_list = Expr::mk_app(Expr::mk_app(cons, zero.clone()), nil);
        let e = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_app(list_rec, nat.clone()), motive),
                    nil_case.clone()
                ),
                cons_case
            ),
            test_list
        );
        let result = reduce_expr(&e).unwrap();
        assert_eq!(result, Expr::mk_app(succ, zero));
    }

    #[test]
    fn test_cross_validation_beta() {
        // Compare Rust whnf with Maude reduce on beta reduction
        use crate::lean::type_checker::*;

        let env = {
            let mut env = Environment::new();
            let nat_decl = Declaration::Axiom(AxiomVal {
                constant_val: ConstantVal {
                    name: Name::new("Nat"),
                    level_params: vec![],
                    ty: Expr::mk_type(),
                },
                is_unsafe: false,
            });
            env.add(nat_decl).unwrap();
            env
        };

        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let lam = Expr::Lambda(
            Name::new("x"),
            BinderInfo::Default,
            Rc::new(nat.clone()),
            Rc::new(Expr::BVar(0)),
        );
        let app = Expr::mk_app(lam, zero.clone());

        let rust_result = tc.whnf(&app);
        let maude_result = reduce_expr(&app).unwrap();

        assert_eq!(rust_result, zero);
        assert_eq!(maude_result, zero);
        assert_eq!(rust_result, maude_result);
    }

    #[test]
    fn test_cross_validation_let() {
        // Compare Rust whnf with Maude reduce on let reduction
        use crate::lean::type_checker::*;

        let env = {
            let mut env = Environment::new();
            let nat_decl = Declaration::Axiom(AxiomVal {
                constant_val: ConstantVal {
                    name: Name::new("Nat"),
                    level_params: vec![],
                    ty: Expr::mk_type(),
                },
                is_unsafe: false,
            });
            env.add(nat_decl).unwrap();
            env
        };

        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let let_expr = Expr::Let(
            Name::new("x"),
            Rc::new(nat.clone()),
            Rc::new(zero.clone()),
            Rc::new(Expr::BVar(0)),
            false,
        );

        let rust_result = tc.whnf(&let_expr);
        let maude_result = reduce_expr(&let_expr).unwrap();

        assert_eq!(rust_result, zero);
        assert_eq!(maude_result, zero);
        assert_eq!(rust_result, maude_result);
    }

    #[test]
    fn test_reduce_with_env_delta() {
        // Test delta reduction: unfold a definition via Maude
        let mut env = Environment::new();

        let nat_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("Nat"),
                level_params: vec![],
                ty: Expr::mk_type(),
            },
            is_unsafe: false,
        });
        env.add(nat_decl).unwrap();

        let zero_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("zero"),
                level_params: vec![],
                ty: Expr::mk_const(Name::new("Nat"), vec![]),
            },
            is_unsafe: false,
        });
        env.add(zero_decl).unwrap();

        let succ_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("succ"),
                level_params: vec![],
                ty: Expr::mk_arrow(Expr::mk_const(Name::new("Nat"), vec![]), Expr::mk_const(Name::new("Nat"), vec![])),
            },
            is_unsafe: false,
        });
        env.add(succ_decl).unwrap();

        // Define one := succ zero
        let one_def = Declaration::Definition(DefinitionVal {
            constant_val: ConstantVal {
                name: Name::new("one"),
                level_params: vec![],
                ty: Expr::mk_const(Name::new("Nat"), vec![]),
            },
            value: Expr::mk_app(Expr::mk_const(Name::new("succ"), vec![]), Expr::mk_const(Name::new("zero"), vec![])),
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
        });
        env.add(one_def).unwrap();

        // Reduce "one" via Maude with environment
        let e = Expr::mk_const(Name::new("one"), vec![]);
        let result = reduce_expr_with_env(&e, &env).unwrap();

        let expected = Expr::mk_app(Expr::mk_const(Name::new("succ"), vec![]), Expr::mk_const(Name::new("zero"), vec![]));
        assert_eq!(result, expected);
    }

    #[test]
    fn test_reduce_with_env_nested_delta() {
        // Test nested delta reduction: two := succ one, where one := succ zero
        let mut env = Environment::new();

        let nat_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("Nat"),
                level_params: vec![],
                ty: Expr::mk_type(),
            },
            is_unsafe: false,
        });
        env.add(nat_decl).unwrap();

        let zero_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("zero"),
                level_params: vec![],
                ty: Expr::mk_const(Name::new("Nat"), vec![]),
            },
            is_unsafe: false,
        });
        env.add(zero_decl).unwrap();

        let succ = Expr::mk_const(Name::new("succ"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);

        let succ_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("succ"),
                level_params: vec![],
                ty: Expr::mk_arrow(Expr::mk_const(Name::new("Nat"), vec![]), Expr::mk_const(Name::new("Nat"), vec![])),
            },
            is_unsafe: false,
        });
        env.add(succ_decl).unwrap();

        // one := succ zero
        let one_def = Declaration::Definition(DefinitionVal {
            constant_val: ConstantVal {
                name: Name::new("one"),
                level_params: vec![],
                ty: Expr::mk_const(Name::new("Nat"), vec![]),
            },
            value: Expr::mk_app(succ.clone(), zero.clone()),
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
        });
        env.add(one_def).unwrap();

        // two := succ one
        let two_def = Declaration::Definition(DefinitionVal {
            constant_val: ConstantVal {
                name: Name::new("two"),
                level_params: vec![],
                ty: Expr::mk_const(Name::new("Nat"), vec![]),
            },
            value: Expr::mk_app(succ.clone(), Expr::mk_const(Name::new("one"), vec![])),
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
        });
        env.add(two_def).unwrap();

        // Reduce "two" via Maude with environment
        let e = Expr::mk_const(Name::new("two"), vec![]);
        let result = reduce_expr_with_env(&e, &env).unwrap();

        // Should be succ (succ zero)
        let expected = Expr::mk_app(succ.clone(), Expr::mk_app(succ, zero));
        assert_eq!(result, expected);
    }
}
