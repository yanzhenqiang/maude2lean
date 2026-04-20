// Test for Eq recursor generation

#[cfg(test)]
mod tests {
    use crate::lean::environment::*;
    use crate::lean::expr::*;
    use crate::lean::type_checker::*;

    #[test] 
    fn test_eq_recursor_type() {
        let mut env = Environment::new();
        
        let ty = Expr::mk_type();
        // Eq : Type -> A -> A -> Prop
        let eq_ty = Expr::mk_pi(Name::new("A"), ty.clone(),
            Expr::mk_pi(Name::new("a"), Expr::mk_bvar(0),
                Expr::mk_pi(Name::new("b"), Expr::mk_bvar(1),
                    Expr::mk_sort(Level::Zero))));
        
        let eq_ind = InductiveType {
            name: Name::new("Eq"),
            ty: eq_ty,
            ctors: vec![
                Constructor {
                    name: Name::new("refl"),
                    ty: Expr::mk_pi(Name::new("A"), ty.clone(),
                        Expr::mk_pi(Name::new("a"), Expr::mk_bvar(0),
                            Expr::mk_app(Expr::mk_app(Expr::mk_app(
                                Expr::mk_const(Name::new("Eq"), vec![]),
                                Expr::mk_bvar(1)), Expr::mk_bvar(0)), Expr::mk_bvar(0)))),
                },
            ],
        };
        
        let decl = Declaration::Inductive {
            level_params: vec![],
            num_params: 2,
            types: vec![eq_ind],
            is_unsafe: false,
        };
        env.add(decl).unwrap();
        
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);
        
        let eq_rec = Expr::mk_const(Name::new("rec").extend("Eq"), vec![]);
        let rec_ty = tc.infer(&eq_rec).unwrap();
        println!("Eq.rec type: {}", crate::lean::repl::format_expr(&rec_ty));
        
        // The type should have 6 binders: A, a, P, refl_case, b, h
        // Check that it has the right number of nested Pi binders
        let mut count = 0;
        let mut current = &rec_ty;
        while let Expr::Pi(_, _, _, body) = current {
            count += 1;
            current = body;
        }
        assert_eq!(count, 6, "Eq.rec should have 6 Pi binders, got {}", count);
    }
}
