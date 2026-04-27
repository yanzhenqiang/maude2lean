// Temporary test file for auto-generated recursor
#[cfg(test)]
mod tests {
    use crate::environment::Environment;
    use crate::declaration::{Declaration, InductiveType, Constructor};
    use crate::expr::{Expr, Name, BinderInfo};
    use crate::type_checker::{TypeChecker, TypeCheckerState};
    use std::rc::Rc;

    fn setup_nat_env() -> (Environment, Expr) {
        let mut env = Environment::new();
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let nat_ind = InductiveType {
            name: Name::new("Nat"),
            ty: Expr::mk_type(),
            ctors: vec![
                Constructor { name: Name::new("zero"), ty: nat.clone() },
                Constructor { name: Name::new("succ"), ty: Expr::mk_arrow(nat.clone(), nat.clone()) },
            ],
        };
        let decl = Declaration::Inductive {
            level_params: vec![],
            num_params: 0,
            types: vec![nat_ind],
            is_unsafe: false,
        };
        env.add(decl).unwrap();
        (env, nat)
    }

    #[test]
    fn test_auto_nat_rec_zero() {
        let (env, nat) = setup_nat_env();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let nat_rec = Expr::mk_const(Name::new("rec").extend("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let motive = Expr::mk_lambda(Name::new("n"), nat.clone(), nat.clone());
        let succ_minor = Expr::Lambda(
            Name::new("n"), BinderInfo::Default, Rc::new(nat.clone()),
            Rc::new(Expr::Lambda(
                Name::new("ih"), BinderInfo::Default, Rc::new(nat.clone()),
                Rc::new(Expr::BVar(0))
            ))
        );

        // Nat.rec motive zero succ_minor zero  ~>  zero
        let app_zero = Expr::mk_app(
            Expr::mk_app(Expr::mk_app(Expr::mk_app(nat_rec, motive), zero.clone()), succ_minor),
            zero.clone()
        );
        let result = tc.whnf(&app_zero);
        assert_eq!(result, zero);
    }

    #[test]
    fn test_auto_nat_rec_succ_whnf() {
        let (env, nat) = setup_nat_env();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let nat_rec = Expr::mk_const(Name::new("rec").extend("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let succ = Expr::mk_const(Name::new("succ"), vec![]);
        let motive = Expr::mk_lambda(Name::new("n"), nat.clone(), nat.clone());
        let succ_minor = Expr::Lambda(
            Name::new("n"), BinderInfo::Default, Rc::new(nat.clone()),
            Rc::new(Expr::Lambda(
                Name::new("ih"), BinderInfo::Default, Rc::new(nat.clone()),
                Rc::new(Expr::mk_app(succ.clone(), Expr::BVar(0)))
            ))
        );

        // Nat.rec motive zero succ_minor (succ zero)
        // WHNF should be: succ (Nat.rec motive zero succ_minor zero)
        let one = Expr::mk_app(succ.clone(), zero.clone());
        let app_one = Expr::mk_app(
            Expr::mk_app(Expr::mk_app(Expr::mk_app(nat_rec.clone(), motive.clone()), zero.clone()), succ_minor.clone()),
            one.clone()
        );
        let result = tc.whnf(&app_one);

        let expected_inner = Expr::mk_app(
            Expr::mk_app(Expr::mk_app(Expr::mk_app(nat_rec, motive), zero.clone()), succ_minor), zero
        );
        let expected = Expr::mk_app(succ, expected_inner);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_auto_nat_add_nf() {
        let (env, nat) = setup_nat_env();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let nat_rec = Expr::mk_const(Name::new("rec").extend("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let succ = Expr::mk_const(Name::new("succ"), vec![]);

        // nat_add = λ m n, Nat.rec (λ _, Nat) m (λ _ ih, succ ih) n
        let nat_add = Expr::Lambda(
            Name::new("m"), BinderInfo::Default, Rc::new(nat.clone()),
            Rc::new(Expr::Lambda(
                Name::new("n"), BinderInfo::Default, Rc::new(nat.clone()),
                Rc::new(Expr::mk_app(
                    Expr::mk_app(
                        Expr::mk_app(
                            Expr::mk_app(
                                nat_rec.clone(),
                                Expr::mk_lambda(Name::new("_"), nat.clone(), nat.clone())
                            ),
                            Expr::BVar(1) // m
                        ),
                        Expr::Lambda(
                            Name::new("_"), BinderInfo::Default, Rc::new(nat.clone()),
                            Rc::new(Expr::Lambda(
                                Name::new("ih"), BinderInfo::Default, Rc::new(nat.clone()),
                                Rc::new(Expr::mk_app(succ.clone(), Expr::BVar(0)))
                            ))
                        )
                    ),
                    Expr::BVar(0) // n
                ))
            ))
        );

        // nat_add 3 2 = 5
        let three = Expr::mk_app(succ.clone(), Expr::mk_app(succ.clone(), Expr::mk_app(succ.clone(), zero.clone())));
        let two = Expr::mk_app(succ.clone(), Expr::mk_app(succ.clone(), zero.clone()));
        let five = Expr::mk_app(succ.clone(), Expr::mk_app(succ.clone(), Expr::mk_app(succ.clone(), Expr::mk_app(succ.clone(), Expr::mk_app(succ.clone(), zero.clone())))));

        let app = Expr::mk_app(Expr::mk_app(nat_add, three), two);
        let result = tc.nf(&app);
        assert_eq!(result, five);
    }
}
