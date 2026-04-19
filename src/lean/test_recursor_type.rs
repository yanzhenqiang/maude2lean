#[cfg(test)]
mod tests {
    use super::*;
    use crate::lean::type_checker::*;

    #[test]
    fn test_nat_rec_type_check() {
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
            level_params: vec![], num_params: 0, types: vec![nat_ind], is_unsafe: false,
        };
        env.add(decl).unwrap();

        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let nat_rec = Expr::mk_const(Name::new("rec").extend("Nat"), vec![]);
        let rec_ty = tc.infer(&nat_rec).unwrap();
        println!("Nat.rec type: {:?}", rec_ty);
    }
}
