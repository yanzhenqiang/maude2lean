use super::ast::*;
use std::collections::HashMap;

/// Order-sorted unification.
/// For now, implements basic syntactic unification.
pub fn unify(t1: &Term, t2: &Term) -> Option<HashMap<String, Term>> {
    let mut subst = HashMap::new();
    if unify_inner(t1, t2, &mut subst) {
        Some(subst)
    } else {
        None
    }
}

fn unify_inner(t1: &Term, t2: &Term, subst: &mut HashMap<String, Term>) -> bool {
    let t1 = apply_subst_term(t1, subst);
    let t2 = apply_subst_term(t2, subst);

    match (&t1, &t2) {
        (Term::Variable(name, _), other) | (other, Term::Variable(name, _)) => {
            if let Term::Variable(n, _) = other {
                if n == name { return true; }
            }
            // Occurs check
            if occurs_in(name, &t2) {
                return false;
            }
            subst.insert(name.clone(), t2.clone());
            true
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
                if !unify_inner(a1, a2, subst) {
                    return false;
                }
            }
            true
        }
        _ => false,
    }
}

fn occurs_in(var: &str, term: &Term) -> bool {
    match term {
        Term::Variable(name, _) => name == var,
        Term::Application { args, .. } => args.iter().any(|a| occurs_in(var, a)),
        _ => false,
    }
}

fn apply_subst_term(term: &Term, subst: &HashMap<String, Term>) -> Term {
    match term {
        Term::Variable(name, sort) => {
            if let Some(t) = subst.get(name) {
                t.clone()
            } else {
                Term::Variable(name.clone(), sort.clone())
            }
        }
        Term::Application { op, args, sort } => {
            let new_args: Vec<Term> = args.iter().map(|a| apply_subst_term(a, subst)).collect();
            Term::Application {
                op: op.clone(),
                args: new_args,
                sort: sort.clone(),
            }
        }
        other => other.clone(),
    }
}
