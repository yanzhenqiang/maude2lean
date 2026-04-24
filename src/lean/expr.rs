use std::hash::Hash;
use std::rc::Rc;

/// Hierarchical names, e.g., `Nat.add`, `_root_.Foo.bar`
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Name(pub Vec<String>);

impl Name {
    pub fn new(s: &str) -> Self {
        Name(vec![s.to_string()])
    }

    pub fn extend(&self, s: &str) -> Self {
        let mut parts = self.0.clone();
        parts.push(s.to_string());
        Name(parts)
    }

    pub fn to_string(&self) -> String {
        self.0.join(".")
    }
}

/// Universe levels
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Level {
    Zero,
    Succ(Rc<Level>),
    Max(Rc<Level>, Rc<Level>),
    IMax(Rc<Level>, Rc<Level>),
    Param(Name),
    MVar(Name),
}

impl Level {
    pub fn mk_succ(l: Level) -> Level {
        Level::Succ(Rc::new(l))
    }

    pub fn mk_max(l1: Level, l2: Level) -> Level {
        Level::Max(Rc::new(l1), Rc::new(l2))
    }

    pub fn mk_imax(l1: Level, l2: Level) -> Level {
        Level::IMax(Rc::new(l1), Rc::new(l2))
    }

    pub fn is_zero(&self) -> bool {
        matches!(self, Level::Zero)
    }

    pub fn is_param(&self) -> bool {
        matches!(self, Level::Param(_))
    }

    pub fn is_mvar(&self) -> bool {
        matches!(self, Level::MVar(_))
    }

    pub fn is_succ(&self) -> bool {
        matches!(self, Level::Succ(_))
    }

    pub fn succ_of(&self) -> Option<&Level> {
        match self {
            Level::Succ(l) => Some(l),
            _ => None,
        }
    }

    pub fn max_lhs(&self) -> Option<&Level> {
        match self {
            Level::Max(l, _) => Some(l),
            Level::IMax(l, _) => Some(l),
            _ => None,
        }
    }

    pub fn max_rhs(&self) -> Option<&Level> {
        match self {
            Level::Max(_, r) => Some(r),
            Level::IMax(_, r) => Some(r),
            _ => None,
        }
    }

    pub fn param_id(&self) -> Option<&Name> {
        match self {
            Level::Param(n) => Some(n),
            Level::MVar(n) => Some(n),
            _ => None,
        }
    }

    pub fn normalize(&self) -> Level {
        match self {
            Level::Zero => Level::Zero,
            Level::Succ(l) => Level::mk_succ(l.normalize()),
            Level::Max(l1, l2) => {
                let n1 = l1.normalize();
                let n2 = l2.normalize();
                match (&n1, &n2) {
                    (Level::Zero, _) => n2,
                    (_, Level::Zero) => n1,
                    (Level::Succ(a), Level::Succ(b)) => {
                        Level::mk_succ(Level::mk_max((**a).clone(), (**b).clone()).normalize())
                    }
                    _ => Level::mk_max(n1, n2),
                }
            }
            Level::IMax(l1, l2) => {
                let n1 = l1.normalize();
                let n2 = l2.normalize();
                match (&n1, &n2) {
                    (_, Level::Zero) => Level::Zero,
                    (Level::Zero, _) => n2,
                    _ => Level::mk_imax(n1, n2),
                }
            }
            other => other.clone(),
        }
    }

    pub fn is_equivalent(&self, other: &Level) -> bool {
        self.normalize() == other.normalize()
    }

    pub fn to_explicit(&self) -> Option<u32> {
        match self {
            Level::Zero => Some(0),
            Level::Succ(l) => l.to_explicit().map(|n| n + 1),
            _ => None,
        }
    }

    pub fn is_geq(&self, other: &Level) -> bool {
        let n1 = self.normalize();
        let n2 = other.normalize();
        is_geq_core(&n1, &n2)
    }
}

fn is_geq_core(l1: &Level, l2: &Level) -> bool {
    match (l1, l2) {
        (_, Level::Zero) => true,
        (Level::Zero, _) => false,
        (Level::Succ(a), Level::Succ(b)) => is_geq_core(a, b),
        (Level::Max(a, b), _) => is_geq_core(a, l2) || is_geq_core(b, l2),
        (Level::IMax(_a, b), _) => is_geq_core(b, l2),
        (Level::Param(p1), Level::Param(p2)) => p1 == p2,
        (l, Level::Param(_)) => {
            if let Some(n) = l.to_explicit() {
                n > 0
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Binder information for Pi and Lambda
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

impl BinderInfo {
    pub fn is_implicit(&self) -> bool {
        matches!(self, BinderInfo::Implicit | BinderInfo::StrictImplicit | BinderInfo::InstImplicit)
    }

    pub fn is_explicit(&self) -> bool {
        !self.is_implicit()
    }
}

/// Core expression syntax for TTobs (Observational Type Theory)
/// Based on Pujet & Tabareau, POPL 2022, Figure 1
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    /// Bound variable (de Bruijn index)
    BVar(u64),
    /// Free variable (local variable, implementation detail)
    FVar(Name),
    /// Constant reference: c.{us}
    Const(Name, Vec<Level>),
    /// Application: f a
    App(Rc<Expr>, Rc<Expr>),
    /// Lambda abstraction: λ (x : A). b
    Lambda(Name, BinderInfo, Rc<Expr>, Rc<Expr>),
    /// Dependent product: Π (x : A). B
    Pi(Name, BinderInfo, Rc<Expr>, Rc<Expr>),
    /// Proof-relevant universe: U_i
    U(Level),
    /// Proof-irrelevant universe: Ω_i
    Omega(Level),
    /// Observational equality: t ~_A u  (stored as Eq(A, t, u))
    Eq(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    /// Cast: cast(A, B, e, t)
    Cast(Rc<Expr>, Rc<Expr>, Rc<Expr>, Rc<Expr>),
}

impl Expr {
    // Constructors
    pub fn mk_bvar(idx: u64) -> Expr {
        Expr::BVar(idx)
    }

    pub fn mk_fvar(name: Name) -> Expr {
        Expr::FVar(name)
    }

    pub fn mk_const(name: Name, levels: Vec<Level>) -> Expr {
        Expr::Const(name, levels)
    }

    pub fn mk_app(f: Expr, a: Expr) -> Expr {
        Expr::App(Rc::new(f), Rc::new(a))
    }

    pub fn mk_lambda(name: Name, ty: Expr, body: Expr) -> Expr {
        Expr::Lambda(name, BinderInfo::Default, Rc::new(ty), Rc::new(body))
    }

    pub fn mk_pi(name: Name, ty: Expr, body: Expr) -> Expr {
        Expr::Pi(name, BinderInfo::Default, Rc::new(ty), Rc::new(body))
    }

    pub fn mk_arrow(domain: Expr, codomain: Expr) -> Expr {
        Expr::Pi(Name::new("_"), BinderInfo::Default, Rc::new(domain), Rc::new(codomain))
    }

    pub fn mk_u(level: Level) -> Expr {
        Expr::U(level)
    }

    pub fn mk_omega(level: Level) -> Expr {
        Expr::Omega(level)
    }

    pub fn mk_eq(a: Expr, t: Expr, u: Expr) -> Expr {
        Expr::Eq(Rc::new(a), Rc::new(t), Rc::new(u))
    }

    pub fn mk_cast(a: Expr, b: Expr, e: Expr, t: Expr) -> Expr {
        Expr::Cast(Rc::new(a), Rc::new(b), Rc::new(e), Rc::new(t))
    }

    // Tests
    pub fn is_bvar(&self) -> bool { matches!(self, Expr::BVar(_)) }
    pub fn is_fvar(&self) -> bool { matches!(self, Expr::FVar(_)) }
    pub fn is_const(&self) -> bool { matches!(self, Expr::Const(_, _)) }
    pub fn is_app(&self) -> bool { matches!(self, Expr::App(_, _)) }
    pub fn is_lambda(&self) -> bool { matches!(self, Expr::Lambda(_, _, _, _)) }
    pub fn is_pi(&self) -> bool { matches!(self, Expr::Pi(_, _, _, _)) }
    pub fn is_u(&self) -> bool { matches!(self, Expr::U(_)) }
    pub fn is_omega(&self) -> bool { matches!(self, Expr::Omega(_)) }
    pub fn is_eq(&self) -> bool { matches!(self, Expr::Eq(_, _, _)) }
    pub fn is_cast(&self) -> bool { matches!(self, Expr::Cast(_, _, _, _)) }
    pub fn is_sort(&self) -> bool { matches!(self, Expr::U(_) | Expr::Omega(_)) }

    // Accessors
    pub fn app_fn(&self) -> Option<&Expr> {
        match self {
            Expr::App(f, _) => Some(f),
            _ => None,
        }
    }

    pub fn app_arg(&self) -> Option<&Expr> {
        match self {
            Expr::App(_, a) => Some(a),
            _ => None,
        }
    }

    pub fn bvar_idx(&self) -> Option<u64> {
        match self {
            Expr::BVar(i) => Some(*i),
            _ => None,
        }
    }

    pub fn const_name(&self) -> Option<&Name> {
        match self {
            Expr::Const(n, _) => Some(n),
            _ => None,
        }
    }

    pub fn const_levels(&self) -> Option<&Vec<Level>> {
        match self {
            Expr::Const(_, ls) => Some(ls),
            _ => None,
        }
    }

    pub fn binding_name(&self) -> Option<&Name> {
        match self {
            Expr::Lambda(n, _, _, _) | Expr::Pi(n, _, _, _) => Some(n),
            _ => None,
        }
    }

    pub fn binding_domain(&self) -> Option<&Expr> {
        match self {
            Expr::Lambda(_, _, t, _) | Expr::Pi(_, _, t, _) => Some(t),
            _ => None,
        }
    }

    pub fn binding_body(&self) -> Option<&Expr> {
        match self {
            Expr::Lambda(_, _, _, b) | Expr::Pi(_, _, _, b) => Some(b),
            _ => None,
        }
    }

    pub fn eq_type(&self) -> Option<&Expr> {
        match self {
            Expr::Eq(a, _, _) => Some(a),
            _ => None,
        }
    }

    pub fn eq_lhs(&self) -> Option<&Expr> {
        match self {
            Expr::Eq(_, t, _) => Some(t),
            _ => None,
        }

    }

    pub fn eq_rhs(&self) -> Option<&Expr> {
        match self {
            Expr::Eq(_, _, u) => Some(u),
            _ => None,
        }
    }

    pub fn cast_src(&self) -> Option<&Expr> {
        match self {
            Expr::Cast(a, _, _, _) => Some(a),
            _ => None,
        }
    }

    pub fn cast_dst(&self) -> Option<&Expr> {
        match self {
            Expr::Cast(_, b, _, _) => Some(b),
            _ => None,
        }
    }

    pub fn cast_proof(&self) -> Option<&Expr> {
        match self {
            Expr::Cast(_, _, e, _) => Some(e),
            _ => None,
        }
    }

    pub fn cast_term(&self) -> Option<&Expr> {
        match self {
            Expr::Cast(_, _, _, t) => Some(t),
            _ => None,
        }
    }

    /// Decompose an application into function and all arguments
    pub fn get_app_args(&self) -> (Option<&Expr>, Vec<&Expr>) {
        let mut args = Vec::new();
        let mut current = self;
        while let Expr::App(f, a) = current {
            args.push(a.as_ref());
            current = f;
        }
        args.reverse();
        (Some(current), args)
    }

    /// Get the head function of an application
    pub fn get_app_fn(&self) -> &Expr {
        let mut current = self;
        while let Expr::App(f, _) = current {
            current = f;
        }
        current
    }

    /// Count the number of arguments in an application
    pub fn get_app_num_args(&self) -> usize {
        let mut count = 0;
        let mut current = self;
        while let Expr::App(f, _) = current {
            count += 1;
            current = f;
        }
        count
    }

    /// Lift loose bound variables by `n` starting from `threshold`
    pub fn lift_loose_bvars(&self, n: u64, threshold: u64) -> Expr {
        match self {
            Expr::BVar(i) => {
                if *i >= threshold {
                    Expr::BVar(i + n)
                } else {
                    self.clone()
                }
            }
            Expr::U(l) => Expr::U(l.clone()),
            Expr::Omega(l) => Expr::Omega(l.clone()),
            Expr::Const(name, levels) => Expr::Const(name.clone(), levels.clone()),
            Expr::FVar(name) => Expr::FVar(name.clone()),
            Expr::App(f, a) => {
                Expr::App(
                    Rc::new(f.lift_loose_bvars(n, threshold)),
                    Rc::new(a.lift_loose_bvars(n, threshold)),
                )
            }
            Expr::Lambda(name, bi, ty, body) => {
                Expr::Lambda(
                    name.clone(),
                    *bi,
                    Rc::new(ty.lift_loose_bvars(n, threshold)),
                    Rc::new(body.lift_loose_bvars(n, threshold + 1)),
                )
            }
            Expr::Pi(name, bi, ty, body) => {
                Expr::Pi(
                    name.clone(),
                    *bi,
                    Rc::new(ty.lift_loose_bvars(n, threshold)),
                    Rc::new(body.lift_loose_bvars(n, threshold + 1)),
                )
            }
            Expr::Eq(a, t, u) => Expr::Eq(
                Rc::new(a.lift_loose_bvars(n, threshold)),
                Rc::new(t.lift_loose_bvars(n, threshold)),
                Rc::new(u.lift_loose_bvars(n, threshold)),
            ),
            Expr::Cast(a, b, e, t) => Expr::Cast(
                Rc::new(a.lift_loose_bvars(n, threshold)),
                Rc::new(b.lift_loose_bvars(n, threshold)),
                Rc::new(e.lift_loose_bvars(n, threshold)),
                Rc::new(t.lift_loose_bvars(n, threshold)),
            ),
        }
    }

    /// Abstract a free variable into a bound variable.
    pub fn abstract_fvar(&self, fvar_name: &Name, depth: u64) -> Expr {
        match self {
            Expr::FVar(name) => {
                if name == fvar_name {
                    Expr::mk_bvar(depth)
                } else {
                    self.clone()
                }
            }
            Expr::BVar(i) => {
                if *i >= depth {
                    Expr::mk_bvar(i + 1)
                } else {
                    self.clone()
                }
            }
            Expr::U(l) => Expr::U(l.clone()),
            Expr::Omega(l) => Expr::Omega(l.clone()),
            Expr::Const(name, levels) => Expr::Const(name.clone(), levels.clone()),
            Expr::App(f, a) => {
                Expr::App(
                    Rc::new(f.abstract_fvar(fvar_name, depth)),
                    Rc::new(a.abstract_fvar(fvar_name, depth)),
                )
            }
            Expr::Lambda(name, bi, ty, body) => {
                Expr::Lambda(
                    name.clone(),
                    *bi,
                    Rc::new(ty.abstract_fvar(fvar_name, depth)),
                    Rc::new(body.abstract_fvar(fvar_name, depth + 1)),
                )
            }
            Expr::Pi(name, bi, ty, body) => {
                Expr::Pi(
                    name.clone(),
                    *bi,
                    Rc::new(ty.abstract_fvar(fvar_name, depth)),
                    Rc::new(body.abstract_fvar(fvar_name, depth + 1)),
                )
            }
            Expr::Eq(a, t, u) => Expr::Eq(
                Rc::new(a.abstract_fvar(fvar_name, depth)),
                Rc::new(t.abstract_fvar(fvar_name, depth)),
                Rc::new(u.abstract_fvar(fvar_name, depth)),
            ),
            Expr::Cast(a, b, e, t) => Expr::Cast(
                Rc::new(a.abstract_fvar(fvar_name, depth)),
                Rc::new(b.abstract_fvar(fvar_name, depth)),
                Rc::new(e.abstract_fvar(fvar_name, depth)),
                Rc::new(t.abstract_fvar(fvar_name, depth)),
            ),
        }
    }

    /// Substitute bound variable 0 with `subst` in `self`
    pub fn instantiate(&self, subst: &Expr) -> Expr {
        self.instantiate_range(subst, 0)
    }

    fn instantiate_range(&self, subst: &Expr, offset: u64) -> Expr {
        match self {
            Expr::BVar(i) => {
                if *i == offset {
                    subst.lift_loose_bvars(offset, 0)
                } else if *i > offset {
                    Expr::BVar(i - 1)
                } else {
                    self.clone()
                }
            }
            Expr::U(l) => Expr::U(l.clone()),
            Expr::Omega(l) => Expr::Omega(l.clone()),
            Expr::Const(name, levels) => Expr::Const(name.clone(), levels.clone()),
            Expr::FVar(name) => Expr::FVar(name.clone()),
            Expr::App(f, a) => {
                Expr::App(
                    Rc::new(f.instantiate_range(subst, offset)),
                    Rc::new(a.instantiate_range(subst, offset)),
                )
            }
            Expr::Lambda(name, bi, ty, body) => {
                Expr::Lambda(
                    name.clone(),
                    *bi,
                    Rc::new(ty.instantiate_range(subst, offset)),
                    Rc::new(body.instantiate_range(subst, offset + 1)),
                )
            }
            Expr::Pi(name, bi, ty, body) => {
                Expr::Pi(
                    name.clone(),
                    *bi,
                    Rc::new(ty.instantiate_range(subst, offset)),
                    Rc::new(body.instantiate_range(subst, offset + 1)),
                )
            }
            Expr::Eq(a, t, u) => Expr::Eq(
                Rc::new(a.instantiate_range(subst, offset)),
                Rc::new(t.instantiate_range(subst, offset)),
                Rc::new(u.instantiate_range(subst, offset)),
            ),
            Expr::Cast(a, b, e, t) => Expr::Cast(
                Rc::new(a.instantiate_range(subst, offset)),
                Rc::new(b.instantiate_range(subst, offset)),
                Rc::new(e.instantiate_range(subst, offset)),
                Rc::new(t.instantiate_range(subst, offset)),
            ),
        }
    }

    /// Check if expression contains loose bound variable `idx`
    pub fn has_loose_bvar(&self, idx: u64) -> bool {
        match self {
            Expr::BVar(i) => *i == idx,
            Expr::App(f, a) => f.has_loose_bvar(idx) || a.has_loose_bvar(idx),
            Expr::Lambda(_, _, ty, body) => ty.has_loose_bvar(idx) || body.has_loose_bvar(idx + 1),
            Expr::Pi(_, _, ty, body) => ty.has_loose_bvar(idx) || body.has_loose_bvar(idx + 1),
            Expr::Eq(a, t, u) => a.has_loose_bvar(idx) || t.has_loose_bvar(idx) || u.has_loose_bvar(idx),
            Expr::Cast(a, b, e, t) => a.has_loose_bvar(idx) || b.has_loose_bvar(idx) || e.has_loose_bvar(idx) || t.has_loose_bvar(idx),
            _ => false,
        }
    }

    /// Check if expression contains any free variables
    pub fn has_fvar(&self) -> bool {
        match self {
            Expr::FVar(_) => true,
            Expr::App(f, a) => f.has_fvar() || a.has_fvar(),
            Expr::Lambda(_, _, ty, body) => ty.has_fvar() || body.has_fvar(),
            Expr::Pi(_, _, ty, body) => ty.has_fvar() || body.has_fvar(),
            Expr::Eq(a, t, u) => a.has_fvar() || t.has_fvar() || u.has_fvar(),
            Expr::Cast(a, b, e, t) => a.has_fvar() || b.has_fvar() || e.has_fvar() || t.has_fvar(),
            _ => false,
        }
    }

    /// Check if expression contains a Const with the given name.
    pub fn contains_const(&self, name: &Name) -> bool {
        match self {
            Expr::Const(n, _) => n == name,
            Expr::App(f, a) => f.contains_const(name) || a.contains_const(name),
            Expr::Lambda(_, _, ty, body) => ty.contains_const(name) || body.contains_const(name),
            Expr::Pi(_, _, ty, body) => ty.contains_const(name) || body.contains_const(name),
            Expr::Eq(a, t, u) => a.contains_const(name) || t.contains_const(name) || u.contains_const(name),
            Expr::Cast(a, b, e, t) => a.contains_const(name) || b.contains_const(name) || e.contains_const(name) || t.contains_const(name),
            _ => false,
        }
    }

    /// Strip the first `n` Pi binders and instantiate their bound variables with the given arguments.
    pub fn apply_pi_binders(&self, args: &[Expr]) -> Option<Expr> {
        let mut result = self.clone();
        for arg in args {
            match result {
                Expr::Pi(_, _, _, body) => {
                    result = body.instantiate(arg);
                }
                _ => return None,
            }
        }
        Some(result)
    }

    /// Replace all occurrences of `target` with `replacement` in this expression.
    pub fn replace_expr(&self, target: &Expr, replacement: &Expr) -> Expr {
        if self == target {
            return replacement.clone();
        }
        match self {
            Expr::App(f, a) => Expr::App(
                Rc::new(f.replace_expr(target, replacement)),
                Rc::new(a.replace_expr(target, replacement)),
            ),
            Expr::Lambda(name, bi, ty, body) => Expr::Lambda(
                name.clone(),
                *bi,
                Rc::new(ty.replace_expr(target, replacement)),
                Rc::new(body.replace_expr(target, replacement)),
            ),
            Expr::Pi(name, bi, ty, body) => Expr::Pi(
                name.clone(),
                *bi,
                Rc::new(ty.replace_expr(target, replacement)),
                Rc::new(body.replace_expr(target, replacement)),
            ),
            Expr::Eq(a, t, u) => Expr::Eq(
                Rc::new(a.replace_expr(target, replacement)),
                Rc::new(t.replace_expr(target, replacement)),
                Rc::new(u.replace_expr(target, replacement)),
            ),
            Expr::Cast(a, b, e, t) => Expr::Cast(
                Rc::new(a.replace_expr(target, replacement)),
                Rc::new(b.replace_expr(target, replacement)),
                Rc::new(e.replace_expr(target, replacement)),
                Rc::new(t.replace_expr(target, replacement)),
            ),
            _ => self.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_name_extend() {
        let n = Name::new("Foo").extend("bar");
        assert_eq!(n.to_string(), "Foo.bar");
    }

    #[test]
    fn test_level_normalize() {
        let l = Level::mk_max(Level::Zero, Level::Param(Name::new("u")));
        assert_eq!(l.normalize(), Level::Param(Name::new("u")));

        let l = Level::mk_imax(Level::Param(Name::new("u")), Level::Zero);
        assert_eq!(l.normalize(), Level::Zero);
    }

    #[test]
    fn test_expr_instantiate_bvar() {
        let a = Expr::mk_const(Name::new("a"), vec![]);
        let e = Expr::App(Rc::new(Expr::BVar(0)), Rc::new(Expr::BVar(1)));
        let result = e.instantiate(&a);
        match result {
            Expr::App(f, arg) => {
                assert_eq!(f.as_ref(), &a);
                assert_eq!(arg.as_ref(), &Expr::BVar(0));
            }
            _ => panic!("Expected App"),
        }
    }

    #[test]
    fn test_expr_lift_loose_bvars() {
        let e = Expr::BVar(1);
        let result = e.lift_loose_bvars(1, 1);
        assert_eq!(result, Expr::BVar(2));

        let e = Expr::BVar(0);
        let result = e.lift_loose_bvars(1, 1);
        assert_eq!(result, Expr::BVar(0));
    }

    #[test]
    fn test_expr_has_loose_bvar() {
        let e = Expr::App(Rc::new(Expr::BVar(0)), Rc::new(Expr::BVar(1)));
        assert!(e.has_loose_bvar(0));
        assert!(e.has_loose_bvar(1));
        assert!(!e.has_loose_bvar(2));
    }

    #[test]
    fn test_expr_get_app_args() {
        let a = Expr::mk_const(Name::new("a"), vec![]);
        let b = Expr::mk_const(Name::new("b"), vec![]);
        let c = Expr::mk_const(Name::new("c"), vec![]);
        let app = Expr::mk_app(Expr::mk_app(a.clone(), b.clone()), c.clone());
        let (fn_expr, args) = app.get_app_args();
        assert_eq!(fn_expr, Some(&a));
        assert_eq!(args, vec![&b, &c]);
    }

    #[test]
    fn test_mk_arrow() {
        let a = Expr::mk_const(Name::new("A"), vec![]);
        let b = Expr::mk_const(Name::new("B"), vec![]);
        let arrow = Expr::mk_arrow(a.clone(), b.clone());
        match arrow {
            Expr::Pi(name, bi, domain, codomain) => {
                assert_eq!(name.to_string(), "_");
                assert_eq!(bi, BinderInfo::Default);
                assert_eq!(domain.as_ref(), &a);
                assert_eq!(codomain.as_ref(), &b);
            }
            _ => panic!("Expected Pi"),
        }
    }

    #[test]
    fn test_mk_eq() {
        let a = Expr::mk_const(Name::new("A"), vec![]);
        let t = Expr::mk_const(Name::new("t"), vec![]);
        let u = Expr::mk_const(Name::new("u"), vec![]);
        let eq = Expr::mk_eq(a.clone(), t.clone(), u.clone());
        assert_eq!(eq.eq_type(), Some(&a));
        assert_eq!(eq.eq_lhs(), Some(&t));
        assert_eq!(eq.eq_rhs(), Some(&u));
    }

    #[test]
    fn test_mk_cast() {
        let a = Expr::mk_const(Name::new("A"), vec![]);
        let b = Expr::mk_const(Name::new("B"), vec![]);
        let e = Expr::mk_const(Name::new("e"), vec![]);
        let t = Expr::mk_const(Name::new("t"), vec![]);
        let cast = Expr::mk_cast(a.clone(), b.clone(), e.clone(), t.clone());
        assert_eq!(cast.cast_src(), Some(&a));
        assert_eq!(cast.cast_dst(), Some(&b));
        assert_eq!(cast.cast_proof(), Some(&e));
        assert_eq!(cast.cast_term(), Some(&t));
    }
}
