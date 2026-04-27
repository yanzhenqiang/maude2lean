use std::hash::Hash;
use std::rc::Rc;

/// Lean names are hierarchical, e.g., `Nat.add`, `_root_.Foo.bar`
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

    pub fn last(&self) -> &str {
        self.0.last().map(|s| s.as_str()).unwrap_or("")
    }

    pub fn len(&self) -> usize {
        self.0.len()
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

    pub fn is_max(&self) -> bool {
        matches!(self, Level::Max(_, _))
    }

    pub fn is_imax(&self) -> bool {
        matches!(self, Level::IMax(_, _))
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

    /// Normalize a level expression
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

    /// Check if two levels are equivalent (after normalization)
    pub fn is_equivalent(&self, other: &Level) -> bool {
        self.normalize() == other.normalize()
    }

    /// Convert explicit level to unsigned integer
    pub fn to_explicit(&self) -> Option<u32> {
        match self {
            Level::Zero => Some(0),
            Level::Succ(l) => l.to_explicit().map(|n| n + 1),
            _ => None,
        }
    }

    /// Check if this level is greater than or equal to another
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
        (Level::IMax(_a, b), _) => {
            // imax(a, b) >= l2 iff b >= l2 (when b >= 1)
            // or if a >= l2 and b >= l2
            is_geq_core(b, l2)
        }
        (Level::Param(p1), Level::Param(p2)) => p1 == p2,
        (l, Level::Param(_)) => {
            // Check if l contains the param and is larger
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
    Rec,
}

impl BinderInfo {
    pub fn is_implicit(&self) -> bool {
        matches!(self, BinderInfo::Implicit | BinderInfo::StrictImplicit | BinderInfo::InstImplicit)
    }

    pub fn is_explicit(&self) -> bool {
        !self.is_implicit()
    }
}

/// Literal values
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    String(String),
}

/// Lean expressions
/// Based on Lean 4 kernel's `expr.h`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    /// Bound variable (de Bruijn index)
    BVar(u64),
    /// Free variable (local variable)
    FVar(Name),
    /// Metavariable
    MVar(Name),
    /// Universe sort: Sort u
    Sort(Level),
    /// Constant reference: c.{us}
    Const(Name, Vec<Level>),
    /// Application: f a
    App(Rc<Expr>, Rc<Expr>),
    /// Lambda abstraction: λ (x : t). b
    Lambda(Name, BinderInfo, Rc<Expr>, Rc<Expr>),
    /// Dependent arrow: Π (x : t). b
    Pi(Name, BinderInfo, Rc<Expr>, Rc<Expr>),
    /// Let expression: let x : t := v in b
    Let(Name, Rc<Expr>, Rc<Expr>, Rc<Expr>, bool),
    /// Literal value
    Lit(Literal),
    /// Metadata
    MData(Rc<MData>, Rc<Expr>),
    /// Projection
    Proj(Name, u64, Rc<Expr>),
}

/// Metadata map (simplified)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MData {
    pub data: Vec<(String, Expr)>,
}

impl Expr {
    // Constructors
    pub fn mk_bvar(idx: u64) -> Expr {
        Expr::BVar(idx)
    }

    pub fn mk_fvar(name: Name) -> Expr {
        Expr::FVar(name)
    }

    pub fn mk_mvar(name: Name) -> Expr {
        Expr::MVar(name)
    }

    pub fn mk_sort(level: Level) -> Expr {
        Expr::Sort(level)
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

    pub fn mk_let(name: Name, ty: Expr, value: Expr, body: Expr) -> Expr {
        Expr::Let(name, Rc::new(ty), Rc::new(value), Rc::new(body), false)
    }

    pub fn mk_lit(lit: Literal) -> Expr {
        Expr::Lit(lit)
    }

    pub fn mk_prop() -> Expr {
        Expr::Sort(Level::Zero)
    }

    pub fn mk_type() -> Expr {
        Expr::Sort(Level::mk_succ(Level::Zero))
    }

    // Tests
    pub fn is_bvar(&self) -> bool { matches!(self, Expr::BVar(_)) }
    pub fn is_fvar(&self) -> bool { matches!(self, Expr::FVar(_)) }
    pub fn is_mvar(&self) -> bool { matches!(self, Expr::MVar(_)) }
    pub fn is_sort(&self) -> bool { matches!(self, Expr::Sort(_)) }
    pub fn is_const(&self) -> bool { matches!(self, Expr::Const(_, _)) }
    pub fn is_app(&self) -> bool { matches!(self, Expr::App(_, _)) }
    pub fn is_lambda(&self) -> bool { matches!(self, Expr::Lambda(_, _, _, _)) }
    pub fn is_pi(&self) -> bool { matches!(self, Expr::Pi(_, _, _, _)) }
    pub fn is_let(&self) -> bool { matches!(self, Expr::Let(_, _, _, _, _)) }
    pub fn is_lit(&self) -> bool { matches!(self, Expr::Lit(_)) }
    pub fn is_proj(&self) -> bool { matches!(self, Expr::Proj(_, _, _)) }

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
            Expr::Lambda(n, _, _, _) | Expr::Pi(n, _, _, _) | Expr::Let(n, _, _, _, _) => Some(n),
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

    pub fn let_type(&self) -> Option<&Expr> {
        match self {
            Expr::Let(_, t, _, _, _) => Some(t),
            _ => None,
        }
    }

    pub fn let_value(&self) -> Option<&Expr> {
        match self {
            Expr::Let(_, _, v, _, _) => Some(v),
            _ => None,
        }
    }

    pub fn let_body(&self) -> Option<&Expr> {
        match self {
            Expr::Let(_, _, _, b, _) => Some(b),
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
            Expr::Sort(l) => Expr::Sort(l.clone()),
            Expr::Const(name, levels) => Expr::Const(name.clone(), levels.clone()),
            Expr::FVar(name) => Expr::FVar(name.clone()),
            Expr::MVar(name) => Expr::MVar(name.clone()),
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
            Expr::Let(name, ty, value, body, nondep) => {
                Expr::Let(
                    name.clone(),
                    Rc::new(ty.lift_loose_bvars(n, threshold)),
                    Rc::new(value.lift_loose_bvars(n, threshold)),
                    Rc::new(body.lift_loose_bvars(n, threshold + 1)),
                    *nondep,
                )
            }
            Expr::Lit(lit) => Expr::Lit(lit.clone()),
            Expr::MData(d, e) => Expr::MData(d.clone(), Rc::new(e.lift_loose_bvars(n, threshold))),
            Expr::Proj(s, i, e) => Expr::Proj(s.clone(), *i, Rc::new(e.lift_loose_bvars(n, threshold))),
        }
    }

    /// Check if the expression contains a specific free variable.
    pub fn contains_fvar(&self, fvar_name: &Name) -> bool {
        match self {
            Expr::FVar(name) => name == fvar_name,
            Expr::App(f, a) => f.contains_fvar(fvar_name) || a.contains_fvar(fvar_name),
            Expr::Lambda(_, _, ty, body) |
            Expr::Pi(_, _, ty, body) => ty.contains_fvar(fvar_name) || body.contains_fvar(fvar_name),
            Expr::Let(_, ty, value, body, _) => {
                ty.contains_fvar(fvar_name) || value.contains_fvar(fvar_name) || body.contains_fvar(fvar_name)
            }
            Expr::MData(_, e) | Expr::Proj(_, _, e) => e.contains_fvar(fvar_name),
            _ => false,
        }
    }

    /// Abstract a free variable into a bound variable.
    /// Replace occurrences of `fvar_name` with `BVar(depth)` and lift existing BVars accordingly.
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
            Expr::Sort(l) => Expr::Sort(l.clone()),
            Expr::Const(name, levels) => Expr::Const(name.clone(), levels.clone()),
            Expr::MVar(name) => Expr::MVar(name.clone()),
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
            Expr::Let(name, ty, value, body, nondep) => {
                Expr::Let(
                    name.clone(),
                    Rc::new(ty.abstract_fvar(fvar_name, depth)),
                    Rc::new(value.abstract_fvar(fvar_name, depth)),
                    Rc::new(body.abstract_fvar(fvar_name, depth + 1)),
                    *nondep,
                )
            }
            Expr::Lit(lit) => Expr::Lit(lit.clone()),
            Expr::MData(d, e) => Expr::MData(d.clone(), Rc::new(e.abstract_fvar(fvar_name, depth))),
            Expr::Proj(s, i, e) => Expr::Proj(s.clone(), *i, Rc::new(e.abstract_fvar(fvar_name, depth))),
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
            Expr::Sort(l) => Expr::Sort(l.clone()),
            Expr::Const(name, levels) => Expr::Const(name.clone(), levels.clone()),
            Expr::FVar(name) => Expr::FVar(name.clone()),
            Expr::MVar(name) => Expr::MVar(name.clone()),
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
            Expr::Let(name, ty, value, body, nondep) => {
                Expr::Let(
                    name.clone(),
                    Rc::new(ty.instantiate_range(subst, offset)),
                    Rc::new(value.instantiate_range(subst, offset)),
                    Rc::new(body.instantiate_range(subst, offset + 1)),
                    *nondep,
                )
            }
            Expr::Lit(lit) => Expr::Lit(lit.clone()),
            Expr::MData(d, e) => Expr::MData(d.clone(), Rc::new(e.instantiate_range(subst, offset))),
            Expr::Proj(s, i, e) => Expr::Proj(s.clone(), *i, Rc::new(e.instantiate_range(subst, offset))),
        }
    }

    /// Check if expression contains loose bound variable `idx`
    pub fn has_loose_bvar(&self, idx: u64) -> bool {
        match self {
            Expr::BVar(i) => *i == idx,
            Expr::App(f, a) => f.has_loose_bvar(idx) || a.has_loose_bvar(idx),
            Expr::Lambda(_, _, ty, body) => ty.has_loose_bvar(idx) || body.has_loose_bvar(idx + 1),
            Expr::Pi(_, _, ty, body) => ty.has_loose_bvar(idx) || body.has_loose_bvar(idx + 1),
            Expr::Let(_, ty, value, body, _) => {
                ty.has_loose_bvar(idx) || value.has_loose_bvar(idx) || body.has_loose_bvar(idx + 1)
            }
            Expr::MData(_, e) => e.has_loose_bvar(idx),
            Expr::Proj(_, _, e) => e.has_loose_bvar(idx),
            _ => false,
        }
    }

    /// Check if expression contains any metavariables
    pub fn has_expr_mvar(&self) -> bool {
        match self {
            Expr::MVar(_) => true,
            Expr::App(f, a) => f.has_expr_mvar() || a.has_expr_mvar(),
            Expr::Lambda(_, _, ty, body) => ty.has_expr_mvar() || body.has_expr_mvar(),
            Expr::Pi(_, _, ty, body) => ty.has_expr_mvar() || body.has_expr_mvar(),
            Expr::Let(_, ty, value, body, _) => {
                ty.has_expr_mvar() || value.has_expr_mvar() || body.has_expr_mvar()
            }
            Expr::MData(_, e) => e.has_expr_mvar(),
            Expr::Proj(_, _, e) => e.has_expr_mvar(),
            _ => false,
        }
    }

    /// Check if expression contains a specific named metavariable
    pub fn has_mvar_named(&self, name: &Name) -> bool {
        match self {
            Expr::MVar(n) => n == name,
            Expr::App(f, a) => f.has_mvar_named(name) || a.has_mvar_named(name),
            Expr::Lambda(_, _, ty, body) => ty.has_mvar_named(name) || body.has_mvar_named(name),
            Expr::Pi(_, _, ty, body) => ty.has_mvar_named(name) || body.has_mvar_named(name),
            Expr::Let(_, ty, value, body, _) => {
                ty.has_mvar_named(name) || value.has_mvar_named(name) || body.has_mvar_named(name)
            }
            Expr::MData(_, e) => e.has_mvar_named(name),
            Expr::Proj(_, _, e) => e.has_mvar_named(name),
            _ => false,
        }
    }

    /// Collect all named metavariables in the expression
    pub fn collect_mvars(&self, out: &mut Vec<Name>) {
        match self {
            Expr::MVar(n) => {
                if !out.contains(n) {
                    out.push(n.clone());
                }
            }
            Expr::App(f, a) => { f.collect_mvars(out); a.collect_mvars(out); }
            Expr::Lambda(_, _, ty, body) => { ty.collect_mvars(out); body.collect_mvars(out); }
            Expr::Pi(_, _, ty, body) => { ty.collect_mvars(out); body.collect_mvars(out); }
            Expr::Let(_, ty, value, body, _) => { ty.collect_mvars(out); value.collect_mvars(out); body.collect_mvars(out); }
            Expr::MData(_, e) => e.collect_mvars(out),
            Expr::Proj(_, _, e) => e.collect_mvars(out),
            _ => {}
        }
    }

    /// Check if expression contains any free variables
    pub fn has_fvar(&self) -> bool {
        match self {
            Expr::FVar(_) => true,
            Expr::App(f, a) => f.has_fvar() || a.has_fvar(),
            Expr::Lambda(_, _, ty, body) => ty.has_fvar() || body.has_fvar(),
            Expr::Pi(_, _, ty, body) => ty.has_fvar() || body.has_fvar(),
            Expr::Let(_, ty, value, body, _) => {
                ty.has_fvar() || value.has_fvar() || body.has_fvar()
            }
            Expr::MData(_, e) => e.has_fvar(),
            Expr::Proj(_, _, e) => e.has_fvar(),
            _ => false,
        }
    }

    /// Strip the first `n` Pi binders and instantiate their bound variables with the given arguments.
    /// Given `Pi(x1,T1, Pi(x2,T2, ... body))` and args `[a1, a2, ...]`,
    /// returns `body[a1/x1][a2/x2]...`.
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
            Expr::Let(name, ty, value, body, nondep) => Expr::Let(
                name.clone(),
                Rc::new(ty.replace_expr(target, replacement)),
                Rc::new(value.replace_expr(target, replacement)),
                Rc::new(body.replace_expr(target, replacement)),
                *nondep,
            ),
            Expr::MData(d, e) => Expr::MData(d.clone(), Rc::new(e.replace_expr(target, replacement))),
            Expr::Proj(s, i, e) => Expr::Proj(s.clone(), *i, Rc::new(e.replace_expr(target, replacement))),
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
        // max(0, u) = u
        let l = Level::mk_max(Level::Zero, Level::Param(Name::new("u")));
        assert_eq!(l.normalize(), Level::Param(Name::new("u")));

        // imax(u, 0) = 0
        let l = Level::mk_imax(Level::Param(Name::new("u")), Level::Zero);
        assert_eq!(l.normalize(), Level::Zero);

        // succ(max(a,b)) = max(succ(a), succ(b))
        let l = Level::mk_succ(Level::mk_max(Level::Param(Name::new("a")), Level::Param(Name::new("b"))));
        let expected = Level::mk_max(
            Level::mk_succ(Level::Param(Name::new("a"))),
            Level::mk_succ(Level::Param(Name::new("b"))),
        ).normalize();
        assert_eq!(l.normalize(), expected);
    }

    #[test]
    fn test_level_equivalent() {
        let a = Level::mk_max(Level::Zero, Level::Param(Name::new("u")));
        let b = Level::Param(Name::new("u"));
        assert!(a.is_equivalent(&b));
    }

    #[test]
    fn test_expr_instantiate_bvar() {
        // Substitute BVar(0) with `a` in App(BVar(0), BVar(1))
        // Result should be App(a, BVar(0))
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
        // Lift BVar(1) by 1 starting at threshold 1 -> BVar(2)
        let e = Expr::BVar(1);
        let result = e.lift_loose_bvars(1, 1);
        assert_eq!(result, Expr::BVar(2));

        // BVar(0) stays unchanged when threshold is 1
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
}
