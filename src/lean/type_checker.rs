#[cfg(test)]
use super::declaration::*;
use super::environment::*;
use super::expr::*;
use super::local_ctx::*;
use std::collections::HashMap;
use std::rc::Rc;

/// A cache key for definitional equality
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ExprPair(Expr, Expr);

/// Type checker state (caches, metavariable assignments, etc.)
#[derive(Debug, Clone)]
pub struct TypeCheckerState {
    env: Environment,
    infer_cache: HashMap<Expr, Expr>,
    whnf_cache: HashMap<Expr, Expr>,
    failure_cache: HashMap<ExprPair, bool>,
    /// Metavariable assignments: ?m -> value
    mvar_assignments: HashMap<Name, Expr>,
    /// Universe level parameter substitutions: u -> level
    level_subst: HashMap<Name, Level>,
}

impl TypeCheckerState {
    pub fn new(env: Environment) -> Self {
        TypeCheckerState {
            env,
            infer_cache: HashMap::new(),
            whnf_cache: HashMap::new(),
            failure_cache: HashMap::new(),
            mvar_assignments: HashMap::new(),
            level_subst: HashMap::new(),
        }
    }

    pub fn env(&self) -> &Environment {
        &self.env
    }

    pub fn get_mvar_assignment(&self, name: &Name) -> Option<&Expr> {
        self.mvar_assignments.get(name)
    }

    pub fn assign_mvar(&mut self, name: &Name, val: Expr) -> bool {
        // Occur check: the metavariable must not occur in its assigned value
        if val.has_mvar_named(name) {
            return false;
        }
        self.mvar_assignments.insert(name.clone(), val);
        // Clear whnf cache since metavariable assignments can change reduction results
        self.whnf_cache.clear();
        true
    }

    pub fn clear_mvar_assignments(&mut self) {
        self.mvar_assignments.clear();
    }

    pub fn get_level_subst(&self, name: &Name) -> Option<&Level> {
        self.level_subst.get(name)
    }

    pub fn assign_level_param(&mut self, name: &Name, level: Level) -> bool {
        // Occur check for level params: avoid cyclic substitutions
        if Self::level_contains_param(&level, name) {
            return false;
        }
        self.level_subst.insert(name.clone(), level);
        true
    }

    pub fn clear_level_subst(&mut self) {
        self.level_subst.clear();
    }

    fn level_contains_param(level: &Level, name: &Name) -> bool {
        match level {
            Level::Param(n) => n == name,
            Level::MVar(n) => n == name,
            Level::Succ(l) => Self::level_contains_param(l, name),
            Level::Max(l1, l2) | Level::IMax(l1, l2) => {
                Self::level_contains_param(l1, name) || Self::level_contains_param(l2, name)
            }
            Level::Zero => false,
        }
    }
}

/// Lean kernel type checker
pub struct TypeChecker<'a> {
    st: &'a mut TypeCheckerState,
    lctx: LocalCtx,
}

impl<'a> TypeChecker<'a> {
    pub fn new(st: &'a mut TypeCheckerState) -> Self {
        TypeChecker {
            st,
            lctx: LocalCtx::new(),
        }
    }

    pub fn with_local_ctx(st: &'a mut TypeCheckerState, lctx: LocalCtx) -> Self {
        TypeChecker { st, lctx }
    }

    /// Infer the type of an expression
    pub fn infer(&mut self, e: &Expr) -> Result<Expr, String> {
        self.infer_type(e)
    }

    /// Check that an expression has a given type
    pub fn check(&mut self, e: &Expr, expected_ty: &Expr) -> Result<Expr, String> {
        let inferred = self.infer(e)?;
        if self.is_def_eq(&inferred, expected_ty) {
            Ok(inferred)
        } else {
            Err(format!(
                "Type mismatch: expected {}, got {} for expression {}",
                self.expr_to_string(expected_ty),
                self.expr_to_string(&inferred),
                self.expr_to_string(e)
            ))
        }
    }

    fn infer_type(&mut self, e: &Expr) -> Result<Expr, String> {
        // FVar and MVar types depend on local context / state which may change,
        // so we must not cache them.
        match e {
            Expr::FVar(name) => {
                return self.lctx
                    .get_type(&Expr::FVar(name.clone()))
                    .cloned()
                    .ok_or_else(|| format!("Unknown free variable {}", name.to_string()))
            }
            Expr::MVar(name) => {
                if let Some(val) = self.st.get_mvar_assignment(name).cloned() {
                    return self.infer_type(&val)
                } else {
                    return Err(format!("Unassigned metavariable {}", name.to_string()))
                }
            }
            _ => {}
        }

        // Check cache
        if let Some(ty) = self.st.infer_cache.get(e) {
            return Ok(ty.clone());
        }

        let result = match e {
            Expr::BVar(idx) => {
                if let Some(ty) = self.lctx.get_bvar_type(*idx) {
                    Ok(ty.clone())
                } else {
                    Err(format!("Unbound bound variable {} in expression {}", idx, self.expr_to_string(e)))
                }
            }
            Expr::FVar(_) | Expr::MVar(_) => {
                unreachable!("FVar and MVar are handled before the cache")
            }
            Expr::Sort(level) => {
                Ok(Expr::Sort(Level::mk_succ(level.clone())))
            }
            Expr::Const(name, levels) => {
                if !self.st.env().contains(name) {
                    return Err(format!("Constant not found: {:?}", name));
                }
                let info = self.st.env().get(name);
                if info.is_quot() {
                    return self.infer_quot_const(name, levels);
                }
                let ty = info.get_type();
                Ok(self.instantiate_univ_params(ty, info.get_level_params(), levels))
            }
            Expr::App(f, a) => {
                self.infer_app(f, a)
            }
            Expr::Lambda(name, bi, ty, body) => {
                // Ensure ty is a sort
                let ty_type = self.infer(ty)?;
                self.ensure_sort(&ty_type)?;

                // Create a fresh FVar for the binder and substitute BVar(0)
                let fvar = Expr::mk_fvar(name.clone());
                let mut new_lctx = self.lctx.clone();
                let converted_ty = new_lctx.replace_bvars_with_fvars(&ty);
                new_lctx.mk_local_decl(name.clone(), name.clone(), converted_ty, *bi);
                new_lctx.push_bvar(name.clone(), (**ty).clone());

                let body_inst = body.instantiate(&fvar);
                let mut tc = TypeChecker::with_local_ctx(self.st, new_lctx);
                let body_type = tc.infer(&body_inst)?;

                // Abstract the FVar back to a bound variable in the Pi body
                let body_type_abstracted = body_type.abstract_fvar(name, 0);

                Ok(Expr::Pi(name.clone(), *bi, ty.clone(), Rc::new(body_type_abstracted)))
            }
            Expr::Pi(name, bi, ty, body) => {
                let ty_type = self.infer(ty)?;
                let ty_level = self.ensure_sort(&ty_type)?;
                let ty_u = self.sort_level(&ty_level)?;

                let fvar = Expr::mk_fvar(name.clone());
                let mut new_lctx = self.lctx.clone();
                let converted_ty = new_lctx.replace_bvars_with_fvars(&ty);
                new_lctx.mk_local_decl(name.clone(), name.clone(), converted_ty, *bi);
                new_lctx.push_bvar(name.clone(), (**ty).clone());

                let body_u = {
                    let body_inst = body.instantiate(&fvar);
                    let mut tc = TypeChecker::with_local_ctx(self.st, new_lctx);
                    let body_type = tc.infer(&body_inst)?;
                    let body_level = tc.ensure_sort(&body_type)?;
                    tc.sort_level(&body_level)?
                };

                // Prop impredicativity: Pi(x:A).Prop : Prop
                let is_prop = body_u == Level::Zero || matches!(&**body, Expr::Sort(Level::Zero));
                if is_prop {
                    Ok(Expr::Sort(Level::Zero))
                } else {
                    Ok(Expr::Sort(Level::mk_max(ty_u, body_u)))
                }
            }
            Expr::Let(name, ty, value, body, _) => {
                let ty_type = self.infer(ty)?;
                self.ensure_sort(&ty_type)?;
                self.check(value, ty)?;

                let fvar = Expr::mk_fvar(name.clone());
                let mut new_lctx = self.lctx.clone();
                let converted_ty = new_lctx.replace_bvars_with_fvars(&ty);
                let converted_value = new_lctx.replace_bvars_with_fvars(&value);
                new_lctx.mk_let_decl(name.clone(), name.clone(), converted_ty, converted_value);
                new_lctx.push_bvar(name.clone(), (**ty).clone());

                let body_inst = body.instantiate(&fvar);
                let mut tc = TypeChecker::with_local_ctx(self.st, new_lctx);
                let result = tc.infer(&body_inst);
                result
            }
            Expr::Lit(lit) => {
                match lit {
                    Literal::Nat(_) => Ok(Expr::mk_const(Name::new("Nat"), vec![])),
                    Literal::String(_) => Ok(Expr::mk_const(Name::new("String"), vec![])),
                }
            }
            Expr::MData(_, e) => {
                self.infer(e)
            }
            Expr::Proj(_struct_name, _idx, e) => {
                let _e_type = self.infer(e)?;
                let _e_type_whnf = self.whnf(&_e_type);
                // Simplified: look up projection type from environment
                Err("Projection not fully implemented".to_string())
            }
        }?;

        self.st.infer_cache.insert(e.clone(), result.clone());
        Ok(result)
    }

    fn infer_app(&mut self, f: &Expr, a: &Expr) -> Result<Expr, String> {
        let f_type = self.infer(f)?;
        let f_type_whnf = self.whnf(&f_type);
        let pi = self.ensure_pi(&f_type_whnf)?;

        let domain = pi.binding_domain()
            .ok_or("Invalid Pi type")?
            .clone();
        let codomain = pi.binding_body()
            .ok_or("Invalid Pi type")?
            .clone();

        self.check(a, &domain)?;

        // Substitute bound variable 0 with a in codomain and normalize
        let result = codomain.instantiate(a);
        Ok(self.whnf(&result))
    }

    fn ensure_sort(&mut self, e: &Expr) -> Result<Expr, String> {
        let e_whnf = self.whnf(e);
        match e_whnf {
            Expr::Sort(_) => Ok(e_whnf),
            _ => Err(format!("Expected sort, got {}", self.expr_to_string(&e_whnf))),
        }
    }

    fn ensure_pi(&mut self, e: &Expr) -> Result<Expr, String> {
        let e_whnf = self.whnf(e);
        match e_whnf {
            Expr::Pi(_, _, _, _) => Ok(e_whnf),
            _ => Err(format!("Expected function type, got {}", self.expr_to_string(&e_whnf))),
        }
    }

    fn sort_level(&self, e: &Expr) -> Result<Level, String> {
        match e {
            Expr::Sort(l) => Ok(l.clone()),
            _ => Err("Expected Sort".to_string()),
        }
    }

    /// Check if an expression is a proposition (its type is Prop)
    fn is_prop(&mut self, e: &Expr) -> bool {
        if let Ok(ty) = self.infer(e) {
            let ty_whnf = self.whnf(&ty);
            if let Ok(sort) = self.ensure_sort(&ty_whnf) {
                if let Ok(lvl) = self.sort_level(&sort) {
                    return lvl.is_zero();
                }
            }
        }
        false
    }

    /// Quick check if an expression could be a proof term.
    /// Returns false for types (Sort, Pi) since they are not proofs.
    /// Follows Lean 4's isProofQuick pattern.
    fn is_proof_quick(&self, e: &Expr) -> bool {
        match e {
            Expr::Sort(_) => false,
            Expr::Pi(_, _, _, _) => false,
            Expr::Lambda(_, _, _, body) => self.is_proof_quick(body),
            Expr::Let(_, _, _, body, _) => self.is_proof_quick(body),
            Expr::MData(_, inner) => self.is_proof_quick(inner),
            _ => true,
        }
    }

    /// Check if an expression's type is Prop (i.e., Sort(0)).
    /// This checks if `e` is a proposition (inhabits Prop), NOT if `e` itself is Prop.
    /// Note: Prop itself is a universe (Type), not a proposition.
    fn is_prop_type(&mut self, e: &Expr) -> bool {
        // We only check if e's type is Prop.
        // We do NOT check if e itself is Sort(0), because Prop : Type, not Prop : Prop.
        if let Ok(ty) = self.infer(e) {
            let ty_whnf = self.whnf(&ty);
            if let Ok(sort) = self.ensure_sort(&ty_whnf) {
                if let Ok(lvl) = self.sort_level(&sort) {
                    return lvl.is_zero();
                }
            }
        }
        false
    }

    /// Weak head normal form
    pub fn whnf(&mut self, e: &Expr) -> Expr {
        // Check cache
        if let Some(result) = self.st.whnf_cache.get(e) {
            return result.clone();
        }

        let result = self.whnf_core(e);
        self.st.whnf_cache.insert(e.clone(), result.clone());
        result
    }

    fn whnf_core(&mut self, e: &Expr) -> Expr {
        match e {
            Expr::BVar(_) | Expr::Sort(_) | Expr::Pi(_, _, _, _) => {
                e.clone()
            }
            Expr::MVar(name) => {
                if let Some(val) = self.st.get_mvar_assignment(name).cloned() {
                    self.whnf_core(&val)
                } else {
                    e.clone()
                }
            }
            Expr::Lit(lit) => {
                match lit {
                    Literal::Nat(n) => Self::nat_lit_to_expr(*n),
                    _ => e.clone(),
                }
            }
            Expr::FVar(name) => {
                if let Some(value) = self.lctx.get_value(&Expr::FVar(name.clone())).cloned() {
                    self.whnf_core(&value)
                } else {
                    e.clone()
                }
            }
            Expr::Const(name, levels) => {
                if let Some(info) = self.st.env().find(name) {
                    if info.is_definition() || info.is_theorem() {
                        if let Some(val) = info.get_value(false) {
                            let instantiated = self.instantiate_univ_params(val, info.get_level_params(), levels);
                            return self.whnf_core(&instantiated);
                        }
                    }
                }
                e.clone()
            }
            Expr::App(f, a) => {
                let f_whnf = self.whnf_core(f);
                match f_whnf {
                    Expr::Lambda(_, _, _, body) => {
                        let reduced = body.instantiate(a);
                        self.whnf_core(&reduced)
                    }
                    _ => {
                        // Try recursor reduction
                        if let Some(reduced) = self.reduce_recursor(e) {
                            return self.whnf_core(&reduced);
                        }
                        // Try quotient reduction
                        if let Some(reduced) = self.reduce_quot(e) {
                            return self.whnf_core(&reduced);
                        }
                        Expr::App(Rc::new(f_whnf), a.clone())
                    }
                }
            }
            Expr::Let(_, _, value, body, _) => {
                let reduced = body.instantiate(value);
                self.whnf_core(&reduced)
            }
            Expr::MData(_, inner) => {
                self.whnf_core(inner)
            }
            Expr::Proj(_struct_name, idx, e) => {
                if let Some(reduced) = self.reduce_proj(e, *idx) {
                    return self.whnf_core(&reduced);
                }
                let e_whnf = self.whnf_core(e);
                Expr::Proj(_struct_name.clone(), *idx, Rc::new(e_whnf))
            }
            Expr::Lambda(_, _, _, _) => {
                e.clone()
            }
        }
    }

    fn nat_lit_to_expr(n: u64) -> Expr {
        let succ = Expr::mk_const(Name::new("succ"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let mut result = zero;
        for _ in 0..n {
            result = Expr::mk_app(succ.clone(), result);
        }
        result
    }

    fn reduce_recursor(&mut self, e: &Expr) -> Option<Expr> {
        let (fn_expr, rec_args) = e.get_app_args();
        let fn_expr = fn_expr?;

        if let Expr::Const(rec_name, rec_levels) = fn_expr {
            let info = self.st.env().find(rec_name)?;
            if !info.is_recursor() {
                return None;
            }

            let rec_val = info.to_recursor_val()?.clone();
            let lparams = info.get_level_params().clone();
            let major_idx = rec_val.get_major_idx() as usize;

            if rec_args.len() <= major_idx {
                return None;
            }

            let major = rec_args[major_idx];
            let major_whnf = self.whnf(major);

            // Find matching recursor rule
            let rule = rec_val.rules.iter().find(|r| self.is_constructor_app(&major_whnf, &r.ctor))?;

            // Instantiate universe parameters
            let mut rhs = if !lparams.is_empty() {
                self.instantiate_univ_params(&rule.rhs, &lparams, rec_levels)
            } else {
                rule.rhs.clone()
            };

            // Apply parameters + motives + minors
            let num_pmm = (rec_val.num_params + rec_val.num_motives + rec_val.num_minors) as usize;
            for i in 0..num_pmm {
                rhs = Expr::mk_app(rhs, rec_args[i].clone());
            }

            // Apply fields from major premise
            let (_, major_args) = major_whnf.get_app_args();
            let nparams = major_args.len() - rule.nfields as usize;
            for i in 0..rule.nfields as usize {
                rhs = Expr::mk_app(rhs, major_args[nparams + i].clone());
            }

            // Apply extra arguments after major premise
            if rec_args.len() > major_idx + 1 {
                for i in (major_idx + 1)..rec_args.len() {
                    rhs = Expr::mk_app(rhs, rec_args[i].clone());
                }
            }

            Some(rhs)
        } else {
            None
        }
    }

    fn is_constructor_app(&self, e: &Expr, ctor_name: &Name) -> bool {
        let fn_expr = e.get_app_fn();
        if let Expr::Const(name, _) = fn_expr {
            name == ctor_name
        } else {
            false
        }
    }

    fn reduce_proj(&mut self, e: &Expr, idx: u64) -> Option<Expr> {
        let e_whnf = self.whnf(e);
        let (mk_fn, args) = e_whnf.get_app_args();
        let mk_fn = mk_fn?;

        if let Expr::Const(ctor_name, _) = mk_fn {
            let ctor_info = self.st.env().find(ctor_name)?;
            if !ctor_info.is_constructor() {
                return None;
            }
            let ctor_val = ctor_info.to_constructor_val()?;
            let nparams = ctor_val.num_params as usize;
            let target_idx = nparams + idx as usize;
            if target_idx < args.len() {
                return Some(args[target_idx].clone());
            }
        }
        None
    }

    /// Infer the type of a quotient primitive constant.
    fn infer_quot_const(&mut self, name: &Name, levels: &[Level]) -> Result<Expr, String> {
        let prop = Expr::mk_prop();
        if name == &Name::new("Quot") {
            // Quot.{u} : (A : Sort u) -> (A -> A -> Prop) -> Sort u
            let u = levels.get(0).cloned().unwrap_or(Level::Param(Name::new("u")));
            let sort_u = Expr::mk_sort(u);
            let r_ty = Expr::mk_pi(Name::new("_"), Expr::mk_bvar(0),
                Expr::mk_pi(Name::new("_"), Expr::mk_bvar(1), prop.clone()));
            Ok(Expr::mk_pi(Name::new("A"), sort_u.clone(),
                Expr::mk_pi(Name::new("r"), r_ty, sort_u)))
        } else if name == &Name::new("Quot").extend("mk") {
            // Quot.mk.{u} : (A : Sort u) -> (r : A -> A -> Prop) -> A -> Quot A r
            let u = levels.get(0).cloned().unwrap_or(Level::Param(Name::new("u")));
            let sort_u = Expr::mk_sort(u.clone());
            let r_ty = Expr::mk_pi(Name::new("_"), Expr::mk_bvar(0),
                Expr::mk_pi(Name::new("_"), Expr::mk_bvar(1), prop.clone()));
            let quot_app = Expr::mk_app(
                Expr::mk_app(Expr::mk_const(Name::new("Quot"), vec![u]), Expr::mk_bvar(2)),
                Expr::mk_bvar(1));
            Ok(Expr::mk_pi(Name::new("A"), sort_u,
                Expr::mk_pi(Name::new("r"), r_ty,
                    Expr::mk_pi(Name::new("a"), Expr::mk_bvar(1), quot_app))))
        } else if name == &Name::new("Quot").extend("lift") {
            // Quot.lift.{u,v} : (A : Sort u) -> (r : A -> A -> Prop) -> (B : Sort v) ->
            //   (f : A -> B) -> (compat : forall a b, r a b -> B) -> Quot A r -> B
            let u = levels.get(0).cloned().unwrap_or(Level::Param(Name::new("u")));
            let v = levels.get(1).cloned().unwrap_or(Level::Param(Name::new("v")));
            let sort_u = Expr::mk_sort(u.clone());
            let sort_v = Expr::mk_sort(v);
            let r_ty = Expr::mk_pi(Name::new("_"), Expr::mk_bvar(0),
                Expr::mk_pi(Name::new("_"), Expr::mk_bvar(1), prop.clone()));
            let a_to_b = Expr::mk_arrow(Expr::mk_bvar(2), Expr::mk_bvar(1));
            // compat: forall a b, r a b -> Eq B (f a) (f b)
            let f_a = Expr::mk_app(Expr::mk_bvar(2), Expr::mk_bvar(1));
            let f_b = Expr::mk_app(Expr::mk_bvar(2), Expr::mk_bvar(0));
            let eq_app = Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_const(Name::new("Eq"), vec![]), Expr::mk_bvar(3)),
                    f_a),
                f_b);
            let compat_ty = Expr::mk_pi(Name::new("a"), Expr::mk_bvar(3),
                Expr::mk_pi(Name::new("b"), Expr::mk_bvar(4),
                    Expr::mk_pi(Name::new("_"),
                        Expr::mk_app(Expr::mk_app(Expr::mk_bvar(4), Expr::mk_bvar(1)), Expr::mk_bvar(0)),
                        eq_app)));
            let quot_app = Expr::mk_app(
                Expr::mk_app(Expr::mk_const(Name::new("Quot"), vec![u]), Expr::mk_bvar(4)),
                Expr::mk_bvar(3));
            let ret_ty = Expr::mk_bvar(2);
            Ok(Expr::mk_pi(Name::new("A"), sort_u,
                Expr::mk_pi(Name::new("r"), r_ty,
                    Expr::mk_pi(Name::new("B"), sort_v,
                        Expr::mk_pi(Name::new("f"), a_to_b,
                            Expr::mk_pi(Name::new("compat"), compat_ty,
                                Expr::mk_pi(Name::new("q"), quot_app, ret_ty)))))))
        } else if name == &Name::new("Quot").extend("ind") {
            // Quot.ind.{u} : (A : Sort u) -> (r : A -> A -> Prop) ->
            //   (B : Quot A r -> Prop) -> (h : forall a, B (Quot.mk A r a)) ->
            //   (q : Quot A r) -> B q
            let u = levels.get(0).cloned().unwrap_or(Level::Param(Name::new("u")));
            let sort_u = Expr::mk_sort(u.clone());
            let r_ty = Expr::mk_pi(Name::new("_"), Expr::mk_bvar(0),
                Expr::mk_pi(Name::new("_"), Expr::mk_bvar(1), prop.clone()));
            let b_ty = Expr::mk_arrow(
                Expr::mk_app(Expr::mk_app(Expr::mk_const(Name::new("Quot"), vec![u.clone()]), Expr::mk_bvar(1)), Expr::mk_bvar(0)),
                prop.clone());
            let h_ty = Expr::mk_pi(Name::new("a"), Expr::mk_bvar(2),
                Expr::mk_app(Expr::mk_bvar(1),
                    Expr::mk_app(
                        Expr::mk_app(Expr::mk_app(Expr::mk_const(Name::new("Quot").extend("mk"), vec![u.clone()]), Expr::mk_bvar(3)), Expr::mk_bvar(2)),
                        Expr::mk_bvar(0))));
            let quot_app = Expr::mk_app(
                Expr::mk_app(Expr::mk_const(Name::new("Quot"), vec![u]), Expr::mk_bvar(3)),
                Expr::mk_bvar(2));
            let ret_ty = Expr::mk_app(Expr::mk_bvar(2), Expr::mk_bvar(0));
            Ok(Expr::mk_pi(Name::new("A"), sort_u,
                Expr::mk_pi(Name::new("r"), r_ty,
                    Expr::mk_pi(Name::new("B"), b_ty,
                        Expr::mk_pi(Name::new("h"), h_ty,
                            Expr::mk_pi(Name::new("q"), quot_app, ret_ty))))))
        } else if name == &Name::new("Quot").extend("sound") {
            // Quot.sound.{u} : (A : Sort u) -> (r : A -> A -> Prop) -> (a : A) -> (b : A) ->
            //   r a b -> Eq (Quot A r) (Quot.mk A r a) (Quot.mk A r b)
            let u = levels.get(0).cloned().unwrap_or(Level::Param(Name::new("u")));
            let sort_u = Expr::mk_sort(u.clone());
            let r_ty = Expr::mk_pi(Name::new("_"), Expr::mk_bvar(0),
                Expr::mk_pi(Name::new("_"), Expr::mk_bvar(1), prop.clone()));
            let h_ty = Expr::mk_app(
                Expr::mk_app(Expr::mk_bvar(2), Expr::mk_bvar(1)),
                Expr::mk_bvar(0));
            let quot_app = Expr::mk_app(
                Expr::mk_app(Expr::mk_const(Name::new("Quot"), vec![u.clone()]), Expr::mk_bvar(4)),
                Expr::mk_bvar(3));
            let mk_a = Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_const(Name::new("Quot").extend("mk"), vec![u.clone()]), Expr::mk_bvar(4)),
                    Expr::mk_bvar(3)),
                Expr::mk_bvar(2));
            let mk_b = Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_const(Name::new("Quot").extend("mk"), vec![u.clone()]), Expr::mk_bvar(4)),
                    Expr::mk_bvar(3)),
                Expr::mk_bvar(1));
            let eq_app = Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_const(Name::new("Eq"), vec![]), quot_app),
                    mk_a),
                mk_b);
            Ok(Expr::mk_pi(Name::new("A"), sort_u,
                Expr::mk_pi(Name::new("r"), r_ty,
                    Expr::mk_pi(Name::new("a"), Expr::mk_bvar(1),
                        Expr::mk_pi(Name::new("b"), Expr::mk_bvar(2),
                            Expr::mk_pi(Name::new("_"), h_ty, eq_app))))))
        } else {
            Err(format!("Unknown quot constant: {}", name.to_string()))
        }
    }

    /// Reduce quotient primitive applications.
    fn reduce_quot(&mut self, e: &Expr) -> Option<Expr> {
        let (fn_expr, args) = e.get_app_args();
        let fn_expr = fn_expr?;

        if let Expr::Const(name, _) = fn_expr {
            if name == &Name::new("Quot").extend("lift") {
                // Quot.lift A r B f compat q
                if args.len() >= 6 {
                    let q = args[5];
                    let q_whnf = self.whnf(q);
                    let (q_fn, q_args) = q_whnf.get_app_args();
                    if let Some(Expr::Const(q_name, _)) = q_fn {
                        if q_name == &Name::new("Quot").extend("mk") && q_args.len() >= 3 {
                            let a = q_args[2];
                            let f = args[3];
                            return Some(Expr::mk_app(f.clone(), a.clone()));
                        }
                    }
                }
            } else if name == &Name::new("Quot").extend("ind") {
                // Quot.ind A r B h q
                if args.len() >= 5 {
                    let q = args[4];
                    let q_whnf = self.whnf(q);
                    let (q_fn, q_args) = q_whnf.get_app_args();
                    if let Some(Expr::Const(q_name, _)) = q_fn {
                        if q_name == &Name::new("Quot").extend("mk") && q_args.len() >= 3 {
                            let a = q_args[2];
                            let h = args[3];
                            return Some(Expr::mk_app(h.clone(), a.clone()));
                        }
                    }
                }
            }
        }
        None
    }

    /// Check definitional equality
    pub fn is_def_eq(&mut self, t: &Expr, s: &Expr) -> bool {
        // Quick checks
        if t == s {
            return true;
        }

        // Check failure cache
        let pair = ExprPair(t.clone(), s.clone());
        if self.st.failure_cache.contains_key(&pair) {
            return false;
        }

        let t_n = self.whnf(t);
        let s_n = self.whnf(s);

        // Metavariable unification
        if let Expr::MVar(name) = &t_n {
            if self.try_assign_mvar(name, &s_n) {
                return true;
            }
        }
        if let Expr::MVar(name) = &s_n {
            if self.try_assign_mvar(name, &t_n) {
                return true;
            }
        }

        // Try is_def_eq_core first
        let result = self.is_def_eq_core(&t_n, &s_n);
        if result {
            return true;
        }

        // Proof irrelevance: any two terms of the same Prop type are defeq
        // A type is a proposition if it is Sort(0), i.e., Prop
        // Only apply to actual proof terms, not to types themselves (Sort/Pi)
        if self.is_proof_quick(t) && self.is_proof_quick(s) {
            if let (Ok(t_ty), Ok(s_ty)) = (self.infer(t), self.infer(s)) {
                let t_is_prop = self.is_prop_type(&t_ty);
                let s_is_prop = self.is_prop_type(&s_ty);
                if t_is_prop && s_is_prop && self.is_def_eq(&t_ty, &s_ty) {
                    return true;
                }
            }
        }

        self.st.failure_cache.insert(pair, false);
        false
    }

    fn is_def_eq_core(&mut self, t: &Expr, s: &Expr) -> bool {
        if t == s {
            return true;
        }

        match (t, s) {
            (Expr::Sort(l1), Expr::Sort(l2)) => {
                self.is_def_eq_levels(l1, l2)
            }
            (Expr::Const(n1, ls1), Expr::Const(n2, ls2)) => {
                if n1 != n2 {
                    return false;
                }
                let max_len = std::cmp::max(ls1.len(), ls2.len());
                for i in 0..max_len {
                    let l1 = ls1.get(i).cloned().unwrap_or(Level::MVar(Name::new(&format!("_ul_{}", i))));
                    let l2 = ls2.get(i).cloned().unwrap_or(Level::MVar(Name::new(&format!("_ur_{}", i))));
                    if !self.is_def_eq_levels(&l1, &l2) {
                        return false;
                    }
                }
                true
            }
            (Expr::FVar(n1), Expr::FVar(n2)) => {
                n1 == n2
            }
            (Expr::App(tf, ta), Expr::App(sf, sa)) => {
                self.is_def_eq(tf, sf) && self.is_def_eq(ta, sa)
            }
            (Expr::Lambda(_, bi1, tty1, tbody1), Expr::Lambda(_, bi2, sty1, sbody1)) |
            (Expr::Pi(_, bi1, tty1, tbody1), Expr::Pi(_, bi2, sty1, sbody1)) => {
                if bi1 != bi2 {
                    return false;
                }
                if !self.is_def_eq(tty1, sty1) {
                    return false;
                }
                // Use a single fresh variable for both sides (standard approach)
                let fresh_name = Name::new(&format!("_fresh_{}", self.lctx.len()));
                let fresh = Expr::mk_fvar(fresh_name.clone());
                let converted_ty = self.lctx.replace_bvars_with_fvars(tty1);
                let fresh_decl = self.lctx.mk_local_decl(fresh_name.clone(), fresh_name.clone(), converted_ty, *bi1);
                self.lctx.push_bvar(fresh_name.clone(), (**tty1).clone());

                let t_body_inst = tbody1.instantiate(&fresh);
                let s_body_inst = sbody1.instantiate(&fresh);
                let result = self.is_def_eq(&t_body_inst, &s_body_inst);

                self.lctx.clear(&fresh_decl);
                self.lctx.pop_bvar();
                result
            }
            (Expr::Lit(l1), Expr::Lit(l2)) => {
                l1 == l2
            }
            _ => {
                // Try eta expansion
                if self.try_eta_expansion(t, s) || self.try_eta_expansion(s, t) {
                    return true;
                }
                // Try structure eta
                if let Some(result) = self.try_struct_eta(t, s) {
                    return result;
                }
                if let Some(result) = self.try_struct_eta(s, t) {
                    return result;
                }
                false
            }
        }
    }

    /// Try to assign a metavariable to a value.
    /// Returns true if assignment succeeds or the metavariable is already assigned
    /// to a definitionally equal value.
    fn try_assign_mvar(&mut self, name: &Name, val: &Expr) -> bool {
        // If already assigned, check definitional equality with assigned value
        if let Some(assigned) = self.st.get_mvar_assignment(name).cloned() {
            return self.is_def_eq(&assigned, val);
        }
        // Occur check: avoid cyclic assignments
        if val.has_mvar_named(name) {
            return false;
        }
        // Perform assignment
        self.st.assign_mvar(name, val.clone())
    }

    /// Check if two universe levels are definitionally equal, using constraint solving for params.
    fn is_def_eq_levels(&mut self, l1: &Level, l2: &Level) -> bool {
        let n1 = l1.normalize();
        let n2 = l2.normalize();
        if n1.is_equivalent(&n2) {
            return true;
        }
        // Try to unify level parameters
        match (&n1, &n2) {
            (Level::Param(p), _) => {
                if let Some(subst) = self.st.get_level_subst(p).cloned() {
                    self.is_def_eq_levels(&subst, &n2)
                } else {
                    self.st.assign_level_param(p, n2.clone())
                }
            }
            (_, Level::Param(p)) => {
                if let Some(subst) = self.st.get_level_subst(p).cloned() {
                    self.is_def_eq_levels(&n1, &subst)
                } else {
                    self.st.assign_level_param(p, n1.clone())
                }
            }
            (Level::MVar(p), _) => {
                if let Some(subst) = self.st.get_level_subst(p).cloned() {
                    self.is_def_eq_levels(&subst, &n2)
                } else {
                    self.st.assign_level_param(p, n2.clone())
                }
            }
            (_, Level::MVar(p)) => {
                if let Some(subst) = self.st.get_level_subst(p).cloned() {
                    self.is_def_eq_levels(&n1, &subst)
                } else {
                    self.st.assign_level_param(p, n1.clone())
                }
            }
            // Max/Max matching: try both permutations
            (Level::Max(a1, b1), Level::Max(a2, b2)) => {
                (self.is_def_eq_levels(a1, a2) && self.is_def_eq_levels(b1, b2))
                    || (self.is_def_eq_levels(a1, b2) && self.is_def_eq_levels(b1, a2))
            }
            // IMax/IMax matching
            (Level::IMax(a1, b1), Level::IMax(a2, b2)) => {
                // IMax(a, b) = if b = 0 then 0 else Max(a, b)
                // Try direct matching first
                if self.is_def_eq_levels(a1, a2) && self.is_def_eq_levels(b1, b2) {
                    return true;
                }
                // Handle special case: IMax(a, 0) = 0 = IMax(b, 0)
                if b1.is_zero() && b2.is_zero() {
                    return true;
                }
                false
            }
            // Max with Succ: try to match one branch
            (Level::Max(a, b), Level::Succ(s)) | (Level::Succ(s), Level::Max(a, b)) => {
                (self.is_def_eq_levels(a, &Level::Succ(s.clone())) && self.is_level_leq(b, &Level::Succ(s.clone())))
                    || (self.is_def_eq_levels(b, &Level::Succ(s.clone())) && self.is_level_leq(a, &Level::Succ(s.clone())))
            }
            // IMax with Zero: IMax(a, 0) = 0
            (Level::IMax(_, b), Level::Zero) | (Level::Zero, Level::IMax(_, b)) => {
                b.is_zero()
            }
            // IMax with Succ/Param: IMax(a, b) = Max(a, b) when b != 0
            (Level::IMax(a, b), other) | (other, Level::IMax(a, b)) => {
                if !b.is_zero() {
                    self.is_def_eq_levels(&Level::Max(a.clone(), b.clone()), other)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// Check if level l1 <= l2 (structural subsumption)
    fn is_level_leq(&mut self, l1: &Level, l2: &Level) -> bool {
        let n1 = l1.normalize();
        let n2 = l2.normalize();
        if n1.is_equivalent(&n2) {
            return true;
        }
        match (&n1, &n2) {
            (Level::Zero, _) => true,
            (_, Level::Zero) => false,
            (Level::Succ(s1), Level::Succ(s2)) => self.is_level_leq(s1, s2),
            (a, Level::Max(b, c)) => self.is_level_leq(a, b) || self.is_level_leq(a, c),
            (Level::Max(a, b), c) => self.is_level_leq(a, c) && self.is_level_leq(b, c),
            (a, Level::IMax(b, c)) => {
                if c.is_zero() {
                    a.is_zero()
                } else {
                    self.is_level_leq(a, b) || self.is_level_leq(a, c)
                }
            }
            (Level::Param(p), _) => {
                if let Some(subst) = self.st.get_level_subst(p).cloned() {
                    self.is_level_leq(&subst, &n2)
                } else {
                    // Try to assign p = l2 if l2 is simpler
                    self.st.assign_level_param(p, n2.clone())
                }
            }
            (_, Level::Param(p)) => {
                if let Some(subst) = self.st.get_level_subst(p).cloned() {
                    self.is_level_leq(&n1, &subst)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn try_eta_expansion(&mut self, t: &Expr, s: &Expr) -> bool {
        // Eta expansion: (λ x. f x) = f  when x not free in f
        if let Expr::Lambda(_, _, _, body) = t {
            if let Expr::App(f, a) = body.as_ref() {
                if let Expr::BVar(0) = a.as_ref() {
                    // Check if body is f applied to bound var 0
                    // And f doesn't contain bound var 0
                    if !f.has_loose_bvar(0) {
                        let f_lifted = f.lift_loose_bvars(1, 0);
                        return self.is_def_eq(&f_lifted, s);
                    }
                }
            }
        }
        false
    }

    /// Structure eta: if t has a structure type and s is the constructor application
    /// with projections of t, then t = s.
    fn try_struct_eta(&mut self, t: &Expr, s: &Expr) -> Option<bool> {
        // Check if s is a constructor application
        let (ctor_fn, s_args) = s.get_app_args();
        let ctor_name = ctor_fn?.const_name()?.clone();

        // Collect constructor info in a scoped block so env borrows are dropped
        let (ind_name, num_fields, num_params) = {
            let ctor_info = self.st.env().find(&ctor_name)?;
            if !ctor_info.is_constructor() {
                return None;
            }
            let ctor_val = ctor_info.to_constructor_val()?;
            let ind_name = ctor_val.induct.clone();
            let num_fields = ctor_val.num_fields as usize;
            let num_params = ctor_val.num_params as usize;

            let ind_info = self.st.env().find(&ind_name)?;
            let ind_val = ind_info.to_inductive_val()?;
            if ind_val.ctors.len() != 1 {
                return None;
            }
            (ind_name, num_fields, num_params)
        };

        // Check if t's type matches the inductive type
        let t_ty = self.infer(t).ok()?;
        let t_ty_head = t_ty.get_app_fn();
        let t_ty_name = t_ty_head.const_name()?;
        if *t_ty_name != ind_name {
            return None;
        }

        // Build eta-expanded form: mk (Proj t 0) (Proj t 1) ...
        let mut eta = Expr::mk_const(ctor_name, vec![]);

        // Apply params from s
        for i in 0..num_params {
            if i < s_args.len() {
                eta = Expr::mk_app(eta, s_args[i].clone());
            }
        }

        // Apply projections of t
        for i in 0..num_fields {
            let proj = Expr::Proj(ind_name.clone(), i as u64, Rc::new(t.clone()));
            eta = Expr::mk_app(eta, proj);
        }

        Some(self.is_def_eq(&eta, s))
    }

    /// Full normalization: recursively reduce to normal form
    pub fn nf(&mut self, e: &Expr) -> Expr {
        let e_whnf = self.whnf(e);
        match e_whnf {
            Expr::App(f, a) => {
                let f_nf = self.nf(&f);
                let a_nf = self.nf(&a);
                Expr::App(Rc::new(f_nf), Rc::new(a_nf))
            }
            Expr::Lambda(name, bi, ty, body) => {
                let ty_nf = self.nf(&ty);
                let body_nf = self.nf(&body);
                Expr::Lambda(name, bi, Rc::new(ty_nf), Rc::new(body_nf))
            }
            Expr::Pi(name, bi, ty, body) => {
                let ty_nf = self.nf(&ty);
                let body_nf = self.nf(&body);
                Expr::Pi(name, bi, Rc::new(ty_nf), Rc::new(body_nf))
            }
            Expr::Let(name, ty, value, body, nondep) => {
                let ty_nf = self.nf(&ty);
                let value_nf = self.nf(&value);
                let body_nf = self.nf(&body);
                Expr::Let(name, Rc::new(ty_nf), Rc::new(value_nf), Rc::new(body_nf), nondep)
            }
            Expr::Proj(s, i, e) => {
                let e_nf = self.nf(&e);
                Expr::Proj(s, i, Rc::new(e_nf))
            }
            Expr::MData(d, e) => {
                let e_nf = self.nf(&e);
                Expr::MData(d, Rc::new(e_nf))
            }
            other => other,
        }
    }

    fn instantiate_univ_params(&self, e: &Expr, params: &[Name], levels: &[Level]) -> Expr {
        if params.is_empty() && self.st.level_subst.is_empty() {
            return e.clone();
        }
        let mut subst: HashMap<Name, Level> = params.iter().cloned().zip(levels.iter().cloned()).collect();
        // Also include recorded level substitutions from constraint solving
        for (name, level) in &self.st.level_subst {
            subst.insert(name.clone(), level.clone());
        }
        self.replace_levels(e, &subst)
    }

    fn replace_levels(&self, e: &Expr, subst: &HashMap<Name, Level>) -> Expr {
        match e {
            Expr::Sort(l) => Expr::Sort(self.replace_level_in_level(l, subst)),
            Expr::Const(name, levels) => {
                let new_levels: Vec<Level> = levels.iter()
                    .map(|l| self.replace_level_in_level(l, subst))
                    .collect();
                Expr::Const(name.clone(), new_levels)
            }
            Expr::App(f, a) => {
                Expr::App(
                    Rc::new(self.replace_levels(f, subst)),
                    Rc::new(self.replace_levels(a, subst)),
                )
            }
            Expr::Lambda(name, bi, ty, body) => {
                Expr::Lambda(
                    name.clone(),
                    *bi,
                    Rc::new(self.replace_levels(ty, subst)),
                    Rc::new(self.replace_levels(body, subst)),
                )
            }
            Expr::Pi(name, bi, ty, body) => {
                Expr::Pi(
                    name.clone(),
                    *bi,
                    Rc::new(self.replace_levels(ty, subst)),
                    Rc::new(self.replace_levels(body, subst)),
                )
            }
            Expr::Let(name, ty, value, body, nondep) => {
                Expr::Let(
                    name.clone(),
                    Rc::new(self.replace_levels(ty, subst)),
                    Rc::new(self.replace_levels(value, subst)),
                    Rc::new(self.replace_levels(body, subst)),
                    *nondep,
                )
            }
            Expr::MData(d, inner) => {
                Expr::MData(d.clone(), Rc::new(self.replace_levels(inner, subst)))
            }
            Expr::Proj(s, i, inner) => {
                Expr::Proj(s.clone(), *i, Rc::new(self.replace_levels(inner, subst)))
            }
            other => other.clone(),
        }
    }

    fn replace_level_in_level(&self, level: &Level, subst: &HashMap<Name, Level>) -> Level {
        match level {
            Level::Param(name) | Level::MVar(name) => {
                subst.get(name).cloned().unwrap_or_else(|| level.clone())
            }
            Level::Succ(l) => Level::mk_succ(self.replace_level_in_level(l, subst)),
            Level::Max(l1, l2) => {
                Level::mk_max(
                    self.replace_level_in_level(l1, subst),
                    self.replace_level_in_level(l2, subst),
                )
            }
            Level::IMax(l1, l2) => {
                Level::mk_imax(
                    self.replace_level_in_level(l1, subst),
                    self.replace_level_in_level(l2, subst),
                )
            }
            Level::Zero => Level::Zero,
        }
    }

    fn expr_to_string(&self, e: &Expr) -> String {
        // Simplified expression printer
        format!("{:?}", e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk_env_with_nat() -> Environment {
        let mut env = Environment::new();
        // Add Nat : Type 0
        let nat_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("Nat"),
                level_params: vec![],
                ty: Expr::mk_type(),
            },
            is_unsafe: false,
        });
        env.add(nat_decl).unwrap();
        // Add zero : Nat
        let zero_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("zero"),
                level_params: vec![],
                ty: Expr::mk_const(Name::new("Nat"), vec![]),
            },
            is_unsafe: false,
        });
        env.add(zero_decl).unwrap();
        env
    }

    #[test]
    fn test_infer_sort() {
        let env = Environment::new();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);
        let sort0 = Expr::Sort(Level::Zero);
        let ty = tc.infer(&sort0).unwrap();
        // Sort u : Sort (u+1)
        assert_eq!(ty, Expr::Sort(Level::mk_succ(Level::Zero)));
    }

    #[test]
    fn test_infer_const() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let ty = tc.infer(&nat).unwrap();
        assert_eq!(ty, Expr::mk_type());
    }

    #[test]
    fn test_infer_lambda() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);
        // λ (x : Nat). x
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let body = Expr::BVar(0);
        let lam = Expr::Lambda(
            Name::new("x"),
            BinderInfo::Default,
            Rc::new(nat.clone()),
            Rc::new(body),
        );
        let ty = tc.infer(&lam).unwrap();
        // Should be Nat -> Nat
        match ty {
            Expr::Pi(_, _, domain, codomain) => {
                assert_eq!(domain.as_ref(), &nat);
                assert_eq!(codomain.as_ref(), &nat);
            }
            _ => panic!("Expected Pi, got {:?}", ty),
        }
    }

    #[test]
    fn test_infer_app() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);
        // (λ (x : Nat). x) zero
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let body = Expr::BVar(0);
        let lam = Expr::Lambda(
            Name::new("x"),
            BinderInfo::Default,
            Rc::new(nat.clone()),
            Rc::new(body),
        );
        let app = Expr::mk_app(lam, zero.clone());
        let ty = tc.infer(&app).unwrap();
        assert_eq!(ty, nat);
    }

    #[test]
    fn test_whnf_beta() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);
        // (λ (x : Nat). x) Nat  ~>  Nat
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let body = Expr::BVar(0);
        let lam = Expr::Lambda(
            Name::new("x"),
            BinderInfo::Default,
            Rc::new(nat.clone()),
            Rc::new(body),
        );
        let app = Expr::mk_app(lam, nat.clone());
        let result = tc.whnf(&app);
        assert_eq!(result, nat);
    }

    #[test]
    fn test_is_def_eq_refl() {
        let env = Environment::new();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);
        let a = Expr::mk_const(Name::new("A"), vec![]);
        assert!(tc.is_def_eq(&a, &a));
    }

    #[test]
    fn test_is_def_eq_eta() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);
        // λ (x : Nat). f x = f  (eta)
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let f = Expr::mk_const(Name::new("f"), vec![]);
        let f_app = Expr::mk_app(f.clone(), Expr::BVar(0));
        let lam = Expr::Lambda(
            Name::new("x"),
            BinderInfo::Default,
            Rc::new(nat.clone()),
            Rc::new(f_app),
        );
        // Need to lift f because it has no loose bvars
        assert!(tc.is_def_eq(&lam, &f));
    }

    #[test]
    fn test_instantiate_univ_params() {
        let env = Environment::new();
        let mut st = TypeCheckerState::new(env);
        let tc = TypeChecker::new(&mut st);
        let u = Name::new("u");
        let sort_u = Expr::Sort(Level::Param(u.clone()));
        let sort_zero = Expr::Sort(Level::Zero);
        let result = tc.instantiate_univ_params(&sort_u, &[u], &[Level::Zero]);
        assert_eq!(result, sort_zero);
    }

    fn mk_env_with_bool() -> Environment {
        let mut env = Environment::new();

        // Bool : Type 0
        let bool_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("Bool"),
                level_params: vec![],
                ty: Expr::mk_type(),
            },
            is_unsafe: false,
        });
        env.add(bool_decl).unwrap();

        // false : Bool
        let false_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("false"),
                level_params: vec![],
                ty: Expr::mk_const(Name::new("Bool"), vec![]),
            },
            is_unsafe: false,
        });
        env.add(false_decl).unwrap();

        // true : Bool
        let true_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("true"),
                level_params: vec![],
                ty: Expr::mk_const(Name::new("Bool"), vec![]),
            },
            is_unsafe: false,
        });
        env.add(true_decl).unwrap();

        // Bool.rec : (P : Bool -> Type 0) -> P false -> P true -> (b : Bool) -> P b
        // false rule: λ P. λ pf. λ pt. pf   =  BVar(1) wrapped in 3 lambdas
        // true rule:  λ P. λ pf. λ pt. pt   =  BVar(0) wrapped in 3 lambdas
        let bool_ty = Expr::mk_const(Name::new("Bool"), vec![]);
        let prop = Expr::mk_prop();
        let p_ty = Expr::mk_pi(Name::new("b"), bool_ty.clone(), prop.clone());

        let false_rule_rhs = Expr::Lambda(
            Name::new("P"), BinderInfo::Default, Rc::new(p_ty.clone()),
            Rc::new(Expr::Lambda(
                Name::new("pf"), BinderInfo::Default, Rc::new(Expr::mk_app(Expr::BVar(0), Expr::mk_const(Name::new("false"), vec![]))),
                Rc::new(Expr::Lambda(
                    Name::new("pt"), BinderInfo::Default, Rc::new(Expr::mk_app(Expr::BVar(1), Expr::mk_const(Name::new("true"), vec![]))),
                    Rc::new(Expr::BVar(1))
                ))
            ))
        );

        let true_rule_rhs = Expr::Lambda(
            Name::new("P"), BinderInfo::Default, Rc::new(p_ty.clone()),
            Rc::new(Expr::Lambda(
                Name::new("pf"), BinderInfo::Default, Rc::new(Expr::mk_app(Expr::BVar(0), Expr::mk_const(Name::new("false"), vec![]))),
                Rc::new(Expr::Lambda(
                    Name::new("pt"), BinderInfo::Default, Rc::new(Expr::mk_app(Expr::BVar(1), Expr::mk_const(Name::new("true"), vec![]))),
                    Rc::new(Expr::BVar(0))
                ))
            ))
        );

        let rec_val = RecursorVal {
            constant_val: ConstantVal {
                name: Name::new("rec").extend("Bool"),
                level_params: vec![],
                ty: bool_ty.clone(), // simplified
            },
            all: vec![Name::new("Bool")],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 2,
            rules: vec![
                RecursorRule { ctor: Name::new("false"), nfields: 0, rhs: false_rule_rhs },
                RecursorRule { ctor: Name::new("true"), nfields: 0, rhs: true_rule_rhs },
            ],
            k: true,
            is_unsafe: false,
        };
        env.insert_constant(
            Name::new("rec").extend("Bool"),
            ConstantInfo::RecursorInfo(rec_val),
        );

        env
    }

    #[test]
    fn test_reduce_recursor_bool() {
        let env = mk_env_with_bool();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let bool_rec = Expr::mk_const(Name::new("rec").extend("Bool"), vec![]);
        let false_ctor = Expr::mk_const(Name::new("false"), vec![]);
        let true_ctor = Expr::mk_const(Name::new("true"), vec![]);

        // Bool.rec (λ b. Nat) zero succ false  ~>  zero
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let succ = Expr::mk_const(Name::new("succ"), vec![]);
        let motive = Expr::mk_lambda(Name::new("b"), bool_ty(), nat.clone());
        let app_false = Expr::mk_app(Expr::mk_app(Expr::mk_app(Expr::mk_app(bool_rec.clone(), motive.clone()), zero.clone()), succ.clone()), false_ctor.clone());
        let result = tc.whnf(&app_false);
        assert_eq!(result, zero);

        // Bool.rec (λ b. Nat) zero succ true  ~>  succ
        let app_true = Expr::mk_app(Expr::mk_app(Expr::mk_app(Expr::mk_app(bool_rec, motive), zero.clone()), succ.clone()), true_ctor);
        let result = tc.whnf(&app_true);
        assert_eq!(result, succ);
    }

    fn bool_ty() -> Expr {
        Expr::mk_const(Name::new("Bool"), vec![])
    }

    #[test]
    fn test_reduce_projection() {
        let mut env = Environment::new();
        // Pair : Type 0 -> Type 0 -> Type 0
        let pair_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("Pair"),
                level_params: vec![],
                ty: Expr::mk_arrow(Expr::mk_type(), Expr::mk_arrow(Expr::mk_type(), Expr::mk_type())),
            },
            is_unsafe: false,
        });
        env.add(pair_decl).unwrap();

        // Pair.mk : (A B : Type 0) -> A -> B -> Pair A B
        let pair_mk_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("Pair").extend("mk"),
                level_params: vec![],
                ty: {
                    let a = Expr::mk_const(Name::new("A"), vec![]);
                    let b = Expr::mk_const(Name::new("B"), vec![]);
                    Expr::mk_pi(Name::new("A"), Expr::mk_type(),
                        Expr::mk_pi(Name::new("B"), Expr::mk_type(),
                            Expr::mk_arrow(a.clone(),
                                Expr::mk_arrow(b.clone(),
                                    Expr::mk_app(Expr::mk_app(Expr::mk_const(Name::new("Pair"), vec![]), a), b)))))
                },
            },
            is_unsafe: false,
        });
        env.add(pair_mk_decl).unwrap();

        // Mark Pair.mk as constructor
        let ctor_val = ConstructorVal {
            constant_val: ConstantVal {
                name: Name::new("Pair").extend("mk"),
                level_params: vec![],
                ty: Expr::mk_type(),
            },
            induct: Name::new("Pair"),
            cidx: 0,
            num_params: 2,
            num_fields: 2,
            is_unsafe: false,
        };
        env.insert_constant(
            Name::new("Pair").extend("mk"),
            ConstantInfo::ConstructorInfo(ctor_val),
        );

        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let a = Expr::mk_const(Name::new("a"), vec![]);
        let b = Expr::mk_const(Name::new("b"), vec![]);
        let pair_mk = Expr::mk_const(Name::new("Pair").extend("mk"), vec![]);
        let pair_ab = Expr::mk_app(Expr::mk_app(Expr::mk_app(Expr::mk_app(pair_mk, Expr::mk_type()), Expr::mk_type()), a.clone()), b.clone());

        // Proj(Pair, 0, Pair.mk Type Type a b) ~> a
        let proj0 = Expr::Proj(Name::new("Pair"), 0, Rc::new(pair_ab.clone()));
        let result = tc.whnf(&proj0);
        assert_eq!(result, a);

        // Proj(Pair, 1, Pair.mk Type Type a b) ~> b
        let proj1 = Expr::Proj(Name::new("Pair"), 1, Rc::new(pair_ab));
        let result = tc.whnf(&proj1);
        assert_eq!(result, b);
    }

    fn mk_env_with_nat_rec() -> Environment {
        let mut env = mk_env_with_nat();

        // Also add succ : Nat -> Nat
        let succ_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("succ"),
                level_params: vec![],
                ty: Expr::mk_arrow(Expr::mk_const(Name::new("Nat"), vec![]), Expr::mk_const(Name::new("Nat"), vec![])),
            },
            is_unsafe: false,
        });
        env.add(succ_decl).unwrap();

        // Nat.rec
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let u = Name::new("u");
        let sort_u = Expr::Sort(Level::Param(u.clone()));

        // P : Nat -> Sort u
        let p_ty = Expr::mk_pi(Name::new("n"), nat.clone(), sort_u.clone());

        // zero rule: λ P. λ z. λ s. z  -> body = BVar(1)
        let zero_rule_rhs = Expr::Lambda(
            Name::new("P"), BinderInfo::Default, Rc::new(p_ty.clone()),
            Rc::new(Expr::Lambda(
                Name::new("z"), BinderInfo::Default, Rc::new(Expr::mk_app(Expr::BVar(0), Expr::mk_const(Name::new("zero"), vec![]))),
                Rc::new(Expr::Lambda(
                    Name::new("s"), BinderInfo::Default, Rc::new(Expr::mk_pi(Name::new("n"), nat.clone(), Expr::mk_pi(Name::new("ih"), Expr::mk_app(Expr::BVar(2), Expr::BVar(0)), Expr::mk_app(Expr::BVar(3), Expr::mk_app(Expr::mk_const(Name::new("succ"), vec![]), Expr::BVar(1)))))),
                    Rc::new(Expr::BVar(1))
                ))
            ))
        );

        // succ rule: λ P. λ z. λ s. λ n. s n (Nat.rec P z s n)
        // In body: n = BVar(0), s = BVar(1), z = BVar(2), P = BVar(3)
        let nat_rec_const = Expr::mk_const(Name::new("rec").extend("Nat"), vec![Level::Param(u.clone())]);
        let rec_call = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(nat_rec_const.clone(), Expr::BVar(3)),
                    Expr::BVar(2)
                ),
                Expr::BVar(1)
            ),
            Expr::BVar(0)
        );
        let succ_body = Expr::mk_app(
            Expr::mk_app(Expr::BVar(1), Expr::BVar(0)),
            rec_call
        );
        let succ_rule_rhs = Expr::Lambda(
            Name::new("P"), BinderInfo::Default, Rc::new(p_ty.clone()),
            Rc::new(Expr::Lambda(
                Name::new("z"), BinderInfo::Default, Rc::new(Expr::mk_app(Expr::BVar(0), Expr::mk_const(Name::new("zero"), vec![]))),
                Rc::new(Expr::Lambda(
                    Name::new("s"), BinderInfo::Default, Rc::new(Expr::mk_pi(Name::new("n"), nat.clone(), Expr::mk_pi(Name::new("ih"), Expr::mk_app(Expr::BVar(2), Expr::BVar(0)), Expr::mk_app(Expr::BVar(3), Expr::mk_app(Expr::mk_const(Name::new("succ"), vec![]), Expr::BVar(1)))))),
                    Rc::new(Expr::Lambda(
                        Name::new("n"), BinderInfo::Default, Rc::new(nat.clone()),
                        Rc::new(succ_body)
                    ))
                ))
            ))
        );

        let rec_val = RecursorVal {
            constant_val: ConstantVal {
                name: Name::new("rec").extend("Nat"),
                level_params: vec![u.clone()],
                ty: sort_u.clone(), // simplified
            },
            all: vec![Name::new("Nat")],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 2,
            rules: vec![
                RecursorRule { ctor: Name::new("zero"), nfields: 0, rhs: zero_rule_rhs },
                RecursorRule { ctor: Name::new("succ"), nfields: 1, rhs: succ_rule_rhs },
            ],
            k: false,
            is_unsafe: false,
        };
        env.insert_constant(
            Name::new("rec").extend("Nat"),
            ConstantInfo::RecursorInfo(rec_val),
        );

        env
    }

    #[test]
    fn test_reduce_recursor_nat() {
        let env = mk_env_with_nat_rec();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let nat_rec = Expr::mk_const(Name::new("rec").extend("Nat"), vec![Level::Zero]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let succ = Expr::mk_const(Name::new("succ"), vec![]);
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);

        // Motive: λ n. Nat
        let motive = Expr::mk_lambda(Name::new("n"), nat.clone(), nat.clone());

        // succ minor premise: λ n ih. succ ih
        let succ_minor = Expr::Lambda(
            Name::new("n"), BinderInfo::Default, Rc::new(nat.clone()),
            Rc::new(Expr::Lambda(
                Name::new("ih"), BinderInfo::Default, Rc::new(nat.clone()),
                Rc::new(Expr::mk_app(succ.clone(), Expr::BVar(0)))
            ))
        );

        // Nat.rec (λ n. Nat) zero (λ n ih. succ ih) zero  ~>  zero
        let app_zero = Expr::mk_app(
            Expr::mk_app(Expr::mk_app(Expr::mk_app(nat_rec.clone(), motive.clone()), zero.clone()), succ_minor.clone()),
            zero.clone()
        );
        let result = tc.whnf(&app_zero);
        assert_eq!(result, zero);

        // Nat.rec (λ n. Nat) zero (λ n ih. succ ih) (succ zero)
        // WHNF gives: (λ n ih. succ ih) zero (Nat.rec (λ n. Nat) zero (λ n ih. succ ih) zero)
        //           = succ (Nat.rec (λ n. Nat) zero (λ n ih. succ ih) zero)
        let one = Expr::mk_app(succ.clone(), zero.clone());
        let app_one = Expr::mk_app(
            Expr::mk_app(Expr::mk_app(Expr::mk_app(nat_rec.clone(), motive.clone()), zero.clone()), succ_minor.clone()),
            one.clone()
        );
        let result = tc.whnf(&app_one);
        // WHNF only reduces head, so inner recursor call remains
        let expected_inner = Expr::mk_app(
            Expr::mk_app(Expr::mk_app(Expr::mk_app(nat_rec, motive), zero.clone()), succ_minor), zero
        );
        let expected = Expr::mk_app(succ, expected_inner);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_proof_irrelevance() {
        let mut env = Environment::new();
        // Add a proposition P : Prop
        let p_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("P"),
                level_params: vec![],
                ty: Expr::mk_prop(),
            },
            is_unsafe: false,
        });
        env.add(p_decl).unwrap();
        // Add proofs p : P and q : P
        let p_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("p"),
                level_params: vec![],
                ty: Expr::mk_const(Name::new("P"), vec![]),
            },
            is_unsafe: false,
        });
        env.add(p_decl).unwrap();
        let q_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("q"),
                level_params: vec![],
                ty: Expr::mk_const(Name::new("P"), vec![]),
            },
            is_unsafe: false,
        });
        env.add(q_decl).unwrap();

        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let p = Expr::mk_const(Name::new("p"), vec![]);
        let q = Expr::mk_const(Name::new("q"), vec![]);
        assert!(tc.is_def_eq(&p, &q));
    }

    #[test]
    fn test_nf() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let body = Expr::BVar(0);
        let lam = Expr::Lambda(
            Name::new("x"),
            BinderInfo::Default,
            Rc::new(nat.clone()),
            Rc::new(body),
        );
        let app = Expr::mk_app(lam, zero.clone());
        let result = tc.nf(&app);
        assert_eq!(result, zero);
    }

    #[test]
    fn test_quot_type_and_reduction() {
        let mut env = Environment::new();
        // Add Nat
        let nat_decl = Declaration::Inductive {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::new("Nat"),
                ty: Expr::mk_type(),
                ctors: vec![
                    Constructor { name: Name::new("zero"), ty: Expr::mk_const(Name::new("Nat"), vec![]) },
                    Constructor { name: Name::new("succ"), ty: Expr::mk_arrow(Expr::mk_const(Name::new("Nat"), vec![]), Expr::mk_const(Name::new("Nat"), vec![])) },
                ],
            }],
            is_unsafe: false,
        };
        env.add(nat_decl).unwrap();
        // Add True : Prop with constructor trivial : True
        let true_decl = Declaration::Inductive {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::new("True"),
                ty: Expr::mk_prop(),
                ctors: vec![Constructor { name: Name::new("trivial"), ty: Expr::mk_const(Name::new("True"), vec![]) }],
            }],
            is_unsafe: false,
        };
        env.add(true_decl).unwrap();
        env.add(Declaration::Quot).unwrap();

        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let succ = Expr::mk_const(Name::new("succ"), vec![]);

        // Build a dummy relation r : Nat -> Nat -> Prop
        // r = fun x y => True (simplified)
        let _prop = Expr::mk_prop();
        let true_const = Expr::mk_const(Name::new("True"), vec![]);
        let r = Expr::mk_lambda(Name::new("x"), nat.clone(),
            Expr::mk_lambda(Name::new("y"), nat.clone(), true_const.clone()));

        let type_u = Level::mk_succ(Level::Zero);

        // Quot Nat r
        let quot_nat_r = Expr::mk_app(
            Expr::mk_app(Expr::mk_const(Name::new("Quot"), vec![type_u.clone()]), nat.clone()),
            r.clone(),
        );

        // Type-check Quot
        let quot_ty = tc.infer(&quot_nat_r).unwrap();
        assert_eq!(quot_ty, Expr::mk_type());

        // Quot.mk Nat r zero
        let mk_app = Expr::mk_app(
            Expr::mk_app(Expr::mk_app(Expr::mk_const(Name::new("Quot").extend("mk"), vec![type_u.clone()]), nat.clone()), r.clone()),
            zero.clone(),
        );
        let mk_ty = tc.infer(&mk_app).unwrap();
        assert_eq!(mk_ty, quot_nat_r);

        // Quot.lift Nat r Nat succ compat (Quot.mk Nat r zero) ~> succ zero
        // Build compat : forall a b, r a b -> Nat
        let compat = Expr::mk_lambda(Name::new("a"), nat.clone(),
            Expr::mk_lambda(Name::new("b"), nat.clone(),
                Expr::mk_lambda(Name::new("h"), true_const.clone(), zero.clone())));

        let lift_app = Expr::mk_app(
            Expr::mk_app(Expr::mk_app(Expr::mk_app(Expr::mk_app(
                Expr::mk_app(Expr::mk_const(Name::new("Quot").extend("lift"), vec![type_u.clone(), type_u.clone()]), nat.clone()),
                r.clone()), nat.clone()), succ.clone()), compat.clone()),
            mk_app.clone(),
        );

        let result = tc.whnf(&lift_app);
        let expected = Expr::mk_app(succ.clone(), zero.clone());
        assert_eq!(result, expected, "Quot.lift reduction failed");
    }

    #[test]
    fn test_mvar_unification() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let mvar = Expr::mk_mvar(Name::new("m1"));

        // ?m = zero should succeed
        assert!(tc.is_def_eq(&mvar, &zero));
        // After assignment, ?m should be defeq to zero
        assert!(tc.is_def_eq(&mvar, &zero));
        // And whnf should reduce ?m to zero
        assert_eq!(tc.whnf(&mvar), zero);
    }

    #[test]
    fn test_mvar_occur_check() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let mvar = Expr::mk_mvar(Name::new("m1"));
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let succ = Expr::mk_const(Name::new("succ"), vec![]);
        // ?m = succ ?m should fail (cyclic)
        let cyclic = Expr::mk_app(succ.clone(), mvar.clone());
        assert!(!tc.is_def_eq(&mvar, &cyclic));
    }

    #[test]
    fn test_mvar_infer_after_assign() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let mvar = Expr::mk_mvar(Name::new("m1"));

        // Assign ?m := zero
        assert!(tc.is_def_eq(&mvar, &zero));
        // infer(?m) should be Nat
        let ty = tc.infer(&mvar).unwrap();
        assert_eq!(ty, nat);
    }

    #[test]
    fn test_level_constraint_solving() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let sort_u = Expr::Sort(Level::Param(Name::new("u")));
        let sort_1 = Expr::mk_type();

        // Sort(u) should unify with Sort(1) and record u -> 1
        assert!(tc.is_def_eq(&sort_u, &sort_1));
        // After unification, Sort(u) should be defeq to Sort(1)
        assert!(tc.is_def_eq(&sort_u, &sort_1));
        // And Sort(u) should be defeq to Sort(u) (reflexive)
        assert!(tc.is_def_eq(&sort_u, &sort_u));
    }

    #[test]
    fn test_level_param_exact_match() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let sort_u1 = Expr::Sort(Level::Param(Name::new("u")));
        let sort_u2 = Expr::Sort(Level::Param(Name::new("u")));
        let sort_v = Expr::Sort(Level::Param(Name::new("v")));

        // Same param should match
        assert!(tc.is_def_eq(&sort_u1, &sort_u2));
        // Different params should match via unification
        assert!(tc.is_def_eq(&sort_u1, &sort_v));
    }

    #[test]
    fn test_level_occur_check() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let u = Level::Param(Name::new("u"));
        let sort_u = Expr::Sort(u.clone());
        let sort_succ_u = Expr::Sort(Level::mk_succ(u.clone()));

        // u should NOT match succ(u) (occur check)
        assert!(!tc.is_def_eq(&sort_u, &sort_succ_u));
    }

    #[test]
    fn test_debug_proof_irrel_with_app() {
        let mut env = Environment::new();
        // Add True
        env.add(Declaration::Inductive {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::new("True"),
                ty: Expr::mk_prop(),
                ctors: vec![Constructor { name: Name::new("trivial"), ty: Expr::mk_const(Name::new("True"), vec![]) }],
            }],
            is_unsafe: false,
        }).unwrap();
        // Add P : Prop
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal { name: Name::new("P"), level_params: vec![], ty: Expr::mk_prop() },
            is_unsafe: false,
        })).unwrap();
        // Add p : P
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal { name: Name::new("p"), level_params: vec![], ty: Expr::mk_const(Name::new("P"), vec![]) },
            is_unsafe: false,
        })).unwrap();
        // Add Q : Nat -> Prop
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal { name: Name::new("Nat"), level_params: vec![], ty: Expr::mk_type() },
            is_unsafe: false,
        })).unwrap();
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal { name: Name::new("Q"), level_params: vec![], ty: Expr::mk_pi(Name::new("_"), nat.clone(), Expr::mk_prop()) },
            is_unsafe: false,
        })).unwrap();
        // Add zero : Nat
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal { name: Name::new("zero"), level_params: vec![], ty: nat.clone() },
            is_unsafe: false,
        })).unwrap();
        // Add q_zero : Q zero
        let q_zero_ty = Expr::mk_app(Expr::mk_const(Name::new("Q"), vec![]), Expr::mk_const(Name::new("zero"), vec![]));
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal { name: Name::new("q_zero"), level_params: vec![], ty: q_zero_ty },
            is_unsafe: false,
        })).unwrap();

        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let trivial = Expr::mk_const(Name::new("trivial"), vec![]);
        let p = Expr::mk_const(Name::new("p"), vec![]);
        let q_zero = Expr::mk_const(Name::new("q_zero"), vec![]);

        // trivial : True, p : P, q_zero : Q zero
        // Any two proofs of Prop-typed things are defeq (kernel's permissive proof irrelevance)
        assert!(tc.is_def_eq(&trivial, &p));
        assert!(tc.is_def_eq(&trivial, &q_zero));
        assert!(tc.is_def_eq(&p, &q_zero));
    }
}
