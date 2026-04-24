use super::environment::*;
use super::expr::*;
use super::kernel_ext::*;
use super::local_ctx::*;
use std::collections::HashMap;
use std::rc::Rc;

/// Type checker state (caches, etc.)
#[derive(Debug, Clone)]
pub struct TypeCheckerState {
    env: Environment,
    infer_cache: HashMap<Expr, Expr>,
    whnf_cache: HashMap<Expr, Expr>,
    failure_cache: HashMap<(Expr, Expr), bool>,
    /// Universe level parameter substitutions: u -> level
    level_subst: HashMap<Name, Level>,
    /// Outer-layer extensions (quotients, inductive recursors, etc.)
    pub ext: KernelExt,
}

impl TypeCheckerState {
    pub fn new(env: Environment) -> Self {
        TypeCheckerState {
            env,
            infer_cache: HashMap::new(),
            whnf_cache: HashMap::new(),
            failure_cache: HashMap::new(),
            level_subst: HashMap::new(),
            ext: KernelExt::new(),
        }
    }

    pub fn env(&self) -> &Environment {
        &self.env
    }

    pub fn get_level_subst(&self, name: &Name) -> Option<&Level> {
        self.level_subst.get(name)
    }

    /// Delegate to KernelExt for backwards compatibility.
    pub fn register_recursor(&mut self, rec_name: Name, info: RecursorInfo) {
        self.ext.register_recursor(rec_name, info);
    }

    /// Delegate to KernelExt for backwards compatibility.
    pub fn register_quot(&mut self, name: Name) {
        self.ext.register_quot(name);
    }

    /// Delegate to KernelExt for backwards compatibility.
    pub fn is_quot(&self, name: &Name) -> bool {
        self.ext.is_quot(name)
    }

    pub fn with_env(&self, env: Environment) -> Self {
        TypeCheckerState {
            env,
            infer_cache: HashMap::new(),
            whnf_cache: HashMap::new(),
            failure_cache: HashMap::new(),
            level_subst: HashMap::new(),
            ext: self.ext.clone(),
        }
    }

    /// Delegate to KernelExt for backwards compatibility.
    pub fn get_recursor_info(&self, name: &Name) -> Option<&RecursorInfo> {
        self.ext.get_recursor_info(name)
    }

    pub fn assign_level_param(&mut self, name: &Name, level: Level) -> bool {
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
            Level::Param(n) | Level::MVar(n) => n == name,
            Level::Succ(l) => Self::level_contains_param(l, name),
            Level::Max(l1, l2) | Level::IMax(l1, l2) => {
                Self::level_contains_param(l1, name) || Self::level_contains_param(l2, name)
            }
            Level::Zero => false,
        }
    }
}

/// TTobs kernel type checker
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
        // FVar types depend on local context, so don't cache them
        if let Expr::FVar(name) = e {
            return self.lctx
                .get_type(&Expr::FVar(name.clone()))
                .cloned()
                .ok_or_else(|| format!("Unknown free variable {}", name.to_string()));
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
                    Err(format!("Unbound bound variable {}", idx))
                }
            }
            Expr::FVar(_) => unreachable!("FVar handled before cache"),
            Expr::Const(name, levels) => {
                if self.st.is_quot(name) {
                    return self.infer_quot_const(name, levels);
                }
                if !self.st.env().contains(name) {
                    return Err(format!("Constant not found: {:?}", name));
                }
                let info = self.st.env().get(name);
                let ty = info.get_type();
                Ok(self.instantiate_univ_params(ty, info.get_level_params(), levels))
            }
            Expr::App(f, a) => {
                self.infer_app(f, a)
            }
            Expr::Lambda(name, bi, ty, body) => {
                let ty_type = self.infer(ty)?;
                self.ensure_sort(&ty_type)?;

                let fvar = Expr::mk_fvar(name.clone());
                let mut new_lctx = self.lctx.clone();
                let converted_ty = new_lctx.replace_bvars_with_fvars(&ty);
                new_lctx.mk_local_decl(name.clone(), name.clone(), converted_ty, *bi);
                new_lctx.push_bvar(name.clone(), (**ty).clone());

                let body_inst = body.instantiate(&fvar);
                let mut tc = TypeChecker::with_local_ctx(self.st, new_lctx);
                let body_type = tc.infer(&body_inst)?;
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

                let (body_u, body_level_expr) = {
                    let body_inst = body.instantiate(&fvar);
                    let mut tc = TypeChecker::with_local_ctx(self.st, new_lctx);
                    let body_type = tc.infer(&body_inst)?;
                    let body_level = tc.ensure_sort(&body_type)?;
                    let lvl = tc.sort_level(&body_level)?;
                    (lvl, body_level)
                };

                // Pi sort is max(ty_level, body_level)
                // If body is in Omega, Pi is in Omega
                let is_body_omega = matches!(body_level_expr, Expr::Omega(_));
                if is_body_omega {
                    Ok(Expr::Omega(Level::mk_max(ty_u, body_u)))
                } else {
                    Ok(Expr::U(Level::mk_max(ty_u, body_u)))
                }
            }
            Expr::U(level) => {
                Ok(Expr::U(Level::mk_succ(level.clone())))
            }
            Expr::Omega(level) => {
                Ok(Expr::U(Level::mk_succ(level.clone())))
            }
            Expr::Eq(a, t, u) => {
                let a_type = self.infer(a)?;
                let a_level = self.ensure_sort(&a_type)?;
                let level = self.sort_level(&a_level)?;
                self.check(t, a)?;
                self.check(u, a)?;
                Ok(Expr::Omega(level))
            }
            Expr::Cast(a, b, e, t) => {
                let a_type = self.infer(a)?;
                let a_level_expr = self.ensure_sort(&a_type)?;
                let b_type = self.infer(b)?;
                let b_level_expr = self.ensure_sort(&b_type)?;
                let a_level = self.sort_level(&a_level_expr)?;
                let b_level = self.sort_level(&b_level_expr)?;
                // A and B must be in the same sort hierarchy at the same level
                if !self.is_def_eq_levels(&a_level, &b_level) {
                    return Err("Cast: source and target types are at different levels".to_string());
                }
                // e must have type Eq(a, A, B)
                let expected_eq = Expr::mk_eq((**a).clone(), (**a).clone(), (**b).clone());
                self.check(e, &expected_eq)?;
                self.check(t, a)?;
                Ok((**b).clone())
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

        let result = codomain.instantiate(a);
        Ok(self.whnf(&result))
    }

    fn ensure_sort(&mut self, e: &Expr) -> Result<Expr, String> {
        let e_whnf = self.whnf(e);
        match e_whnf {
            Expr::U(_) | Expr::Omega(_) => Ok(e_whnf),
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
            Expr::U(l) | Expr::Omega(l) => Ok(l.clone()),
            _ => Err("Expected sort".to_string()),
        }
    }

    /// Decompose an application chain into (head, args)
    fn get_app_chain(&self, e: &Expr) -> (Expr, Vec<Expr>) {
        let mut head = e.clone();
        let mut args = Vec::new();
        while let Expr::App(f, a) = head {
            args.push((*a).clone());
            head = (*f).clone();
        }
        args.reverse();
        (head, args)
    }

    /// Reduce quotient primitive applications.
    fn reduce_quot(&mut self, e: &Expr) -> Option<Expr> {
        let (fn_expr, args) = e.get_app_args();
        let fn_expr = fn_expr?;

        if let Expr::Const(name, _) = &fn_expr {
            if name == &Name::new("Quot").extend("lift") {
                // Quot.lift A r B f compat q
                if args.len() >= 6 {
                    let q = args[5];
                    let q_whnf = self.whnf_core(q);
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
                    let q_whnf = self.whnf_core(q);
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

    /// Try to apply iota reduction for recursors
    fn try_iota_reduction(&mut self, f_whnf: &Expr, a: &Expr) -> Option<Expr> {
        let (head, mut args) = self.get_app_chain(f_whnf);
        args.push(a.clone());

        if let Expr::Const(rec_name, _) = &head {
            let rec_info_opt = self.st.get_recursor_info(rec_name).cloned();
            if let Some(rec_info) = rec_info_opt {
                let num_minor = rec_info.constructors.len();
                let expected_args = 1 + num_minor + 1; // C + minor premises + target

                if args.len() >= expected_args {
                    let target = &args[args.len() - 1];
                    let target_whnf = self.whnf_core(target);
                    let (ctor_head, ctor_args) = self.get_app_chain(&target_whnf);

                    if let Expr::Const(ctor_name, _) = &ctor_head {
                        if let Some(ctor_idx) = rec_info
                            .constructors
                            .iter()
                            .position(|c| &c.name == ctor_name)
                        {
                            let minor_premise = args[1 + ctor_idx].clone();
                            let ctor_info = &rec_info.constructors[ctor_idx];

                            // Build result: apply minor premise to constructor args,
                            // then to recursive calls
                            let mut result = minor_premise;

                            // Apply constructor args
                            for ctor_arg in &ctor_args {
                                result = Expr::mk_app(result, ctor_arg.clone());
                            }

                            // Apply recursive calls for recursive arguments
                            for rec_arg_idx in &ctor_info.recursive_args {
                                if *rec_arg_idx < ctor_args.len() {
                                    let rec_arg = ctor_args[*rec_arg_idx].clone();
                                    // Build recursor call: rec C m0...mn rec_arg
                                    let mut rec_call = head.clone();
                                    for i in 0..(1 + num_minor) {
                                        rec_call = Expr::mk_app(rec_call, args[i].clone());
                                    }
                                    rec_call = Expr::mk_app(rec_call, rec_arg);
                                    result = Expr::mk_app(result, rec_call);
                                }
                            }

                            return Some(self.whnf_core(&result));
                        }
                    }
                }
            }
        }

        None
    }

    /// Weak head normal form
    pub fn whnf(&mut self, e: &Expr) -> Expr {
        if let Some(result) = self.st.whnf_cache.get(e) {
            return result.clone();
        }

        let result = self.whnf_core(e);
        self.st.whnf_cache.insert(e.clone(), result.clone());
        result
    }

    fn whnf_core(&mut self, e: &Expr) -> Expr {
        match e {
            Expr::BVar(_) | Expr::U(_) | Expr::Omega(_) | Expr::Pi(_, _, _, _) => {
                e.clone()
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
                    if info.is_definition() {
                        if let Some(val) = info.get_value() {
                            let instantiated = self.instantiate_univ_params(val, info.get_level_params(), levels);
                            return self.whnf_core(&instantiated);
                        }
                    }
                }
                e.clone()
            }
            Expr::App(f, a) => {
                let f_whnf = self.whnf_core(f);
                match &f_whnf {
                    Expr::Lambda(_, _, _, body) => {
                        let reduced = body.instantiate(a);
                        self.whnf_core(&reduced)
                    }
                    _ => {
                        // Try quotient reduction
                        let app = Expr::App(Rc::new(f_whnf.clone()), a.clone());
                        if let Some(reduced) = self.reduce_quot(&app) {
                            return self.whnf_core(&reduced);
                        }
                        // Try iota reduction for recursors
                        if let Some(reduced) = self.try_iota_reduction(&f_whnf, a) {
                            return reduced;
                        }
                        Expr::App(Rc::new(f_whnf), a.clone())
                    }
                }
            }
            Expr::Lambda(_, _, _, _) => e.clone(),
            Expr::Eq(a, t, u) => {
                let a_whnf = self.whnf_core(a);
                match a_whnf {
                    Expr::U(level) => {
                        // Eq-U: Eq(U_i, A, B) -> Eq(Omega_i, A, B)
                        Expr::Eq(Rc::new(Expr::Omega(level)), t.clone(), u.clone())
                    }
                    Expr::Pi(name, bi, domain, body) => {
                        // Eq-Π: Eq(Π(x:A).B, f, g) -> Π(x:A). Eq(B, f x, g x)
                        let f = (**t).clone();
                        let g = (**u).clone();
                        let f_app = Expr::App(Rc::new(f.clone()), Rc::new(Expr::BVar(0)));
                        let g_app = Expr::App(Rc::new(g), Rc::new(Expr::BVar(0)));
                        let eq_body = Expr::Eq(body.clone(), Rc::new(f_app), Rc::new(g_app));
                        Expr::Pi(name, bi, domain, Rc::new(eq_body))
                    }
                    _ => {
                        // Stuck equality: return in WHNF if t and u are neutral
                        Expr::Eq(Rc::new(a_whnf), t.clone(), u.clone())
                    }
                }
            }
            Expr::Cast(a, b, e, t) => {
                let a_whnf = self.whnf_core(a);
                let b_whnf = self.whnf_core(b);
                match (&a_whnf, &b_whnf) {
                    (Expr::U(_), Expr::U(_)) => {
                        // Cast-U: cast(U_i, U_i, e, A) -> A
                        return (**t).clone();
                    }
                    (Expr::Omega(_), Expr::Omega(_)) => {
                        // Cast-Ω: cast(Ω_i, Ω_i, e, p) -> p
                        return (**t).clone();
                    }
                    (Expr::Pi(_, _, a_dom, a_body), Expr::Pi(_, _, b_dom, b_body)) => {
                        // Cast-Π (simplified): cast(Π(A,B), Π(A,B'), e, f) -> λ(x:A). cast(B, B', e, f x)
                        // We require domains to be defeq for now (avoids needing sym)
                        if self.is_def_eq(a_dom, b_dom) {
                            let f = (**t).clone();
                            let x = Expr::BVar(0);
                            let f_app = Expr::App(Rc::new(f), Rc::new(x));
                            let cast_body = Expr::Cast(
                                a_body.clone(),
                                b_body.clone(),
                                e.clone(),
                                Rc::new(f_app),
                            );
                            return Expr::Lambda(
                                Name::new("x"),
                                BinderInfo::Default,
                                a_dom.clone(),
                                Rc::new(cast_body),
                            );
                        }
                    }
                    _ => {}
                }
                // Stuck cast
                let t_whnf = self.whnf_core(t);
                Expr::Cast(Rc::new(a_whnf), Rc::new(b_whnf), e.clone(), Rc::new(t_whnf))
            }
        }
    }

    /// Infer the type of a quotient primitive constant.
    fn infer_quot_const(&mut self, name: &Name, levels: &[Level]) -> Result<Expr, String> {
        let omega = Expr::Omega(Level::Zero);
        if name == &Name::new("Quot") {
            // Quot.{u} : (A : U u) -> (A -> A -> Omega) -> U u
            let u = levels.get(0).cloned().unwrap_or(Level::Param(Name::new("u")));
            let sort_u = Expr::U(u);
            let r_ty = Expr::Pi(
                Name::new("_"), BinderInfo::Default,
                Rc::new(Expr::BVar(0)),
                Rc::new(Expr::Pi(
                    Name::new("_"), BinderInfo::Default,
                    Rc::new(Expr::BVar(1)),
                    Rc::new(omega.clone()),
                )),
            );
            Ok(Expr::Pi(
                Name::new("A"), BinderInfo::Default, Rc::new(sort_u.clone()),
                Rc::new(Expr::Pi(
                    Name::new("r"), BinderInfo::Default, Rc::new(r_ty),
                    Rc::new(sort_u),
                )),
            ))
        } else if name == &Name::new("Quot").extend("mk") {
            // Quot.mk.{u} : (A : U u) -> (r : A -> A -> Omega) -> A -> Quot A r
            let u = levels.get(0).cloned().unwrap_or(Level::Param(Name::new("u")));
            let sort_u = Expr::U(u.clone());
            let r_ty = Expr::Pi(
                Name::new("_"), BinderInfo::Default,
                Rc::new(Expr::BVar(0)),
                Rc::new(Expr::Pi(
                    Name::new("_"), BinderInfo::Default,
                    Rc::new(Expr::BVar(1)),
                    Rc::new(omega.clone()),
                )),
            );
            let quot_app = Expr::mk_app(
                Expr::mk_app(Expr::mk_const(Name::new("Quot"), vec![u]), Expr::BVar(2)),
                Expr::BVar(1),
            );
            Ok(Expr::Pi(
                Name::new("A"), BinderInfo::Default, Rc::new(sort_u),
                Rc::new(Expr::Pi(
                    Name::new("r"), BinderInfo::Default, Rc::new(r_ty),
                    Rc::new(Expr::Pi(
                        Name::new("a"), BinderInfo::Default, Rc::new(Expr::BVar(1)),
                        Rc::new(quot_app),
                    )),
                )),
            ))
        } else if name == &Name::new("Quot").extend("lift") {
            // Quot.lift.{u,v} : (A : U u) -> (r : A -> A -> Omega) -> (B : U v) ->
            //   (f : A -> B) -> (compat : forall a b, r a b -> Eq B (f a) (f b)) -> Quot A r -> B
            let u = levels.get(0).cloned().unwrap_or(Level::Param(Name::new("u")));
            let v = levels.get(1).cloned().unwrap_or(Level::Param(Name::new("v")));
            let sort_u = Expr::U(u.clone());
            let sort_v = Expr::U(v);
            let r_ty = Expr::Pi(
                Name::new("_"), BinderInfo::Default,
                Rc::new(Expr::BVar(0)),
                Rc::new(Expr::Pi(
                    Name::new("_"), BinderInfo::Default,
                    Rc::new(Expr::BVar(1)),
                    Rc::new(omega.clone()),
                )),
            );
            let a_to_b = Expr::mk_arrow(Expr::BVar(2), Expr::BVar(1));
            // compat: forall a b, r a b -> Eq B (f a) (f b)
            let f_a = Expr::mk_app(Expr::BVar(2), Expr::BVar(1));
            let f_b = Expr::mk_app(Expr::BVar(2), Expr::BVar(0));
            let eq_app = Expr::mk_eq(Expr::BVar(3), f_a, f_b);
            let compat_ty = Expr::Pi(
                Name::new("a"), BinderInfo::Default, Rc::new(Expr::BVar(3)),
                Rc::new(Expr::Pi(
                    Name::new("b"), BinderInfo::Default, Rc::new(Expr::BVar(4)),
                    Rc::new(Expr::Pi(
                        Name::new("_"), BinderInfo::Default,
                        Rc::new(Expr::mk_app(
                            Expr::mk_app(Expr::BVar(4), Expr::BVar(1)),
                            Expr::BVar(0),
                        )),
                        Rc::new(eq_app),
                    )),
                )),
            );
            let quot_app = Expr::mk_app(
                Expr::mk_app(Expr::mk_const(Name::new("Quot"), vec![u]), Expr::BVar(4)),
                Expr::BVar(3),
            );
            let ret_ty = Expr::BVar(2);
            Ok(Expr::Pi(
                Name::new("A"), BinderInfo::Default, Rc::new(sort_u),
                Rc::new(Expr::Pi(
                    Name::new("r"), BinderInfo::Default, Rc::new(r_ty),
                    Rc::new(Expr::Pi(
                        Name::new("B"), BinderInfo::Default, Rc::new(sort_v),
                        Rc::new(Expr::Pi(
                            Name::new("f"), BinderInfo::Default, Rc::new(a_to_b),
                            Rc::new(Expr::Pi(
                                Name::new("compat"), BinderInfo::Default, Rc::new(compat_ty),
                                Rc::new(Expr::Pi(
                                    Name::new("q"), BinderInfo::Default, Rc::new(quot_app),
                                    Rc::new(ret_ty),
                                )),
                            )),
                        )),
                    )),
                )),
            ))
        } else if name == &Name::new("Quot").extend("ind") {
            // Quot.ind.{u} : (A : U u) -> (r : A -> A -> Omega) ->
            //   (B : Quot A r -> Omega) -> (h : forall a, B (Quot.mk A r a)) ->
            //   (q : Quot A r) -> B q
            let u = levels.get(0).cloned().unwrap_or(Level::Param(Name::new("u")));
            let sort_u = Expr::U(u.clone());
            let r_ty = Expr::Pi(
                Name::new("_"), BinderInfo::Default,
                Rc::new(Expr::BVar(0)),
                Rc::new(Expr::Pi(
                    Name::new("_"), BinderInfo::Default,
                    Rc::new(Expr::BVar(1)),
                    Rc::new(omega.clone()),
                )),
            );
            let b_ty = Expr::mk_arrow(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_const(Name::new("Quot"), vec![u.clone()]), Expr::BVar(1)),
                    Expr::BVar(0),
                ),
                omega.clone(),
            );
            let mk_a = Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_const(Name::new("Quot").extend("mk"), vec![u.clone()]), Expr::BVar(3)),
                    Expr::BVar(2),
                ),
                Expr::BVar(0),
            );
            let h_ty = Expr::Pi(
                Name::new("a"), BinderInfo::Default, Rc::new(Expr::BVar(2)),
                Rc::new(Expr::mk_app(Expr::BVar(1), mk_a)),
            );
            let quot_app = Expr::mk_app(
                Expr::mk_app(Expr::mk_const(Name::new("Quot"), vec![u]), Expr::BVar(3)),
                Expr::BVar(2),
            );
            let ret_ty = Expr::mk_app(Expr::BVar(2), Expr::BVar(0));
            Ok(Expr::Pi(
                Name::new("A"), BinderInfo::Default, Rc::new(sort_u),
                Rc::new(Expr::Pi(
                    Name::new("r"), BinderInfo::Default, Rc::new(r_ty),
                    Rc::new(Expr::Pi(
                        Name::new("B"), BinderInfo::Default, Rc::new(b_ty),
                        Rc::new(Expr::Pi(
                            Name::new("h"), BinderInfo::Default, Rc::new(h_ty),
                            Rc::new(Expr::Pi(
                                Name::new("q"), BinderInfo::Default, Rc::new(quot_app),
                                Rc::new(ret_ty),
                            )),
                        )),
                    )),
                )),
            ))
        } else if name == &Name::new("Quot").extend("sound") {
            // Quot.sound.{u} : (A : U u) -> (r : A -> A -> Omega) -> (a : A) -> (b : A) ->
            //   r a b -> Eq (Quot A r) (Quot.mk A r a) (Quot.mk A r b)
            let u = levels.get(0).cloned().unwrap_or(Level::Param(Name::new("u")));
            let sort_u = Expr::U(u.clone());
            let r_ty = Expr::Pi(
                Name::new("_"), BinderInfo::Default,
                Rc::new(Expr::BVar(0)),
                Rc::new(Expr::Pi(
                    Name::new("_"), BinderInfo::Default,
                    Rc::new(Expr::BVar(1)),
                    Rc::new(omega.clone()),
                )),
            );
            let h_ty = Expr::mk_app(
                Expr::mk_app(Expr::BVar(2), Expr::BVar(1)),
                Expr::BVar(0),
            );
            let quot_app = Expr::mk_app(
                Expr::mk_app(Expr::mk_const(Name::new("Quot"), vec![u.clone()]), Expr::BVar(4)),
                Expr::BVar(3),
            );
            let mk_a = Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_const(Name::new("Quot").extend("mk"), vec![u.clone()]), Expr::BVar(4)),
                    Expr::BVar(3),
                ),
                Expr::BVar(2),
            );
            let mk_b = Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_const(Name::new("Quot").extend("mk"), vec![u.clone()]), Expr::BVar(4)),
                    Expr::BVar(3),
                ),
                Expr::BVar(1),
            );
            let eq_app = Expr::mk_eq(quot_app, mk_a, mk_b);
            Ok(Expr::Pi(
                Name::new("A"), BinderInfo::Default, Rc::new(sort_u),
                Rc::new(Expr::Pi(
                    Name::new("r"), BinderInfo::Default, Rc::new(r_ty),
                    Rc::new(Expr::Pi(
                        Name::new("a"), BinderInfo::Default, Rc::new(Expr::BVar(1)),
                        Rc::new(Expr::Pi(
                            Name::new("b"), BinderInfo::Default, Rc::new(Expr::BVar(2)),
                            Rc::new(Expr::Pi(
                                Name::new("_"), BinderInfo::Default, Rc::new(h_ty),
                                Rc::new(eq_app),
                            )),
                        )),
                    )),
                )),
            ))
        } else {
            Err(format!("Unknown quot constant: {}", name.to_string()))
        }
    }

    /// Check definitional equality
    pub fn is_def_eq(&mut self, t: &Expr, s: &Expr) -> bool {
        if t == s {
            return true;
        }

        let pair = (t.clone(), s.clone());
        if self.st.failure_cache.contains_key(&pair) {
            return false;
        }

        let t_n = self.whnf(t);
        let s_n = self.whnf(s);

        if t_n == s_n {
            return true;
        }

        let result = self.is_def_eq_core(&t_n, &s_n);
        if result {
            return true;
        }

        // Proof irrelevance for Omega types:
        // If t and s have the same type A, and A : Omega_i,
        // then t and s are definitionally equal.
        if let (Ok(t_ty), Ok(s_ty)) = (self.infer(&t_n), self.infer(&s_n)) {
            let t_ty_whnf = self.whnf(&t_ty);
            let s_ty_whnf = self.whnf(&s_ty);
            if self.is_def_eq(&t_ty_whnf, &s_ty_whnf) {
                // Check if the common type lives in Omega (i.e., type_of(A) = Omega_i)
                if let Ok(ty_of_ty) = self.infer(&t_ty_whnf) {
                    let ty_of_ty_whnf = self.whnf(&ty_of_ty);
                    if let Expr::Omega(_) = ty_of_ty_whnf {
                        return true;
                    }
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
            // Cast coherence: cast(A, B, e, t) = t when A = B
            (Expr::Cast(a, b, _, t), s) | (s, Expr::Cast(a, b, _, t)) => {
                if self.is_def_eq(a, b) {
                    if self.is_def_eq(t, s) {
                        return true;
                    }
                }
                false
            }
            (Expr::U(l1), Expr::U(l2)) | (Expr::Omega(l1), Expr::Omega(l2)) => {
                self.is_def_eq_levels(l1, l2)
            }
            (Expr::Const(n1, ls1), Expr::Const(n2, ls2)) => {
                if n1 != n2 {
                    return false;
                }
                let max_len = std::cmp::max(ls1.len(), ls2.len());
                for i in 0..max_len {
                    let l1 = ls1.get(i).cloned().unwrap_or(Level::Zero);
                    let l2 = ls2.get(i).cloned().unwrap_or(Level::Zero);
                    if !self.is_def_eq_levels(&l1, &l2) {
                        return false;
                    }
                }
                true
            }
            (Expr::FVar(n1), Expr::FVar(n2)) => n1 == n2,
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
            (Expr::Eq(a1, t1, u1), Expr::Eq(a2, t2, u2)) => {
                self.is_def_eq(a1, a2) && self.is_def_eq(t1, t2) && self.is_def_eq(u1, u2)
            }
            _ => {
                if self.try_eta_expansion(t, s) || self.try_eta_expansion(s, t) {
                    return true;
                }
                false
            }
        }
    }

    fn try_eta_expansion(&mut self, t: &Expr, s: &Expr) -> bool {
        if let Expr::Lambda(_, _, _, body) = t {
            if let Expr::App(f, a) = body.as_ref() {
                if let Expr::BVar(0) = a.as_ref() {
                    if !f.has_loose_bvar(0) {
                        let f_lifted = f.lift_loose_bvars(1, 0);
                        return self.is_def_eq(&f_lifted, s);
                    }
                }
            }
        }
        false
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
            Expr::Eq(a, t, u) => {
                let a_nf = self.nf(&a);
                let t_nf = self.nf(&t);
                let u_nf = self.nf(&u);
                Expr::Eq(Rc::new(a_nf), Rc::new(t_nf), Rc::new(u_nf))
            }
            Expr::Cast(a, b, e, t) => {
                let a_nf = self.nf(&a);
                let b_nf = self.nf(&b);
                let e_nf = self.nf(&e);
                let t_nf = self.nf(&t);
                Expr::Cast(Rc::new(a_nf), Rc::new(b_nf), Rc::new(e_nf), Rc::new(t_nf))
            }
            other => other,
        }
    }

    // --- Universe level equality ---

    fn is_def_eq_levels(&mut self, l1: &Level, l2: &Level) -> bool {
        let n1 = l1.normalize();
        let n2 = l2.normalize();
        if n1.is_equivalent(&n2) {
            return true;
        }
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
            (Level::Max(a1, b1), Level::Max(a2, b2)) => {
                (self.is_def_eq_levels(a1, a2) && self.is_def_eq_levels(b1, b2))
                    || (self.is_def_eq_levels(a1, b2) && self.is_def_eq_levels(b1, a2))
            }
            (Level::IMax(a1, b1), Level::IMax(a2, b2)) => {
                if self.is_def_eq_levels(a1, a2) && self.is_def_eq_levels(b1, b2) {
                    return true;
                }
                if b1.is_zero() && b2.is_zero() {
                    return true;
                }
                false
            }
            (Level::Max(a, b), Level::Succ(s)) | (Level::Succ(s), Level::Max(a, b)) => {
                (self.is_def_eq_levels(a, &Level::Succ(s.clone())) && self.is_level_leq(b, &Level::Succ(s.clone())))
                    || (self.is_def_eq_levels(b, &Level::Succ(s.clone())) && self.is_level_leq(a, &Level::Succ(s.clone())))
            }
            (Level::IMax(_, b), Level::Zero) | (Level::Zero, Level::IMax(_, b)) => {
                b.is_zero()
            }
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

    // --- Helpers ---

    fn instantiate_univ_params(&self, e: &Expr, params: &[Name], levels: &[Level]) -> Expr {
        if params.is_empty() && self.st.level_subst.is_empty() {
            return e.clone();
        }
        let mut subst: HashMap<Name, Level> = params.iter().cloned().zip(levels.iter().cloned()).collect();
        for (name, level) in &self.st.level_subst {
            subst.insert(name.clone(), level.clone());
        }
        self.replace_levels(e, &subst)
    }

    fn replace_levels(&self, e: &Expr, subst: &HashMap<Name, Level>) -> Expr {
        match e {
            Expr::U(l) => Expr::U(self.replace_level_in_level(l, subst)),
            Expr::Omega(l) => Expr::Omega(self.replace_level_in_level(l, subst)),
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
            Expr::Eq(a, t, u) => Expr::Eq(
                Rc::new(self.replace_levels(a, subst)),
                Rc::new(self.replace_levels(t, subst)),
                Rc::new(self.replace_levels(u, subst)),
            ),
            Expr::Cast(a, b, e, t) => Expr::Cast(
                Rc::new(self.replace_levels(a, subst)),
                Rc::new(self.replace_levels(b, subst)),
                Rc::new(self.replace_levels(e, subst)),
                Rc::new(self.replace_levels(t, subst)),
            ),
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
        format!("{:?}", e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::declaration::*;

    fn mk_env_with_nat() -> Environment {
        let mut env = Environment::new();
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("Nat"),
                level_params: vec![],
                ty: Expr::U(Level::Zero),
            },
            is_unsafe: false,
        })).unwrap();
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("zero"),
                level_params: vec![],
                ty: Expr::mk_const(Name::new("Nat"), vec![]),
            },
            is_unsafe: false,
        })).unwrap();
        env
    }

    #[test]
    fn test_infer_sort() {
        let env = Environment::new();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);
        let u0 = Expr::U(Level::Zero);
        let ty = tc.infer(&u0).unwrap();
        assert_eq!(ty, Expr::U(Level::mk_succ(Level::Zero)));
    }

    #[test]
    fn test_infer_omega() {
        let env = Environment::new();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);
        let o0 = Expr::Omega(Level::Zero);
        let ty = tc.infer(&o0).unwrap();
        assert_eq!(ty, Expr::U(Level::mk_succ(Level::Zero)));
    }

    #[test]
    fn test_infer_const() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let ty = tc.infer(&nat).unwrap();
        assert_eq!(ty, Expr::U(Level::Zero));
    }

    #[test]
    fn test_infer_lambda() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let body = Expr::BVar(0);
        let lam = Expr::Lambda(
            Name::new("x"),
            BinderInfo::Default,
            Rc::new(nat.clone()),
            Rc::new(body),
        );
        let ty = tc.infer(&lam).unwrap();
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
    fn test_eq_pi_reduction() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let id = Expr::Lambda(
            Name::new("x"),
            BinderInfo::Default,
            Rc::new(nat.clone()),
            Rc::new(Expr::BVar(0)),
        );
        let pi_type = Expr::mk_pi(Name::new("_"), nat.clone(), nat.clone());
        let eq = Expr::mk_eq(pi_type, id.clone(), id.clone());
        let result = tc.whnf(&eq);
        // Should reduce to Pi(Nat, λx. Eq(Nat, id x, id x))
        // Note: WHNF does not reduce inside Pi body, so id x remains as App(id, x)
        match result {
            Expr::Pi(_, _, _, body) => {
                match body.as_ref() {
                    Expr::Eq(a, t, u) => {
                        assert_eq!(a.as_ref(), &nat);
                        let expected_app = Expr::App(Rc::new(id.clone()), Rc::new(Expr::BVar(0)));
                        assert_eq!(t.as_ref(), &expected_app);
                        assert_eq!(u.as_ref(), &expected_app);
                    }
                    _ => panic!("Expected Eq in body, got {:?}", body),
                }
            }
            _ => panic!("Expected Pi, got {:?}", result),
        }
    }

    #[test]
    fn test_cast_u_reduction() {
        let env = Environment::new();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);
        let u0 = Expr::U(Level::Zero);
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let e = Expr::mk_const(Name::new("e"), vec![]);
        let cast = Expr::mk_cast(u0.clone(), u0.clone(), e, nat.clone());
        let result = tc.whnf(&cast);
        assert_eq!(result, nat);
    }

    #[test]
    fn test_cast_omega_reduction() {
        let env = Environment::new();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);
        let o0 = Expr::Omega(Level::Zero);
        let p = Expr::mk_const(Name::new("p"), vec![]);
        let e = Expr::mk_const(Name::new("e"), vec![]);
        let cast = Expr::mk_cast(o0.clone(), o0.clone(), e, p.clone());
        let result = tc.whnf(&cast);
        assert_eq!(result, p);
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
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let f = Expr::mk_const(Name::new("f"), vec![]);
        let f_app = Expr::mk_app(f.clone(), Expr::BVar(0));
        let lam = Expr::Lambda(
            Name::new("x"),
            BinderInfo::Default,
            Rc::new(nat.clone()),
            Rc::new(f_app),
        );
        assert!(tc.is_def_eq(&lam, &f));
    }

    #[test]
    fn test_proof_irrelevance_omega() {
        let mut env = Environment::new();
        // P : Omega_0
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("P"),
                level_params: vec![],
                ty: Expr::Omega(Level::Zero),
            },
            is_unsafe: false,
        })).unwrap();
        // p : P
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("p"),
                level_params: vec![],
                ty: Expr::mk_const(Name::new("P"), vec![]),
            },
            is_unsafe: false,
        })).unwrap();
        // q : P
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("q"),
                level_params: vec![],
                ty: Expr::mk_const(Name::new("P"), vec![]),
            },
            is_unsafe: false,
        })).unwrap();

        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let p = Expr::mk_const(Name::new("p"), vec![]);
        let q = Expr::mk_const(Name::new("q"), vec![]);
        assert!(tc.is_def_eq(&p, &q));
    }

    #[test]
    fn test_cast_coherence() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let e = Expr::mk_const(Name::new("e"), vec![]);
        let cast = Expr::mk_cast(nat.clone(), nat.clone(), e, zero.clone());
        assert!(tc.is_def_eq(&cast, &zero));
    }

    #[test]
    fn test_level_constraint_solving() {
        let env = mk_env_with_nat();
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let sort_u = Expr::U(Level::Param(Name::new("u")));
        let sort_1 = Expr::U(Level::mk_succ(Level::Zero));

        assert!(tc.is_def_eq(&sort_u, &sort_1));
        assert!(tc.is_def_eq(&sort_u, &sort_1));
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
    fn test_iota_reduction_bool() {
        // Bool : U
        let mut env = Environment::new();
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("Bool"),
                level_params: vec![],
                ty: Expr::U(Level::Zero),
            },
            is_unsafe: false,
        })).unwrap();
        // true : Bool
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("true"),
                level_params: vec![],
                ty: Expr::mk_const(Name::new("Bool"), vec![]),
            },
            is_unsafe: false,
        })).unwrap();
        // false : Bool
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("false"),
                level_params: vec![],
                ty: Expr::mk_const(Name::new("Bool"), vec![]),
            },
            is_unsafe: false,
        })).unwrap();
        // rec.Bool : Π(C : Bool → U). C true → C false → Π(b : Bool). C b
        let bool_ty = Expr::mk_const(Name::new("Bool"), vec![]);
        let c_ty = Expr::mk_arrow(bool_ty.clone(), Expr::U(Level::Zero));
        let rec_ty = Expr::Pi(
            Name::new("C"), BinderInfo::Default, Rc::new(c_ty.clone()),
            Rc::new(Expr::Pi(
                Name::new("mt"), BinderInfo::Default,
                Rc::new(Expr::mk_app(Expr::BVar(0), Expr::mk_const(Name::new("true"), vec![]))),
                Rc::new(Expr::Pi(
                    Name::new("mf"), BinderInfo::Default,
                    Rc::new(Expr::mk_app(Expr::BVar(1), Expr::mk_const(Name::new("false"), vec![]))),
                    Rc::new(Expr::Pi(
                        Name::new("b"), BinderInfo::Default, Rc::new(bool_ty.clone()),
                        Rc::new(Expr::mk_app(Expr::BVar(2), Expr::BVar(0))),
                    )),
                )),
            )),
        );
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("rec.Bool"),
                level_params: vec![],
                ty: rec_ty,
            },
            is_unsafe: false,
        })).unwrap();

        let mut st = TypeCheckerState::new(env);
        // Register recursor info
        st.register_recursor(
            Name::new("rec.Bool"),
            RecursorInfo {
                inductive_name: Name::new("Bool"),
                constructors: vec![
                    ConstructorInfo { name: Name::new("true"), num_args: 0, recursive_args: vec![] },
                    ConstructorInfo { name: Name::new("false"), num_args: 0, recursive_args: vec![] },
                ],
            },
        );
        let mut tc = TypeChecker::new(&mut st);

        // Build: rec.Bool (\b. Bool) true false true
        let c_val = Expr::Lambda(
            Name::new("b"), BinderInfo::Default,
            Rc::new(bool_ty.clone()),
            Rc::new(bool_ty.clone()),
        );
        let mt = Expr::mk_const(Name::new("true"), vec![]);
        let mf = Expr::mk_const(Name::new("false"), vec![]);
        let b_true = Expr::mk_const(Name::new("true"), vec![]);
        let rec_app = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_const(Name::new("rec.Bool"), vec![]), c_val.clone()),
                    mt.clone(),
                ),
                mf.clone(),
            ),
            b_true.clone(),
        );
        let result = tc.whnf(&rec_app);
        assert_eq!(result, mt);

        // Build: rec.Bool (\b. Bool) true false false
        let b_false = Expr::mk_const(Name::new("false"), vec![]);
        let rec_app2 = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_const(Name::new("rec.Bool"), vec![]), c_val.clone()),
                    mt.clone(),
                ),
                mf.clone(),
            ),
            b_false.clone(),
        );
        let result2 = tc.whnf(&rec_app2);
        assert_eq!(result2, mf);
    }

    #[test]
    fn test_iota_reduction_nat() {
        // Nat : U, zero : Nat, succ : Nat → Nat
        let mut env = Environment::new();
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("Nat"),
                level_params: vec![],
                ty: Expr::U(Level::Zero),
            },
            is_unsafe: false,
        })).unwrap();
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("zero"),
                level_params: vec![],
                ty: nat.clone(),
            },
            is_unsafe: false,
        })).unwrap();
        let nat_to_nat = Expr::mk_arrow(nat.clone(), nat.clone());
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("succ"),
                level_params: vec![],
                ty: nat_to_nat.clone(),
            },
            is_unsafe: false,
        })).unwrap();

        // rec.Nat : Π(C : Nat → U). C zero → (Π(n:Nat). C n → C (succ n)) → Π(n:Nat). C n
        let c_ty = Expr::mk_arrow(nat.clone(), Expr::U(Level::Zero));
        let rec_ty = Expr::Pi(
            Name::new("C"), BinderInfo::Default, Rc::new(c_ty.clone()),
            Rc::new(Expr::Pi(
                Name::new("mz"), BinderInfo::Default,
                Rc::new(Expr::mk_app(Expr::BVar(0), Expr::mk_const(Name::new("zero"), vec![]))),
                Rc::new(Expr::Pi(
                    Name::new("ms"), BinderInfo::Default,
                    Rc::new(Expr::Pi(
                        Name::new("n"), BinderInfo::Default, Rc::new(nat.clone()),
                        Rc::new(Expr::mk_arrow(
                            Expr::mk_app(Expr::BVar(1), Expr::BVar(0)),
                            Expr::mk_app(Expr::BVar(1), Expr::mk_app(Expr::mk_const(Name::new("succ"), vec![]), Expr::BVar(0))),
                        )),
                    )),
                    Rc::new(Expr::Pi(
                        Name::new("n"), BinderInfo::Default, Rc::new(nat.clone()),
                        Rc::new(Expr::mk_app(Expr::BVar(2), Expr::BVar(0))),
                    )),
                )),
            )),
        );
        env.add(Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("rec.Nat"),
                level_params: vec![],
                ty: rec_ty,
            },
            is_unsafe: false,
        })).unwrap();

        let mut st = TypeCheckerState::new(env);
        st.register_recursor(
            Name::new("rec.Nat"),
            RecursorInfo {
                inductive_name: Name::new("Nat"),
                constructors: vec![
                    ConstructorInfo { name: Name::new("zero"), num_args: 0, recursive_args: vec![] },
                    ConstructorInfo { name: Name::new("succ"), num_args: 1, recursive_args: vec![0] },
                ],
            },
        );
        let mut tc = TypeChecker::new(&mut st);

        // C = \n. Nat
        let c_val = Expr::Lambda(
            Name::new("n"), BinderInfo::Default,
            Rc::new(nat.clone()), Rc::new(nat.clone()),
        );
        let mz = Expr::mk_const(Name::new("zero"), vec![]);
        // ms = \n. \ih. succ n
        let ms = Expr::Lambda(
            Name::new("n"), BinderInfo::Default, Rc::new(nat.clone()),
            Rc::new(Expr::Lambda(
                Name::new("ih"), BinderInfo::Default,
                Rc::new(Expr::mk_app(c_val.clone(), Expr::BVar(0))),
                Rc::new(Expr::mk_app(Expr::mk_const(Name::new("succ"), vec![]), Expr::BVar(1))),
            )),
        );

        // rec.Nat (\n.Nat) zero ms zero → zero
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let rec_app_zero = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_const(Name::new("rec.Nat"), vec![]), c_val.clone()),
                    mz.clone(),
                ),
                ms.clone(),
            ),
            zero.clone(),
        );
        let result = tc.whnf(&rec_app_zero);
        assert_eq!(result, zero);

        // rec.Nat (\n.Nat) zero ms (succ zero) → ms zero (rec.Nat ... zero)
        // Since ms ignores ih and returns succ n, result should be succ zero
        let succ_zero = Expr::mk_app(Expr::mk_const(Name::new("succ"), vec![]), zero.clone());
        let rec_app_succ = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_const(Name::new("rec.Nat"), vec![]), c_val.clone()),
                    mz.clone(),
                ),
                ms.clone(),
            ),
            succ_zero.clone(),
        );
        let result2 = tc.whnf(&rec_app_succ);
        // After iota reduction: ms zero (rec.Nat C mz ms zero)
        // ms zero ih → succ zero (since ms ignores ih)
        // But whnf should fully reduce through beta
        let expected = succ_zero;
        assert_eq!(result2, expected);
    }

    #[test]
    fn test_quot_type_inference() {
        let env = Environment::new();
        let mut st = TypeCheckerState::new(env);
        for name in [
            Name::new("Quot"),
            Name::new("Quot").extend("mk"),
            Name::new("Quot").extend("lift"),
            Name::new("Quot").extend("ind"),
            Name::new("Quot").extend("sound"),
        ] {
            st.register_quot(name);
        }
        let mut tc = TypeChecker::new(&mut st);

        // infer(Quot.{0}) should be a Pi type
        let quot = Expr::mk_const(Name::new("Quot"), vec![Level::Zero]);
        let ty = tc.infer(&quot).unwrap();
        match ty {
            Expr::Pi(_, _, _, _) => {}
            _ => panic!("Expected Pi type for Quot, got {:?}", ty),
        }

        // infer(Quot.mk.{0}) should be a Pi type
        let quot_mk = Expr::mk_const(Name::new("Quot").extend("mk"), vec![Level::Zero]);
        let ty = tc.infer(&quot_mk).unwrap();
        match ty {
            Expr::Pi(_, _, _, _) => {}
            _ => panic!("Expected Pi type for Quot.mk, got {:?}", ty),
        }
    }

    #[test]
    fn test_quot_lift_reduction() {
        let env = Environment::new();
        let mut st = TypeCheckerState::new(env);
        for name in [
            Name::new("Quot"),
            Name::new("Quot").extend("mk"),
            Name::new("Quot").extend("lift"),
            Name::new("Quot").extend("ind"),
            Name::new("Quot").extend("sound"),
        ] {
            st.register_quot(name);
        }
        let mut tc = TypeChecker::new(&mut st);

        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);

        // Build: Quot.lift Nat r Nat (\x.x) compat (Quot.mk Nat r zero)
        // where r is a dummy relation
        let r = Expr::Lambda(
            Name::new("x"), BinderInfo::Default, Rc::new(nat.clone()),
            Rc::new(Expr::Lambda(
                Name::new("y"), BinderInfo::Default, Rc::new(nat.clone()),
                Rc::new(Expr::mk_const(Name::new("true"), vec![])),
            )),
        );
        let f = Expr::Lambda(
            Name::new("x"), BinderInfo::Default, Rc::new(nat.clone()),
            Rc::new(Expr::BVar(0)),
        );
        let compat = Expr::mk_const(Name::new("compat"), vec![]);
        let quot_mk = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(Expr::mk_const(Name::new("Quot").extend("mk"), vec![Level::Zero]), nat.clone()),
                r.clone(),
            ),
            zero.clone(),
        );
        let quot_lift = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(
                        Expr::mk_app(
                            Expr::mk_app(Expr::mk_const(Name::new("Quot").extend("lift"), vec![Level::Zero, Level::Zero]), nat.clone()),
                            r.clone(),
                        ),
                        nat.clone(),
                    ),
                    f.clone(),
                ),
                compat.clone(),
            ),
            quot_mk,
        );
        let result = tc.whnf(&quot_lift);
        // Should reduce to f zero = zero
        assert_eq!(result, zero);
    }
}
