use super::declaration::*;
use super::environment::Environment;
use super::expr::*;
use super::local_ctx::{LocalCtx, LocalDecl};
use super::type_checker::{TypeChecker, TypeCheckerState};
use std::collections::HashMap;
use std::rc::Rc;

/// A proof goal: local context + target type + placeholder metavariable
#[derive(Debug, Clone)]
pub struct Goal {
    pub lctx: LocalCtx,
    pub target: Expr,
    pub mvar: Name,
}

/// Lightweight tactic engine
pub struct TacticEngine<'a> {
    pub st: &'a mut TypeCheckerState,
    pub env: &'a Environment,
    pub env_bindings: &'a HashMap<String, Expr>,
    /// Stack of open goals (last = current)
    pub goals: Vec<Goal>,
    /// Next fresh index for MVars
    next_mvar_idx: u64,
    /// MVar assignments accumulated during tactic execution
    pub mvar_assignments: HashMap<Name, Expr>,
}

impl<'a> TacticEngine<'a> {
    pub fn new(
        st: &'a mut TypeCheckerState,
        env: &'a Environment,
        env_bindings: &'a HashMap<String, Expr>,
        initial_target: Expr,
    ) -> Self {
        let mut engine = TacticEngine {
            st,
            env,
            env_bindings,
            goals: Vec::new(),
            next_mvar_idx: 0,
            mvar_assignments: HashMap::new(),
        };
        engine.push_goal(initial_target);
        engine
    }

    fn fresh_mvar_name(&mut self) -> Name {
        let idx = self.next_mvar_idx;
        self.next_mvar_idx += 1;
        Name::new(&format!("_tactic_mvar_{}", idx))
    }

    fn push_goal(&mut self, target: Expr) -> Name {
        let mvar = self.fresh_mvar_name();
        self.goals.push(Goal {
            lctx: LocalCtx::new(),
            target,
            mvar: mvar.clone(),
        });
        mvar
    }

    /// Current goal (last on stack)
    pub fn current_goal(&self) -> Option<&Goal> {
        self.goals.last()
    }

    pub fn current_goal_mut(&mut self) -> Option<&mut Goal> {
        self.goals.last_mut()
    }

    /// Pop current goal, returning its mvar
    pub fn pop_goal(&mut self) -> Option<Goal> {
        self.goals.pop()
    }

    /// Number of remaining goals
    pub fn num_goals(&self) -> usize {
        self.goals.len()
    }

    /// Assign a metavariable to a value
    pub fn assign_mvar(&mut self, name: &Name, val: Expr) {
        self.mvar_assignments.insert(name.clone(), val);
    }

    /// Build the final proof term by substituting all MVar assignments
    pub fn build_proof(&self, root: &Expr) -> Expr {
        self.instantiate_mvars(root)
    }

    fn instantiate_mvars(&self, e: &Expr) -> Expr {
        match e {
            Expr::MVar(name) => {
                if let Some(val) = self.mvar_assignments.get(name) {
                    self.instantiate_mvars(val)
                } else {
                    e.clone()
                }
            }
            Expr::App(f, a) => {
                Expr::App(
                    Rc::new(self.instantiate_mvars(f)),
                    Rc::new(self.instantiate_mvars(a)),
                )
            }
            Expr::Lambda(name, bi, ty, body) => {
                Expr::Lambda(name.clone(), *bi, Rc::new(self.instantiate_mvars(ty)), Rc::new(self.instantiate_mvars(body)))
            }
            Expr::Pi(name, bi, ty, body) => {
                Expr::Pi(name.clone(), *bi, Rc::new(self.instantiate_mvars(ty)), Rc::new(self.instantiate_mvars(body)))
            }
            Expr::Let(name, ty, val, body, nd) => {
                Expr::Let(name.clone(), Rc::new(self.instantiate_mvars(ty)), Rc::new(self.instantiate_mvars(val)), Rc::new(self.instantiate_mvars(body)), *nd)
            }
            Expr::Proj(name, idx, e) => {
                Expr::Proj(name.clone(), *idx, Rc::new(self.instantiate_mvars(e)))
            }
            Expr::MData(md, e) => {
                Expr::MData(md.clone(), Rc::new(self.instantiate_mvars(e)))
            }
            other => other.clone(),
        }
    }

    /// Type-check an expression in the current goal's context
    pub fn infer_in_goal(&mut self, e: &Expr) -> Result<Expr, String> {
        if let Some(goal) = self.current_goal() {
            let mut tc = TypeChecker::with_local_ctx(self.st, goal.lctx.clone());
            tc.infer(e)
        } else {
            Err("No current goal".to_string())
        }
    }

    /// Check definitional equality in the current goal's context
    pub fn is_def_eq_in_goal(&mut self, t: &Expr, s: &Expr) -> bool {
        if let Some(goal) = self.current_goal() {
            let mut tc = TypeChecker::with_local_ctx(self.st, goal.lctx.clone());
            tc.is_def_eq(t, s)
        } else {
            false
        }
    }

    /// Introduce a variable from a Pi target
    pub fn tactic_intro(&mut self, name: &str) -> Result<(), String> {
        let target;
        let lctx;
        {
            let goal = self.current_goal_mut().ok_or("No goals remaining")?;
            target = goal.target.clone();
            lctx = goal.lctx.clone();
        }

        // WHNF the target to expose Pi
        let target_whnf = {
            let mut tc = TypeChecker::with_local_ctx(self.st, lctx.clone());
            tc.whnf(&target)
        };

        match &target_whnf {
            Expr::Pi(_, _, dom, body) => {
                let fvar_name = Name::new(name);
                let fvar = Expr::mk_fvar(fvar_name.clone());
                let goal = self.current_goal_mut().ok_or("No goals remaining")?;
                goal.lctx.mk_local_decl(fvar_name.clone(), Name::new(name), (**dom).clone(), BinderInfo::Default);

                // New target is the body with the bound var replaced by FVar
                goal.target = body.instantiate(&fvar);
                Ok(())
            }
            _ => Err(format!("tactic_intro: target is not a Pi type: {}", format_expr(&target_whnf))),
        }
    }

    /// Close current goal with exact proof term
    pub fn tactic_exact(&mut self, proof: &Expr) -> Result<(), String> {
        let goal = self.pop_goal().ok_or("No goals remaining")?;

        let mut tc = TypeChecker::with_local_ctx(self.st, goal.lctx.clone());
        let proof_ty = tc.infer(proof).map_err(|e| format!("tactic_exact: type inference failed: {}", e))?;

        if !tc.is_def_eq(&proof_ty, &goal.target) {
            return Err(format!(
                "tactic_exact: type mismatch. Expected {}, got {}",
                format_expr(&goal.target),
                format_expr(&proof_ty)
            ));
        }

        // Close proof over local context
        let fvars: Vec<Expr> = goal.lctx.iter_decls().map(|d| d.mk_ref()).collect();
        let closed_proof = goal.lctx.mk_lambda(&fvars, proof.clone(), true);
        self.assign_mvar(&goal.mvar, closed_proof);

        Ok(())
    }

    /// Apply a function to the current goal
    pub fn tactic_apply(&mut self, fn_expr: &Expr) -> Result<(), String> {
        let goal = self.current_goal().ok_or("No goals remaining")?;
        let target = goal.target.clone();

        let mut tc = TypeChecker::with_local_ctx(self.st, goal.lctx.clone());
        let fn_ty = tc.infer(fn_expr)
            .map_err(|e| format!("tactic_apply: cannot infer function type: {}", e))?;

        // Decompose function type into premises and conclusion
        let mut premises = Vec::new();
        let mut current_ty = fn_ty;
        loop {
            let whnf_ty = tc.whnf(&current_ty);
            match &whnf_ty {
                Expr::Pi(name, bi, dom, body) => {
                    premises.push((name.clone(), *bi, (**dom).clone()));
                    current_ty = (**body).clone();
                }
                _ => break,
            }
        }

        // Check conclusion matches target
        if !tc.is_def_eq(&current_ty, &target) {
            return Err(format!(
                "tactic_apply: conclusion {} does not match goal {}",
                format_expr(&current_ty),
                format_expr(&target)
            ));
        }

        // Pop current goal
        let goal = self.pop_goal().unwrap();

        // Create subgoals for each premise (reversed so the first premise is the current goal)
        let mut subgoal_mvars: Vec<Expr> = Vec::new();
        for (idx, (name, bi, dom)) in premises.iter().enumerate().rev() {
            let mvar_name = self.push_goal(dom.clone());

            // Create a lambda for the proof term
            let mvar_expr = Expr::mk_mvar(mvar_name.clone());

            // Build the application
            let mut applied = if idx == premises.len() - 1 {
                fn_expr.clone()
            } else {
                subgoal_mvars.last().unwrap().clone()
            };

            applied = Expr::mk_app(applied, mvar_expr.clone());
            subgoal_mvars.push(applied);
        }

        // Build the final proof term
        let proof = if subgoal_mvars.is_empty() {
            fn_expr.clone()
        } else {
            subgoal_mvars.last().unwrap().clone()
        };

        // Close over local context
        let fvars: Vec<Expr> = goal.lctx.iter_decls().map(|d| d.mk_ref()).collect();
        let closed_proof = goal.lctx.mk_lambda(&fvars, proof, true);
        self.assign_mvar(&goal.mvar, closed_proof);

        Ok(())
    }

    /// Try to solve goal by reflexivity (Eq A a a)
    pub fn tactic_refl(&mut self) -> Result<(), String> {
        let goal = self.pop_goal().ok_or("No goals remaining")?;
        let target = goal.target.clone();

        let mut tc = TypeChecker::with_local_ctx(self.st, goal.lctx.clone());
        let target_whnf = tc.whnf(&target);

        let (eq_head, eq_args) = target_whnf.get_app_args();
        let eq_const = eq_head.and_then(|h| h.const_name()).cloned();
        if eq_const != Some(Name::new("Eq")) || eq_args.len() != 3 {
            return Err(format!("tactic_refl: goal is not an equality: {}", format_expr(&target_whnf)));
        }

        let a_type = eq_args[0].clone();
        let a = eq_args[1].clone();
        let b = eq_args[2].clone();

        if !tc.is_def_eq(&a, &b) {
            return Err(format!(
                "tactic_refl: terms are not definitionally equal: {} != {}",
                format_expr(&a),
                format_expr(&b)
            ));
        }

        // Build refl proof: refl A a
        let proof = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_const(Name::new("refl"), vec![]),
                a_type,
            ),
            a,
        );

        let fvars: Vec<Expr> = goal.lctx.iter_decls().map(|d| d.mk_ref()).collect();
        let closed_proof = goal.lctx.mk_lambda(&fvars, proof, true);
        self.assign_mvar(&goal.mvar, closed_proof);

        Ok(())
    }

    /// Try to solve current goal from assumptions in local context
    pub fn tactic_assumption(&mut self) -> Result<(), String> {
        let goal = self.current_goal().ok_or("No goals remaining")?;
        let target = goal.target.clone();
        // Collect fvars first to avoid iterator holding a borrow
        let fvars: Vec<Expr> = goal.lctx.iter_decls().map(|d| d.mk_ref()).collect();

        for fvar in fvars {
            if let Ok(ty) = self.infer_in_goal(&fvar) {
                if self.is_def_eq_in_goal(&ty, &target) {
                    return self.tactic_exact(&fvar);
                }
            }
        }

        Err("tactic_assumption: no matching assumption found".to_string())
    }

    /// Induction on a variable of inductive type
    pub fn tactic_induction(&mut self, var_expr: &Expr) -> Result<(), String> {
        let goal = self.current_goal().ok_or("No goals remaining")?;

        // var_expr must be an FVar
        let var_name = match var_expr {
            Expr::FVar(name) => name.clone(),
            _ => return Err("induction: expected a variable".to_string()),
        };

        let goal_lctx = goal.lctx.clone();

        // Phase 1: Infer variable type (tc scope limited)
        let (var_ty, var_ty_whnf) = {
            let mut tc = TypeChecker::with_local_ctx(self.st, goal_lctx.clone());
            let var_ty = tc.infer(var_expr)
                .map_err(|e| format!("induction: cannot infer type: {}", e))?;
            let var_ty_whnf = tc.whnf(&var_ty);
            (var_ty, var_ty_whnf)
        };

        // Get the inductive type name and arguments
        let (ind_name, ind_args) = {
            let (head, args) = var_ty_whnf.get_app_args();
            let name = head.and_then(|h| h.const_name()).cloned()
                .ok_or_else(|| format!("induction: not an inductive type: {}", format_expr(&var_ty_whnf)))?;
            (name, args.iter().map(|a| (*a).clone()).collect::<Vec<_>>())
        };

        // Find recursor
        let rec_name = Name::new("rec").extend(&ind_name.to_string());
        let rec_info = self.env.find(&rec_name)
            .ok_or_else(|| format!("induction: no recursor for {}", ind_name.to_string()))?;
        let rec_val = rec_info.to_recursor_val()
            .ok_or_else(|| format!("induction: {} is not a recursor", rec_name.to_string()))?;

        // Get inductive info
        let ind_info = self.env.find(&ind_name)
            .ok_or_else(|| format!("induction: inductive type {} not found", ind_name.to_string()))?;
        let ind_val = ind_info.to_inductive_val()
            .ok_or_else(|| format!("induction: {} is not an inductive type", ind_name.to_string()))?;

        let num_params = ind_val.num_params;
        let num_indices = ind_val.num_indices;
        let num_minors = rec_val.num_minors;

        if num_indices > 0 {
            return Err("induction: indexed inductive types not yet supported".to_string());
        }

        // Pop current goal
        let goal = self.pop_goal().unwrap();
        let target = goal.target.clone();

        // Phase 2: Build proof using tc, then drop it before push_goal
        let minor_types = {
            let mut tc = TypeChecker::with_local_ctx(self.st, goal.lctx.clone());

            // Determine universe level from target sort
            let target_sort = tc.infer(&target)
                .map_err(|e| format!("induction: cannot infer target sort: {}", e))?;
            let target_sort_whnf = tc.whnf(&target_sort);
            let u_level = match &target_sort_whnf {
                Expr::Sort(l) => l.clone(),
                _ => Level::Zero,
            };

            // Build motive: λ x. target[x/var]
            let motive = Expr::Lambda(
                var_name.clone(),
                BinderInfo::Default,
                Rc::new(var_ty),
                Rc::new(target.abstract_fvar(&var_name, 0)),
            );

            // Build recursor constant with universe level
            let rec_levels = if rec_val.constant_val.level_params.len() == 1 {
                vec![u_level.clone()]
            } else {
                vec![u_level.clone()]
            };
            let mut proof = Expr::mk_const(rec_name.clone(), rec_levels);

            // Apply params
            for i in 0..num_params as usize {
                if i < ind_args.len() {
                    proof = Expr::mk_app(proof, ind_args[i].clone());
                }
            }

            // Apply motive
            proof = Expr::mk_app(proof, motive.clone());

            // Infer type of partial application to get minor premise types
            let partial_ty = tc.infer(&proof)
                .map_err(|e| format!("induction: cannot infer recursor type: {}", e))?;

            // Collect minor premise types from the Pi chain
            let mut minor_types = Vec::new();
            let mut current_ty = partial_ty;
            for _ in 0..num_minors {
                let c_whnf = tc.whnf(&current_ty);
                match &c_whnf {
                    Expr::Pi(_, _, dom, body) => {
                        minor_types.push((**dom).clone());
                        current_ty = (**body).clone();
                    }
                    _ => return Err(format!(
                        "induction: recursor type does not have enough minor premises. Got: {}",
                        format_expr(&c_whnf)
                    )),
                }
            }
            minor_types
        }; // tc dropped here

        // Create subgoals for each minor premise (in reverse so first is current)
        let mut minor_mvars = Vec::new();
        for minor_ty in minor_types.iter().rev() {
            let mvar_name = self.push_goal(minor_ty.clone());
            minor_mvars.push(Expr::mk_mvar(mvar_name));
        }

        // Reconstruct the proof term
        let u_level = {
            let mut tc = TypeChecker::with_local_ctx(self.st, goal.lctx.clone());
            let target_sort = tc.infer(&target).unwrap_or(Expr::mk_type());
            let target_sort_whnf = tc.whnf(&target_sort);
            match &target_sort_whnf {
                Expr::Sort(l) => l.clone(),
                _ => Level::Zero,
            }
        };

        let motive = Expr::Lambda(
            var_name.clone(),
            BinderInfo::Default,
            Rc::new(var_ty_whnf),
            Rc::new(target.abstract_fvar(&var_name, 0)),
        );

        let rec_levels = vec![u_level.clone()];
        let mut proof = Expr::mk_const(rec_name.clone(), rec_levels);

        for i in 0..num_params as usize {
            if i < ind_args.len() {
                proof = Expr::mk_app(proof, ind_args[i].clone());
            }
        }
        proof = Expr::mk_app(proof, motive.clone());

        // Apply minor premises
        for mvar_expr in minor_mvars.iter().rev() {
            proof = Expr::mk_app(proof, mvar_expr.clone());
        }

        // Apply indices
        for i in num_params as usize..ind_args.len() {
            proof = Expr::mk_app(proof, ind_args[i].clone());
        }

        // Apply major premise (the induction variable)
        proof = Expr::mk_app(proof, var_expr.clone());

        // Close over local context
        let fvars: Vec<Expr> = goal.lctx.iter_decls().map(|d| d.mk_ref()).collect();
        let closed_proof = goal.lctx.mk_lambda(&fvars, proof, true);
        self.assign_mvar(&goal.mvar, closed_proof);

        Ok(())
    }

    /// Introduce a local let-binding (have h : P := proof)
    pub fn tactic_have(&mut self, name: &str, ty: &Expr, proof: &Expr) -> Result<(), String> {
        let goal_lctx = {
            let goal = self.current_goal().ok_or("No goals remaining")?;
            goal.lctx.clone()
        };

        {
            let mut tc = TypeChecker::with_local_ctx(self.st, goal_lctx);
            let proof_ty = tc.infer(proof)
                .map_err(|e| format!("have: type inference failed: {}", e))?;

            if !tc.is_def_eq(&proof_ty, ty) {
                return Err(format!(
                    "have: type mismatch. Expected {}, got {}",
                    format_expr(ty),
                    format_expr(&proof_ty)
                ));
            }
        } // tc released here

        let goal = self.current_goal_mut().ok_or("No goals remaining")?;
        goal.lctx.mk_let_decl(Name::new(name), Name::new(name), ty.clone(), proof.clone());
        Ok(())
    }

    /// Rewrite using an equality hypothesis
    pub fn tactic_rewrite(&mut self, hyp_expr: &Expr) -> Result<(), String> {
        let goal = self.current_goal().ok_or("No goals remaining")?;
        let mut tc = TypeChecker::with_local_ctx(self.st, goal.lctx.clone());

        // Infer type of hypothesis
        let hyp_ty = tc.infer(hyp_expr).map_err(|e| format!("tactic_rewrite: {}", e))?;
        let hyp_whnf = tc.whnf(&hyp_ty);

        // Expect Eq A a b
        let (eq_head, eq_args) = hyp_whnf.get_app_args();
        let eq_const = eq_head.and_then(|h| h.const_name()).cloned();
        if eq_const != Some(Name::new("Eq")) || eq_args.len() != 3 {
            return Err(format!("tactic_rewrite: hypothesis is not an equality: {}", format_expr(&hyp_whnf)));
        }

        let a_type = eq_args[0].clone();
        let a = eq_args[1].clone();
        let b = eq_args[2].clone();

        // Pop current goal
        let goal = self.pop_goal().unwrap();
        let target = goal.target.clone();

        // Create a new goal: target with a replaced by b
        let new_target = replace_expr(&target, &a, &b);
        let new_mvar = self.push_goal(new_target.clone());

        // Build eq_subst A a b (fun x => target[x/a]) hyp_expr ?new_goal
        // eq_subst : forall (A : Type) (a : A) (b : A) (P : A -> Prop),
        //   Eq A a b -> P a -> P b
        // We need: eq_subst A a b (fun x => target[x/a]) hyp_expr ?m : target[b/a]
        let motive_body = replace_expr(&target, &a, &Expr::mk_bvar(0));
        let motive = Expr::Lambda(Name::new("x"), BinderInfo::Default, Rc::new(a_type.clone()), Rc::new(motive_body));

        let proof = Expr::mk_app(
            Expr::mk_app(Expr::mk_app(Expr::mk_app(Expr::mk_app(
                Expr::mk_const(Name::new("eq_subst"), vec![]),
                a_type.clone()),
                a.clone()),
                b.clone()),
                motive.clone()),
            hyp_expr.clone(),
        );
        let proof = Expr::mk_app(proof, Expr::mk_mvar(new_mvar));

        let fvars: Vec<Expr> = goal.lctx.iter_decls().map(|d| d.mk_ref()).collect();
        let closed_proof = goal.lctx.mk_lambda(&fvars, proof, true);
        self.assign_mvar(&goal.mvar, closed_proof);

        Ok(())
    }
}

/// Replace all occurrences of `old` with `new` in `e`
fn replace_expr(e: &Expr, old: &Expr, new: &Expr) -> Expr {
    if e == old {
        return new.clone();
    }
    match e {
        Expr::App(f, a) => {
            Expr::App(Rc::new(replace_expr(f, old, new)), Rc::new(replace_expr(a, old, new)))
        }
        Expr::Lambda(name, bi, ty, body) => {
            Expr::Lambda(name.clone(), *bi, Rc::new(replace_expr(ty, old, new)), Rc::new(replace_expr(body, old, new)))
        }
        Expr::Pi(name, bi, ty, body) => {
            Expr::Pi(name.clone(), *bi, Rc::new(replace_expr(ty, old, new)), Rc::new(replace_expr(body, old, new)))
        }
        Expr::Let(name, ty, val, body, nd) => {
            Expr::Let(name.clone(), Rc::new(replace_expr(ty, old, new)), Rc::new(replace_expr(val, old, new)), Rc::new(replace_expr(body, old, new)), *nd)
        }
        Expr::Proj(name, idx, e) => {
            Expr::Proj(name.clone(), *idx, Rc::new(replace_expr(e, old, new)))
        }
        Expr::MData(md, e) => {
            Expr::MData(md.clone(), Rc::new(replace_expr(e, old, new)))
        }
        other => other.clone(),
    }
}

/// Simple formatter for error messages
fn format_expr(e: &Expr) -> String {
    match e {
        Expr::Const(name, _) => name.to_string(),
        Expr::App(_, _) => {
            let (head, args) = e.get_app_args();
            if let Some(h) = head {
                let mut s = format_expr(h);
                for arg in args {
                    s.push(' ');
                    s.push_str(&format_expr(arg));
                }
                s
            } else {
                "(app)".to_string()
            }
        }
        Expr::Pi(name, _, dom, body) => {
            format!("Pi({} : {}, {})", name.to_string(), format_expr(dom), format_expr(body))
        }
        Expr::Lambda(name, _, dom, body) => {
            format!("fun({} : {}) => {}", name.to_string(), format_expr(dom), format_expr(body))
        }
        Expr::Sort(l) => format!("Sort({})", format_level(l)),
        Expr::BVar(i) => format!("BVar({})", i),
        Expr::FVar(name) => name.to_string(),
        Expr::MVar(name) => format!("?{}", name.to_string()),
        Expr::Let(name, ty, val, body, _) => {
            format!("let {} : {} := {} in {}", name.to_string(), format_expr(ty), format_expr(val), format_expr(body))
        }
        Expr::Proj(name, idx, e) => {
            format!("({}.proj{})", format_expr(e), idx)
        }
        Expr::MData(_, e) => format_expr(e),
        Expr::Lit(lit) => format!("{:?}", lit),
    }
}

fn format_level(l: &Level) -> String {
    match l {
        Level::Zero => "0".to_string(),
        Level::Param(name) => name.to_string(),
        Level::MVar(name) => format!("?{}", name.to_string()),
        Level::Succ(inner) => format!("succ({})", format_level(inner)),
        Level::Max(a, b) => format!("max({}, {})", format_level(a), format_level(b)),
        Level::IMax(a, b) => format!("imax({}, {})", format_level(a), format_level(b)),
    }
}
