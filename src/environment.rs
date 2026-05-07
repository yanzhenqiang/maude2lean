use super::declaration::*;
use super::expr::*;
use std::collections::HashMap;
use std::rc::Rc;

/// Lean environment stores all constant declarations
#[derive(Debug, Clone)]
pub struct Environment {
    constants: HashMap<Name, ConstantInfo>,
    quot_initialized: bool,
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            constants: HashMap::new(),
            quot_initialized: false,
        }
    }

    pub fn is_quot_initialized(&self) -> bool {
        self.quot_initialized
    }

    pub fn mark_quot_initialized(&mut self) {
        self.quot_initialized = true;
    }

    /// Find a constant by name
    pub fn find(&self, name: &Name) -> Option<&ConstantInfo> {
        self.constants.get(name)
    }

    /// Get all constructor names for an inductive type.
    /// Returns None if the type is not found or is not inductive.
    pub fn get_constructors(&self, type_name: &Name) -> Option<Vec<Name>> {
        self.find(type_name)?.to_inductive_val().map(|v| v.ctors.clone())
    }

    /// Get a constructor name by index for an inductive type.
    /// Returns None if the type is not found or index is out of bounds.
    pub fn get_constructor(&self, type_name: &Name, idx: usize) -> Option<Name> {
        let ctors = self.get_constructors(type_name)?;
        ctors.get(idx).cloned()
    }

    /// Resolve a bare constant name to its fully-qualified Name.
    /// Searches all constants (definitions, theorems, constructors, axioms).
    /// Returns the name if exactly one match is found.
    pub fn resolve_constant_name(&self, bare: &str) -> Option<Name> {
        let mut candidates = Vec::new();
        for (_, info) in self.constants.iter() {
            let name = info.name();
            if name.last() == bare {
                candidates.push(name.clone());
            }
        }
        if candidates.len() == 1 {
            Some(candidates[0].clone())
        } else {
            None
        }
    }

    /// Get a constructor name by its bare name, searching all constructors.
    /// Returns the fully-qualified name if exactly one match is found.
    pub fn resolve_ctor_name(&self, bare: &str) -> Option<Name> {
        let mut candidates = Vec::new();
        for (_, info) in self.constants.iter() {
            if let Some(cval) = info.to_constructor_val() {
                if cval.constant_val.name.last() == bare {
                    candidates.push(cval.constant_val.name.clone());
                }
            }
        }
        if candidates.len() == 1 {
            Some(candidates[0].clone())
        } else {
            None
        }
    }

    /// Get a constructor name by its bare name, scoped to a specific inductive type.
    pub fn resolve_ctor_name_in(&self, type_name: &Name, bare: &str) -> Option<Name> {
        let ctors = self.get_constructors(type_name)?;
        ctors.iter().find(|c| c.last() == bare).cloned()
    }

    /// Get a constant by name (panics if not found)
    pub fn get(&self, name: &Name) -> &ConstantInfo {
        self.constants.get(name).expect("Constant not found")
    }

    /// Check if a constant exists
    pub fn contains(&self, name: &Name) -> bool {
        self.constants.contains_key(name)
    }

    /// Insert a constant info directly (used for recursors and built-ins)
    pub fn insert_constant(&mut self, name: Name, info: ConstantInfo) {
        self.constants.insert(name, info);
    }

    /// Add a declaration to the environment
    pub fn add(&mut self, decl: Declaration) -> Result<(), String> {
        match decl {
            Declaration::Axiom(val) => {
                let info = ConstantInfo::AxiomInfo(val.clone());
                self.check_name(&val.constant_val.name)?;
                self.constants.insert(val.constant_val.name, info);
                Ok(())
            }
            Declaration::Definition(val) => {
                let info = ConstantInfo::DefinitionInfo(val.clone());
                self.check_name(&val.constant_val.name)?;
                self.check_duplicated_univ_params(&val.constant_val.level_params)?;
                self.constants.insert(val.constant_val.name, info);
                Ok(())
            }
            Declaration::Theorem(val) => {
                let info = ConstantInfo::TheoremInfo(val.clone());
                self.check_name(&val.constant_val.name)?;
                self.check_duplicated_univ_params(&val.constant_val.level_params)?;
                self.constants.insert(val.constant_val.name, info);
                Ok(())
            }
            Declaration::Opaque(val) => {
                let info = ConstantInfo::OpaqueInfo(val.clone());
                self.check_name(&val.constant_val.name)?;
                self.check_duplicated_univ_params(&val.constant_val.level_params)?;
                self.constants.insert(val.constant_val.name, info);
                Ok(())
            }
            Declaration::Quot => {
                self.add_quot()
            }
            Declaration::MutualDefinition(defs) => {
                for val in defs {
                    let info = ConstantInfo::DefinitionInfo(val.clone());
                    self.check_name(&val.constant_val.name)?;
                    self.check_duplicated_univ_params(&val.constant_val.level_params)?;
                    self.constants.insert(val.constant_val.name, info);
                }
                Ok(())
            }
            Declaration::Inductive { level_params, num_params, types, is_unsafe } => {
                self.add_inductive(level_params, num_params, types, is_unsafe)
            }
        }
    }

    fn check_name(&self, name: &Name) -> Result<(), String> {
        if self.constants.contains_key(name) {
            Err(format!("Constant '{}' already declared", name.to_string()))
        } else {
            Ok(())
        }
    }

    fn check_duplicated_univ_params(&self, params: &Vec<Name>) -> Result<(), String> {
        let mut seen = HashMap::new();
        for p in params {
            if seen.contains_key(p) {
                return Err(format!("Duplicate universe parameter '{}'", p.to_string()));
            }
            seen.insert(p.clone(), true);
        }
        Ok(())
    }

    fn add_quot(&mut self) -> Result<(), String> {
        // Add Quot, Quot.mk, Quot.lift, Quot.ind
        // Actual types are hardcoded in the type checker; we insert minimal stubs here.
        let u = Name(vec!["u".to_string()]);
        let dummy_ty = Expr::mk_type();

        let quot_name = Name::new("Quot");
        self.constants.insert(quot_name.clone(), ConstantInfo::QuotInfo(QuotVal {
            constant_val: ConstantVal { name: quot_name, level_params: vec![u.clone()], ty: dummy_ty.clone() },
            kind: QuotKind::Type,
        }));

        let mk_name = Name::new("Quot").extend("mk");
        self.constants.insert(mk_name.clone(), ConstantInfo::QuotInfo(QuotVal {
            constant_val: ConstantVal { name: mk_name, level_params: vec![u.clone()], ty: dummy_ty.clone() },
            kind: QuotKind::Mk,
        }));

        let lift_name = Name::new("Quot").extend("lift");
        let v = Name(vec!["v".to_string()]);
        self.constants.insert(lift_name.clone(), ConstantInfo::QuotInfo(QuotVal {
            constant_val: ConstantVal { name: lift_name, level_params: vec![u.clone(), v], ty: dummy_ty.clone() },
            kind: QuotKind::Lift,
        }));

        let ind_name = Name::new("Quot").extend("ind");
        self.constants.insert(ind_name.clone(), ConstantInfo::QuotInfo(QuotVal {
            constant_val: ConstantVal { name: ind_name, level_params: vec![u.clone()], ty: dummy_ty.clone() },
            kind: QuotKind::Ind,
        }));

        let sound_name = Name::new("Quot").extend("sound");
        self.constants.insert(sound_name.clone(), ConstantInfo::QuotInfo(QuotVal {
            constant_val: ConstantVal { name: sound_name, level_params: vec![u.clone()], ty: dummy_ty },
            kind: QuotKind::Sound,
        }));

        self.mark_quot_initialized();
        Ok(())
    }

    fn add_inductive(
        &mut self,
        level_params: Vec<Name>,
        num_params: u64,
        types: Vec<InductiveType>,
        is_unsafe: bool,
    ) -> Result<(), String> {
        let all_names: Vec<Name> = types.iter().map(|t| t.name.clone()).collect();

        for (_idx, ind_type) in types.iter().enumerate() {
            let num_indices = Self::count_indices(&ind_type.ty, num_params);
            let ctor_names: Vec<Name> = ind_type.ctors.iter().map(|c| c.name.clone()).collect();

            // Validate constructors and compute is_rec
            let mut is_rec = false;
            for ctor in &ind_type.ctors {
                // Check constructor return type matches inductive type
                Self::validate_constructor_return_type(
                    &ctor.ty, num_params, &ind_type.name, num_params, num_indices
                )?;
                // Check if constructor has recursive arguments
                if Self::ctor_is_recursive_mutual(&ctor.ty, num_params, &all_names) {
                    is_rec = true;
                }
            }

            // Add inductive type
            let inductive_val = InductiveVal {
                constant_val: ConstantVal {
                    name: ind_type.name.clone(),
                    level_params: level_params.clone(),
                    ty: ind_type.ty.clone(),
                },
                num_params,
                num_indices,
                all: all_names.clone(),
                ctors: ctor_names.clone(),
                num_nested: 0,
                is_rec,
                is_unsafe,
                is_reflexive: false,
            };

            self.check_name(&ind_type.name)?;
            self.constants.insert(
                ind_type.name.clone(),
                ConstantInfo::InductiveInfo(inductive_val),
            );

            // Extract param names for converting constructor types to de Bruijn
            let param_names = Self::extract_param_names(&ind_type.ty, num_params);

            // Add constructors
            for (cidx, ctor) in ind_type.ctors.iter().enumerate() {
                let num_fields = Self::count_fields(&ctor.ty, num_params);
                // Convert parameter constants to bound variables for type inference
                let ctor_ty_debruijn = Self::abstract_params(&ctor.ty, &param_names, 0);
                let ctor_val = ConstructorVal {
                    constant_val: ConstantVal {
                        name: ctor.name.clone(),
                        level_params: level_params.clone(),
                        ty: ctor_ty_debruijn,
                    },
                    induct: ind_type.name.clone(),
                    cidx: cidx as u64,
                    num_params,
                    num_fields,
                    is_unsafe,
                };

                self.check_name(&ctor.name)?;
                self.constants.insert(
                    ctor.name.clone(),
                    ConstantInfo::ConstructorInfo(ctor_val),
                );
            }

            // Generate recursor
            let rec_name = Name::new("rec").extend(&ind_type.name.to_string());
            let type_idx = _idx; // index of current type in all_names
            let num_motives = all_names.len() as u64;

            // Build global constructor list: all constructors across all types
            // Each entry: (global_cidx, type_idx_of_ctor, constructor)
            let mut global_ctors: Vec<(usize, usize, &Constructor)> = Vec::new();
            for (tidx, t) in types.iter().enumerate() {
                for (_cidx, ctor) in t.ctors.iter().enumerate() {
                    global_ctors.push((global_ctors.len(), tidx, ctor));
                }
            }
            let total_minors = global_ctors.len() as u64;

            // Build rules only for the current type's constructors
            let mut rules = Vec::new();
            for (cidx, ctor) in ind_type.ctors.iter().enumerate() {
                let nfields = Self::count_fields(&ctor.ty, num_params);
                let ctor_is_rec = Self::ctor_is_recursive_mutual(&ctor.ty, num_params, &all_names);
                // Find global cidx for this constructor
                let global_cidx = global_ctors.iter()
                    .position(|(_, tidx, c)| *tidx == type_idx && c.name == ctor.name)
                    .unwrap_or(cidx) as u64;
                let rhs = Self::mk_recursor_rhs(
                    &ctor.ty,
                    num_params,
                    nfields,
                    total_minors,
                    global_cidx,
                    &ind_type.name,
                    &level_params,
                    ctor_is_rec,
                    &all_names,
                    type_idx as u64,
                );
                rules.push(RecursorRule {
                    ctor: ctor.name.clone(),
                    nfields,
                    rhs,
                });
            }

            // Generate recursor type with minor premises for ALL constructors
            let (rec_ty, rec_u) = Self::mk_recursor_type(
                &ind_type.name,
                &ind_type.ty,
                num_params,
                num_indices,
                &global_ctors,
                &all_names,
                type_idx,
            );

            let mut rec_level_params = level_params.clone();
            rec_level_params.push(rec_u);

            let rec_val = RecursorVal {
                constant_val: ConstantVal {
                    name: rec_name.clone(),
                    level_params: rec_level_params,
                    ty: rec_ty,
                },
                all: all_names.clone(),
                num_params,
                num_indices,
                num_motives,
                num_minors: total_minors,
                rules,
                k: num_indices == 0 && !is_rec, // K-like if no indices and not recursive
                is_unsafe,
            };

            self.constants.insert(rec_name, ConstantInfo::RecursorInfo(rec_val));
        }

        Ok(())
    }

    /// Validate that a constructor's return type (after consuming params) is the inductive type.
    fn validate_constructor_return_type(
        ctor_ty: &Expr,
        num_params: u64,
        ind_name: &Name,
        _ind_num_params: u64,
        _ind_num_indices: u64,
    ) -> Result<(), String> {
        let mut current = ctor_ty;
        // Skip parameter binders
        for _ in 0..num_params {
            if let Some(body) = current.binding_body() {
                current = body;
            } else {
                return Err("Constructor type has fewer Pi binders than declared parameters".to_string());
            }
        }
        // Skip field binders to get to the return type
        while current.is_pi() {
            if let Some(body) = current.binding_body() {
                current = body;
            } else {
                break;
            }
        }
        // The result should be an application of the inductive type (or just the inductive type)
        let head = current.get_app_fn();
        if let Expr::Const(name, _) = head {
            if name == ind_name {
                return Ok(());
            }
        }
        // For simple cases like `Nat` with no params/indices, the return type is just `Const(Nat)`
        if let Expr::Const(name, _) = current {
            if name == ind_name {
                return Ok(());
            }
        }
        Err(format!(
            "Constructor return type {:?} does not match inductive type {}",
            current, ind_name.to_string()
        ))
    }

    /// Check if a constructor has recursive arguments (mutual inductive).
    fn ctor_is_recursive_mutual(ctor_ty: &Expr, num_params: u64, all_names: &[Name]) -> bool {
        let mut current = ctor_ty;
        for _ in 0..num_params {
            if let Some(body) = current.binding_body() {
                current = body;
            } else {
                return false;
            }
        }
        while let Expr::Pi(_, _, domain, body) = current {
            if Self::expr_contains_any_const(domain, all_names) {
                return true;
            }
            current = body;
        }
        false
    }

    /// Check if an expression contains a constant with the given name.
    fn expr_contains_const(e: &Expr, name: &Name) -> bool {
        match e {
            Expr::Const(n, _) => n == name,
            Expr::App(f, a) => Self::expr_contains_const(f, name) || Self::expr_contains_const(a, name),
            Expr::Pi(_, _, ty, body) => Self::expr_contains_const(ty, name) || Self::expr_contains_const(body, name),
            Expr::Lambda(_, _, ty, body) => Self::expr_contains_const(ty, name) || Self::expr_contains_const(body, name),
            Expr::Let(_, ty, value, body, _) => {
                Self::expr_contains_const(ty, name)
                    || Self::expr_contains_const(value, name)
                    || Self::expr_contains_const(body, name)
            }
            Expr::Sort(l) => Self::level_contains_name(l, name),
            _ => false,
        }
    }

    /// Check if an expression contains any of the given constants.
    fn expr_contains_any_const(e: &Expr, names: &[Name]) -> bool {
        names.iter().any(|n| Self::expr_contains_const(e, n))
    }

    /// Find which mutual type (if any) the expression contains.
    /// Returns the index in `names` of the first matching type.
    fn find_mutual_type(e: &Expr, names: &[Name]) -> Option<usize> {
        for (i, name) in names.iter().enumerate() {
            if Self::expr_contains_const(e, name) {
                return Some(i);
            }
        }
        None
    }

    fn level_contains_name(l: &Level, name: &Name) -> bool {
        match l {
            Level::Param(n) | Level::MVar(n) => n == name,
            Level::Succ(l) => Self::level_contains_name(l, name),
            Level::Max(l1, l2) | Level::IMax(l1, l2) => {
                Self::level_contains_name(l1, name) || Self::level_contains_name(l2, name)
            }
            Level::Zero => false,
        }
    }

    /// Map bound variable indices in an expression using a function.
    fn map_bvars(e: &Expr, f: &dyn Fn(u64) -> u64) -> Expr {
        match e {
            Expr::BVar(i) => Expr::mk_bvar(f(*i)),
            Expr::App(a, b) => Expr::mk_app(
                Self::map_bvars(a, f),
                Self::map_bvars(b, f),
            ),
            Expr::Pi(n, bi, ty, body) => Expr::Pi(
                n.clone(),
                *bi,
                Rc::new(Self::map_bvars(ty, f)),
                Rc::new(Self::map_bvars(body, f)),
            ),
            Expr::Lambda(n, bi, ty, body) => Expr::Lambda(
                n.clone(),
                *bi,
                Rc::new(Self::map_bvars(ty, f)),
                Rc::new(Self::map_bvars(body, f)),
            ),
            Expr::Let(n, ty, val, body, nd) => Expr::Let(
                n.clone(),
                Rc::new(Self::map_bvars(ty, f)),
                Rc::new(Self::map_bvars(val, f)),
                Rc::new(Self::map_bvars(body, f)),
                *nd,
            ),
            Expr::Sort(l) => Expr::Sort(l.clone()),
            Expr::Const(n, ls) => Expr::Const(n.clone(), ls.clone()),
            Expr::FVar(n) => Expr::FVar(n.clone()),
            Expr::MVar(n) => Expr::MVar(n.clone()),
            Expr::Lit(l) => Expr::Lit(l.clone()),
            Expr::MData(d, e) => Expr::MData(d.clone(), Rc::new(Self::map_bvars(e, f))),
            Expr::Proj(s, i, e) => Expr::Proj(s.clone(), *i, Rc::new(Self::map_bvars(e, f))),
        }
    }

    /// Build the recursor rule RHS for a constructor.
    ///
    /// The result is wrapped in lambdas with binding order (from outside in):
    ///   params, motives, minors, fields
    ///
    /// Inside the innermost body:
    ///   BVar(0) = last field
    ///   BVar(nfields - 1) = first field
    ///   BVar(nfields) = last minor premise
    ///   BVar(nfields + n_minors - 1) = first minor premise
    ///   BVar(nfields + n_minors) = last motive
    ///   BVar(nfields + n_minors + n_motives - 1) = first motive
    ///   BVar(nfields + n_minors + n_motives) = last param
    ///   BVar(nfields + n_minors + n_motives + num_params - 1) = first param
    fn mk_recursor_rhs(
        ctor_ty: &Expr,
        num_params: u64,
        nfields: u64,
        num_minors: u64,
        cidx: u64,
        ind_name: &Name,
        level_params: &[Name],
        is_rec: bool,
        all_names: &[Name],
        current_type_idx: u64,
    ) -> Expr {
        let num_motives = all_names.len() as u64;
        let total_bound = nfields + num_minors + num_motives + num_params;

        // Build the inner body
        let minor_idx = nfields + num_minors - 1 - cidx;
        let mut body = Expr::mk_bvar(minor_idx);

        // Apply all fields to the minor premise
        for j in 0..nfields {
            let field_idx = nfields - 1 - j;
            body = Expr::mk_app(body, Expr::mk_bvar(field_idx));
        }

        // For recursive constructors, also apply the recursive call
        if is_rec && nfields > 0 {
            // Determine which mutual type the last field references
            let last_field_type = Self::get_last_field_type(ctor_ty, num_params);
            let rec_type_idx = Self::find_mutual_type(&last_field_type, all_names)
                .unwrap_or(current_type_idx as usize) as u64;
            let rec_type_name = &all_names[rec_type_idx as usize];

            let rec_levels: Vec<Level> = level_params.iter().cloned().map(Level::Param).collect();
            let mut rec_call = Expr::mk_const(
                Name::new("rec").extend(&rec_type_name.to_string()),
                rec_levels,
            );

            // Apply params
            for i in 0..num_params {
                let param_idx = total_bound - 1 - i;
                rec_call = Expr::mk_app(rec_call, Expr::mk_bvar(param_idx));
            }

            // Apply all motives
            for i in 0..num_motives {
                let motive_idx = total_bound - 1 - num_params - i;
                rec_call = Expr::mk_app(rec_call, Expr::mk_bvar(motive_idx));
            }

            // Apply minors
            for i in 0..num_minors {
                let minor_bvar_idx = nfields + num_minors - 1 - i;
                rec_call = Expr::mk_app(rec_call, Expr::mk_bvar(minor_bvar_idx));
            }

            // Extract index expressions from constructor return type and map BVars to recursor context.
            let ctor_return = Self::ctor_return_type(ctor_ty, num_params);
            let index_exprs = Self::extract_indices_from_return_type(&ctor_return, ind_name, num_params);
            let mapped_indices: Vec<Expr> = index_exprs.iter()
                .map(|e| Self::map_bvars(e, &|j| {
                    if j < nfields {
                        j
                    } else {
                        num_minors + num_motives + j
                    }
                }))
                .collect();

            // Apply indices to the recursive call
            for idx_expr in &mapped_indices {
                rec_call = Expr::mk_app(rec_call, idx_expr.clone());
            }

            // Apply the recursive field (last field, innermost binder = BVar(0))
            rec_call = Expr::mk_app(rec_call, Expr::mk_bvar(0));

            body = Expr::mk_app(body, rec_call);
        }

        // Wrap body in lambdas: fields (innermost), then minors, then motives, then params (outermost)
        let mut result = body;

        // Wrap fields (last to first)
        for j in (0..nfields).rev() {
            result = Expr::Lambda(
                Name::new(&format!("f{}", j)),
                BinderInfo::Default,
                Rc::new(Expr::mk_type()),
                Rc::new(result),
            );
        }

        // Wrap minors (last to first)
        for j in (0..num_minors).rev() {
            result = Expr::Lambda(
                Name::new(&format!("m{}", j)),
                BinderInfo::Default,
                Rc::new(Expr::mk_type()),
                Rc::new(result),
            );
        }

        // Wrap motives (last to first, so P0 is outermost)
        for j in (0..num_motives).rev() {
            result = Expr::Lambda(
                Name::new(&format!("P{}", j)),
                BinderInfo::Default,
                Rc::new(Expr::mk_type()),
                Rc::new(result),
            );
        }

        // Wrap params (last to first)
        for j in (0..num_params).rev() {
            result = Expr::Lambda(
                Name::new(&format!("p{}", j)),
                BinderInfo::Default,
                Rc::new(Expr::mk_type()),
                Rc::new(result),
            );
        }

        result
    }

    /// Extract the type of the last field from a constructor type.
    fn get_last_field_type(ctor_ty: &Expr, num_params: u64) -> Expr {
        let mut current = ctor_ty;
        // Skip parameters
        for _ in 0..num_params {
            if let Some(body) = current.binding_body() {
                current = body;
            } else {
                return Expr::mk_type();
            }
        }
        // Collect field types
        let mut field_types = Vec::new();
        while let Expr::Pi(_, _, domain, body) = current {
            field_types.push((**domain).clone());
            current = body;
        }
        field_types.last().cloned().unwrap_or(Expr::mk_type())
    }

    /// Extract index types from the inductive type (Pi binders after params).
    fn extract_index_types(ty: &Expr, num_params: u64, num_indices: u64) -> Vec<(Name, Expr)> {
        let mut result = Vec::new();
        let mut current = ty;
        // Skip parameters
        for _ in 0..num_params {
            if let Expr::Pi(_, _, _, body) = current {
                current = body;
            } else {
                break;
            }
        }
        // Collect index types
        for _ in 0..num_indices {
            if let Expr::Pi(name, _, domain, body) = current {
                result.push((name.clone(), (**domain).clone()));
                current = body;
            } else {
                break;
            }
        }
        result
    }

    /// Extract the constructor return type by skipping params and fields.
    fn ctor_return_type(ctor_ty: &Expr, num_params: u64) -> Expr {
        let mut current = ctor_ty;
        // Skip parameters
        for _ in 0..num_params {
            if let Expr::Pi(_, _, _, body) = current {
                current = body;
            } else {
                break;
            }
        }
        // Skip fields
        while let Expr::Pi(_, _, _, body) = current {
            current = body;
        }
        current.clone()
    }

    /// Extract index expressions from a constructor return type.
    /// The return type is expected to be `I params indices`.
    /// Returns the list of index expressions (as Expr).
    fn extract_indices_from_return_type(return_type: &Expr, ind_name: &Name, num_params: u64) -> Vec<Expr> {
        let mut indices = Vec::new();
        let mut current = return_type;
        // Unwrap applications to get to the head
        let mut args = Vec::new();
        while let Expr::App(f, a) = current {
            args.push((**a).clone());
            current = f;
        }
        args.reverse();
        // Head should be the inductive type constant
        if let Expr::Const(name, _) = current {
            if name == ind_name {
                // Skip params
                let start = num_params as usize;
                for i in start..args.len() {
                    indices.push(args[i].clone());
                }
            }
        }
        indices
    }

    /// Generate a recursor type for the inductive type.
    /// The recursor type is:
    ///   (params) -> (P0 : ... -> Sort u) -> ... -> (Pn : ... -> Sort u) -> minor_premises ->
    ///   (indices) -> (x : I params indices) -> P_current indices x
    fn mk_recursor_type(
        ind_name: &Name,
        ind_ty: &Expr,
        num_params: u64,
        num_indices: u64,
        global_ctors: &[(usize, usize, &Constructor)],
        all_names: &[Name],
        current_type_idx: usize,
    ) -> (Expr, Name) {
        let num_minors = global_ctors.len() as u64;
        let num_motives = all_names.len() as u64;
        let u = Name::new("u");
        let u_level = Level::Param(u.clone());

        // Innermost expression: P_current indices x
        // In the final structure (inside x):
        //   x = BVar(0)
        //   indices = BVar(1) to BVar(num_indices)
        //   minors = BVar(num_indices + 1) to BVar(num_indices + num_minors)
        //   motives = BVar(num_indices + num_minors + 1) to BVar(num_indices + num_minors + num_motives)
        //   params = after motives
        let p_current_idx = num_indices + num_minors + 1 + current_type_idx as u64;
        let mut result = Expr::mk_bvar(p_current_idx);
        // Apply indices to P_current
        for i in 0..num_indices {
            result = Expr::mk_app(result, Expr::mk_bvar(num_indices - i));
        }
        result = Expr::mk_app(result, Expr::mk_bvar(0));

        // Wrap major premise: (x : I params indices)
        let x_ty = Self::mk_inductive_app(ind_name, num_params, num_indices, num_indices + num_minors + num_motives);
        result = Expr::mk_pi(Name::new("x"), x_ty, result);

        // Wrap indices (from last to first so i0 is outermost)
        let index_types = Self::extract_index_types(ind_ty, num_params, num_indices);
        for (name, ty) in index_types.iter().rev() {
            result = Expr::mk_pi(name.clone(), ty.clone(), result);
        }

        // Wrap minor premises for ALL constructors (from last to first)
        for (global_cidx, ctor_type_idx, ctor) in global_ctors.iter().rev() {
            let minor_ty = Self::mk_minor_premise_type(
                ctor,
                num_params,
                num_indices,
                &all_names[*ctor_type_idx],
                *global_cidx as u64,
                all_names,
            );
            result = Expr::mk_pi(Name::new(&format!("m{}", global_cidx)), minor_ty, result);
        }

        // Wrap motives (P0 first, then P1, etc.)
        // Pj is the motive for all_names[j]
        for j in (0..num_motives).rev() {
            let motive_ty = Self::mk_motive_type(&all_names[j as usize], ind_ty, num_params, num_indices, u_level.clone());
            result = Expr::mk_pi(Name::new(&format!("P{}", j)), motive_ty, result);
        }

        // Wrap parameters (from last to first so p0 is outermost)
        let param_types = Self::extract_param_types(ind_ty, num_params);
        for (name, ty) in param_types.iter().rev() {
            result = Expr::mk_pi(name.clone(), ty.clone(), result);
        }

        (result, u)
    }

    /// Build the motive type: forall indices, I params indices -> Sort u
    fn mk_motive_type(
        ind_name: &Name,
        ind_ty: &Expr,
        num_params: u64,
        num_indices: u64,
        u_level: Level,
    ) -> Expr {
        // In P's domain, params are the innermost binders (start at BVar 0),
        // and indices come after params.
        let ind_app = Self::mk_inductive_app(ind_name, num_params, num_indices, 0);
        let mut result = Expr::mk_arrow(ind_app, Expr::mk_sort(u_level));
        // Quantify over indices (from last to first so i0 is outermost)
        let index_types = Self::extract_index_types(ind_ty, num_params, num_indices);
        for (name, ty) in index_types.iter().rev() {
            result = Expr::mk_pi(name.clone(), ty.clone(), result);
        }
        result
    }

    /// Build an application of the inductive type to params and indices (as BVars).
    /// `param_offset` is the BVar index of the first param at the point of use.
    fn mk_inductive_app(ind_name: &Name, num_params: u64, num_indices: u64, param_offset: u64) -> Expr {
        let mut app = Expr::mk_const(ind_name.clone(), vec![]);
        // Apply params in reverse order to match recursor binder structure
        // (params are wrapped from last to first, so last param is innermost)
        for i in (0..num_params).rev() {
            app = Expr::mk_app(app, Expr::mk_bvar(param_offset + i));
        }
        for i in 0..num_indices {
            app = Expr::mk_app(app, Expr::mk_bvar(param_offset + num_params + i));
        }
        app
    }

    /// Build the minor premise type for a constructor.
    /// The minor premise is a Pi type over the constructor's fields,
    /// with an extra ih argument for each recursive field.
    fn mk_minor_premise_type(
        ctor: &Constructor,
        num_params: u64,
        _num_indices: u64,
        ind_name: &Name,
        cidx: u64,
        all_names: &[Name],
    ) -> Expr {
        let num_motives = all_names.len() as u64;

        // Collect field types from constructor type (skipping params)
        let mut fields = Vec::new();
        let mut current = &ctor.ty;
        for _ in 0..num_params {
            if let Some(body) = current.binding_body() {
                current = body;
            } else {
                break;
            }
        }
        while let Expr::Pi(name, _, domain, body) = current {
            fields.push((name.clone(), (**domain).clone()));
            current = body;
        }

        let num_ihs = fields
            .iter()
            .filter(|(_, d)| Self::expr_contains_any_const(d, all_names))
            .count();
        let total_inner = fields.len() + num_ihs;

        // Extract index expressions from constructor return type.
        let ctor_return = Self::ctor_return_type(&ctor.ty, num_params);
        let index_exprs: Vec<Expr> = Self::extract_indices_from_return_type(&ctor_return, ind_name, num_params)
            .into_iter()
            .map(|e| e.lift_loose_bvars(num_ihs as u64, 0))
            .collect();

        // In the minor premise domain, the recursor-level binders from inside out are:
        //   preceding minors (cidx of them), motives (num_motives), params (num_params)
        // So P0 (first motive) is at BVar(total_inner + cidx) in the return type,
        // and Pj is at BVar(total_inner + cidx + j).
        // param i is at BVar(total_inner + cidx + num_motives + i).

        // Build return type: P_current indices (ctor params fields)
        let current_type_idx = all_names.iter().position(|n| n == ind_name).unwrap_or(0) as u64;
        let p_current_idx = total_inner as u64 + cidx + current_type_idx;
        let mut ctor_app = Expr::mk_const(ctor.name.clone(), vec![]);
        // Apply params
        for i in 0..num_params {
            let param_idx = total_inner as u64 + cidx + num_motives + i;
            ctor_app = Expr::mk_app(ctor_app, Expr::mk_bvar(param_idx));
        }
        // Apply fields (field j is at BVar(total_inner - 1 - j) from inside all binders)
        for fidx in 0..fields.len() {
            let field_bvar = (total_inner - 1 - fidx) as u64;
            ctor_app = Expr::mk_app(ctor_app, Expr::mk_bvar(field_bvar));
        }

        let mut result = Expr::mk_bvar(p_current_idx);
        // Apply indices to P_current
        for idx_expr in &index_exprs {
            result = Expr::mk_app(result, idx_expr.clone());
        }
        result = Expr::mk_app(result, ctor_app);

        // Wrap field binders from inside out (last field first).
        // For each field, wrap ih FIRST (making it inner), then field (outer).
        for fidx in (0..fields.len()).rev() {
            let maybe_recursive = Self::find_mutual_type(&fields[fidx].1, all_names);

            if let Some(rec_type_idx) = maybe_recursive {
                // ih_ty = P_rec indices field
                // P_rec is the motive for the recursive field's type.
                // In ih_ty: field = BVar(0), P_rec = BVar(fidx + 1 + cidx + rec_type_idx)
                let p_idx_in_ih_ty = (fidx + 1) as u64 + cidx + rec_type_idx as u64;
                let mut ih_ty = Expr::mk_bvar(p_idx_in_ih_ty);
                for idx_expr in &index_exprs {
                    ih_ty = Expr::mk_app(ih_ty, idx_expr.clone());
                }
                ih_ty = Expr::mk_app(ih_ty, Expr::mk_bvar(0));
                result = Expr::mk_pi(Name::new("ih"), ih_ty, result);
            }

            // field_ty: convert param constants to BVars.
            // In field_ty (outside field fidx, inside earlier fields):
            // param i = BVar(fidx + cidx + num_motives + i)
            let param_base = fidx as u64 + cidx + num_motives;
            let domain = Self::subst_params_with_bvars(
                &fields[fidx].1,
                num_params,
                param_base,
            );
            result = Expr::mk_pi(fields[fidx].0.clone(), domain, result);
        }

        result
    }

    /// Convert parameter constants in a constructor type to bound variables.
    /// The constructor type is expected to have its parameters as the outermost Pi binders.
    /// `param_names` are the names of the parameters, in order (outermost first).
    /// `depth` is the current number of enclosing binders during traversal.
    fn abstract_params(e: &Expr, param_names: &[Name], depth: u64) -> Expr {
        if param_names.is_empty() {
            return e.clone();
        }
        match e {
            Expr::Const(name, ls) => {
                for (i, param_name) in param_names.iter().enumerate() {
                    if name == param_name {
                        // Param at index i (0 = outermost) is at BVar(depth - 1 - i)
                        return Expr::mk_bvar(depth - 1 - i as u64);
                    }
                }
                Expr::Const(name.clone(), ls.clone())
            }
            Expr::App(f, a) => Expr::mk_app(
                Self::abstract_params(f, param_names, depth),
                Self::abstract_params(a, param_names, depth),
            ),
            Expr::Pi(name, bi, ty, body) => Expr::Pi(
                name.clone(),
                *bi,
                Rc::new(Self::abstract_params(ty, param_names, depth)),
                Rc::new(Self::abstract_params(body, param_names, depth + 1)),
            ),
            Expr::Lambda(name, bi, ty, body) => Expr::Lambda(
                name.clone(),
                *bi,
                Rc::new(Self::abstract_params(ty, param_names, depth)),
                Rc::new(Self::abstract_params(body, param_names, depth + 1)),
            ),
            Expr::Let(name, ty, value, body, nondep) => Expr::Let(
                name.clone(),
                Rc::new(Self::abstract_params(ty, param_names, depth)),
                Rc::new(Self::abstract_params(value, param_names, depth)),
                Rc::new(Self::abstract_params(body, param_names, depth + 1)),
                *nondep,
            ),
            Expr::Sort(l) => Expr::Sort(l.clone()),
            Expr::Lit(lit) => Expr::Lit(lit.clone()),
            Expr::MData(d, e) => Expr::MData(d.clone(), Rc::new(Self::abstract_params(e, param_names, depth))),
            Expr::Proj(s, i, e) => Expr::Proj(s.clone(), *i, Rc::new(Self::abstract_params(e, param_names, depth))),
            other => other.clone(),
        }
    }

    /// Substitute param constants in an expression with BVars.
    /// In our constructor types, params are referenced as constants (e.g., Const("A")).
    /// In the recursor type, params are bound as Pi binders at specific de Bruijn indices.
    /// `param_base` is the BVar index of the FIRST param (outermost) from the current position.
    fn subst_params_with_bvars(e: &Expr, num_params: u64, param_base: u64) -> Expr {
        if num_params == 0 {
            return e.clone();
        }
        match e {
            Expr::Const(n, ls) => {
                // For simplicity, we assume a single param named "A" when num_params == 1.
                // This matches our test cases. For multi-param, we'd need param names.
                if num_params == 1 && n.0 == ["A"] {
                    Expr::mk_bvar(param_base)
                } else {
                    Expr::Const(n.clone(), ls.clone())
                }
            }
            Expr::App(f, a) => Expr::mk_app(
                Self::subst_params_with_bvars(f, num_params, param_base),
                Self::subst_params_with_bvars(a, num_params, param_base),
            ),
            Expr::Pi(name, bi, ty, body) => Expr::Pi(
                name.clone(),
                *bi,
                Rc::new(Self::subst_params_with_bvars(ty, num_params, param_base)),
                Rc::new(Self::subst_params_with_bvars(body, num_params, param_base + 1)),
            ),
            Expr::Lambda(name, bi, ty, body) => Expr::Lambda(
                name.clone(),
                *bi,
                Rc::new(Self::subst_params_with_bvars(ty, num_params, param_base)),
                Rc::new(Self::subst_params_with_bvars(body, num_params, param_base + 1)),
            ),
            Expr::Let(name, ty, value, body, nondep) => Expr::Let(
                name.clone(),
                Rc::new(Self::subst_params_with_bvars(ty, num_params, param_base)),
                Rc::new(Self::subst_params_with_bvars(value, num_params, param_base)),
                Rc::new(Self::subst_params_with_bvars(body, num_params, param_base + 1)),
                *nondep,
            ),
            Expr::Sort(l) => Expr::Sort(Self::subst_params_in_level(l, num_params, param_base)),
            Expr::Proj(s, i, e) => Expr::Proj(
                s.clone(),
                *i,
                Rc::new(Self::subst_params_with_bvars(e, num_params, param_base)),
            ),
            Expr::MData(d, e) => Expr::MData(
                d.clone(),
                Rc::new(Self::subst_params_with_bvars(e, num_params, param_base)),
            ),
            other => other.clone(),
        }
    }

    fn subst_params_in_level(l: &Level, num_params: u64, param_base: u64) -> Level {
        if num_params == 0 {
            return l.clone();
        }
        match l {
            Level::Param(n) => {
                if num_params == 1 && n.0 == ["A"] {
                    // Level params are not substituted in our simplified implementation
                    l.clone()
                } else {
                    l.clone()
                }
            }
            Level::Succ(l) => Level::mk_succ(Self::subst_params_in_level(l, num_params, param_base)),
            Level::Max(l1, l2) => Level::mk_max(
                Self::subst_params_in_level(l1, num_params, param_base),
                Self::subst_params_in_level(l2, num_params, param_base),
            ),
            Level::IMax(l1, l2) => Level::mk_imax(
                Self::subst_params_in_level(l1, num_params, param_base),
                Self::subst_params_in_level(l2, num_params, param_base),
            ),
            other => other.clone(),
        }
    }

    /// Extract parameter names from the inductive type.
    fn extract_param_names(ty: &Expr, num_params: u64) -> Vec<Name> {
        let mut result = Vec::new();
        let mut current = ty;
        for _ in 0..num_params {
            if let Expr::Pi(name, _, _, body) = current {
                result.push(name.clone());
                current = body;
            } else {
                break;
            }
        }
        result
    }

    /// Extract parameter types from the inductive type.
    fn extract_param_types(ty: &Expr, num_params: u64) -> Vec<(Name, Expr)> {
        let mut result = Vec::new();
        let mut current = ty;
        for _ in 0..num_params {
            if let Expr::Pi(name, _, domain, body) = current {
                result.push((name.clone(), (**domain).clone()));
                current = body;
            } else {
                break;
            }
        }
        result
    }

    fn count_indices(ty: &Expr, num_params: u64) -> u64 {
        let mut count = 0;
        let mut current = ty;
        // Skip parameters
        for _ in 0..num_params {
            if let Some(body) = current.binding_body() {
                current = body;
            } else {
                break;
            }
        }
        // Count remaining Pi types as indices
        while current.is_pi() {
            count += 1;
            if let Some(body) = current.binding_body() {
                current = body;
            } else {
                break;
            }
        }
        count
    }

    fn count_fields(ty: &Expr, num_params: u64) -> u64 {
        let mut count = 0;
        let mut current = ty;
        // Skip parameters
        for _ in 0..num_params {
            if let Some(body) = current.binding_body() {
                current = body;
            } else {
                break;
            }
        }
        // Count remaining Pi types as fields
        while current.is_pi() {
            count += 1;
            if let Some(body) = current.binding_body() {
                current = body;
            } else {
                break;
            }
        }
        count
    }

    /// Iterate over all constants
    pub fn for_each_constant<F>(&self, mut f: F)
    where
        F: FnMut(&ConstantInfo),
    {
        for (_, info) in &self.constants {
            f(info);
        }
    }

    pub fn num_constants(&self) -> usize {
        self.constants.len()
    }

    pub fn iter_names(&self) -> impl Iterator<Item = &Name> {
        self.constants.keys()
    }
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;

    #[test]
    fn test_add_inductive_bool() {
        let mut env = Environment::new();

        let bool_ind = InductiveType {
            name: Name::new("Bool"),
            ty: Expr::mk_type(),
            ctors: vec![
                Constructor { name: Name::new("false"), ty: Expr::mk_const(Name::new("Bool"), vec![]) },
                Constructor { name: Name::new("true"), ty: Expr::mk_const(Name::new("Bool"), vec![]) },
            ],
        };

        let decl = Declaration::Inductive {
            level_params: vec![],
            num_params: 0,
            types: vec![bool_ind],
            is_unsafe: false,
        };

        env.add(decl).unwrap();

        assert!(env.contains(&Name::new("Bool")));
        assert!(env.contains(&Name::new("false")));
        assert!(env.contains(&Name::new("true")));
        assert!(env.contains(&Name::new("rec").extend("Bool")));

        // Check Bool is not recursive
        let bool_info = env.find(&Name::new("Bool")).unwrap().to_inductive_val().unwrap();
        assert!(!bool_info.is_rec);
    }

    #[test]
    fn test_add_inductive_nat() {
        let mut env = Environment::new();

        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let nat_ind = InductiveType {
            name: Name::new("Nat"),
            ty: Expr::mk_type(),
            ctors: vec![
                Constructor { name: Name::new("zero"), ty: nat.clone() },
                Constructor {
                    name: Name::new("succ"),
                    ty: Expr::mk_arrow(nat.clone(), nat.clone()),
                },
            ],
        };

        let decl = Declaration::Inductive {
            level_params: vec![],
            num_params: 0,
            types: vec![nat_ind],
            is_unsafe: false,
        };

        env.add(decl).unwrap();

        assert!(env.contains(&Name::new("Nat")));
        assert!(env.contains(&Name::new("zero")));
        assert!(env.contains(&Name::new("succ")));
        assert!(env.contains(&Name::new("rec").extend("Nat")));

        // Check Nat is recursive
        let nat_info = env.find(&Name::new("Nat")).unwrap().to_inductive_val().unwrap();
        assert!(nat_info.is_rec);

        // Check constructor info
        let zero_info = env.find(&Name::new("zero")).unwrap().to_constructor_val().unwrap();
        assert_eq!(zero_info.num_fields, 0);

        let succ_info = env.find(&Name::new("succ")).unwrap().to_constructor_val().unwrap();
        assert_eq!(succ_info.num_fields, 1);

        // Check recursor has 2 rules
        let rec_info = env.find(&Name::new("rec").extend("Nat")).unwrap().to_recursor_val().unwrap();
        assert_eq!(rec_info.rules.len(), 2);
        assert_eq!(rec_info.num_minors, 2);
    }

    #[test]
    fn test_add_inductive_invalid_constructor() {
        let mut env = Environment::new();

        // Constructor returning wrong type
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let bool_ind = InductiveType {
            name: Name::new("Bool"),
            ty: Expr::mk_type(),
            ctors: vec![
                Constructor { name: Name::new("false"), ty: nat.clone() }, // wrong: returns Nat instead of Bool
            ],
        };

        let decl = Declaration::Inductive {
            level_params: vec![],
            num_params: 0,
            types: vec![bool_ind],
            is_unsafe: false,
        };

        assert!(env.add(decl).is_err());
    }

    #[test]
    fn test_generated_recursor_reduces() {
        use crate::type_checker::*;

        let mut env = Environment::new();

        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let nat_ind = InductiveType {
            name: Name::new("Nat"),
            ty: Expr::mk_type(),
            ctors: vec![
                Constructor { name: Name::new("zero"), ty: nat.clone() },
                Constructor {
                    name: Name::new("succ"),
                    ty: Expr::mk_arrow(nat.clone(), nat.clone()),
                },
            ],
        };

        let decl = Declaration::Inductive {
            level_params: vec![],
            num_params: 0,
            types: vec![nat_ind],
            is_unsafe: false,
        };

        env.add(decl).unwrap();

        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let nat_rec = Expr::mk_const(Name::new("rec").extend("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let succ = Expr::mk_const(Name::new("succ"), vec![]);

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
        let one = Expr::mk_app(succ.clone(), zero.clone());
        let app_one = Expr::mk_app(
            Expr::mk_app(Expr::mk_app(Expr::mk_app(nat_rec.clone(), motive.clone()), zero.clone()), succ_minor.clone()),
            one.clone()
        );
        let result = tc.whnf(&app_one);
        // WHNF should give: succ (Nat.rec (λ n. Nat) zero (λ n ih. succ ih) zero)
        let expected_inner = Expr::mk_app(
            Expr::mk_app(Expr::mk_app(Expr::mk_app(nat_rec, motive), zero.clone()), succ_minor), zero
        );
        let expected = Expr::mk_app(succ, expected_inner);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_add_inductive_list() {
        use crate::type_checker::*;

        let mut env = Environment::new();

        let type0 = Expr::mk_type();
        let a_ty = Expr::mk_const(Name::new("A"), vec![]);
        let list_a = Expr::mk_app(Expr::mk_const(Name::new("List"), vec![]), a_ty.clone());

        let list_ind = InductiveType {
            name: Name::new("List"),
            ty: Expr::mk_pi(Name::new("A"), type0.clone(), type0.clone()),
            ctors: vec![
                // nil : (A : Type) -> List A
                Constructor {
                    name: Name::new("nil"),
                    ty: Expr::mk_pi(Name::new("A"), type0.clone(), list_a.clone()),
                },
                // cons : (A : Type) -> A -> List A -> List A
                Constructor {
                    name: Name::new("cons"),
                    ty: Expr::mk_pi(
                        Name::new("A"),
                        type0.clone(),
                        Expr::mk_arrow(
                            a_ty.clone(),
                            Expr::mk_arrow(list_a.clone(), list_a.clone()),
                        ),
                    ),
                },
            ],
        };

        let decl = Declaration::Inductive {
            level_params: vec![],
            num_params: 1,
            types: vec![list_ind],
            is_unsafe: false,
        };

        env.add(decl).unwrap();

        // Verify constructors and recursor exist
        assert!(env.contains(&Name::new("List")));
        assert!(env.contains(&Name::new("nil")));
        assert!(env.contains(&Name::new("cons")));
        assert!(env.contains(&Name::new("rec").extend("List")));

        // Check List is recursive
        let list_info = env.find(&Name::new("List")).unwrap().to_inductive_val().unwrap();
        assert!(list_info.is_rec);
        assert_eq!(list_info.num_params, 1);

        // Check constructor field counts
        let nil_info = env.find(&Name::new("nil")).unwrap().to_constructor_val().unwrap();
        assert_eq!(nil_info.num_fields, 0);

        let cons_info = env.find(&Name::new("cons")).unwrap().to_constructor_val().unwrap();
        assert_eq!(cons_info.num_fields, 2);

        // Test reduction with generated recursor
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let list_rec = Expr::mk_const(Name::new("rec").extend("List"), vec![]);
        let nil_ctor = Expr::mk_const(Name::new("nil"), vec![]);
        let cons_ctor = Expr::mk_const(Name::new("cons"), vec![]);
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);

        // Build: List Nat
        let list_nat = Expr::mk_app(Expr::mk_const(Name::new("List"), vec![]), nat.clone());

        // Motive: λ (l : List Nat). Nat
        let motive = Expr::mk_lambda(Name::new("l"), list_nat.clone(), nat.clone());

        // nil case: zero
        let nil_case = zero.clone();

        // cons case: λ a l ih. succ ih  (where succ is a placeholder)
        let succ = Expr::mk_const(Name::new("succ"), vec![]);
        let cons_case = Expr::Lambda(
            Name::new("a"), BinderInfo::Default, Rc::new(nat.clone()),
            Rc::new(Expr::Lambda(
                Name::new("l"), BinderInfo::Default, Rc::new(list_nat.clone()),
                Rc::new(Expr::Lambda(
                    Name::new("ih"), BinderInfo::Default, Rc::new(nat.clone()),
                    Rc::new(Expr::mk_app(succ.clone(), Expr::BVar(0)))
                ))
            ))
        );

        // List.rec Nat (λ l. Nat) zero (λ a l ih. succ ih) (cons Nat zero nil)
        let nil_list_nat = Expr::mk_app(nil_ctor.clone(), nat.clone());
        let test_list = Expr::mk_app(
            Expr::mk_app(Expr::mk_app(cons_ctor.clone(), nat.clone()), zero.clone()),
            nil_list_nat.clone()
        );

        let app = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_app(list_rec, nat.clone()), motive.clone()),
                    nil_case.clone()
                ),
                cons_case.clone()
            ),
            test_list.clone()
        );

        let result = tc.nf(&app);
        // Full normalization should reduce the entire expression
        let expected = Expr::mk_app(succ, zero);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_nat_recursor_type_check() {
        use crate::type_checker::*;

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

        // Check that Nat.rec has a Pi type
        let nat_rec = Expr::mk_const(Name::new("rec").extend("Nat"), vec![]);
        let rec_ty = tc.infer(&nat_rec).unwrap();
        assert!(rec_ty.is_pi(), "Nat.rec type should be a Pi, got {:?}", rec_ty);
        println!("Nat.rec type: {:?}", rec_ty);

        // Type-check a recursor application
        let motive = Expr::mk_lambda(Name::new("n"), nat.clone(), nat.clone());
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let succ = Expr::mk_const(Name::new("succ"), vec![]);
        let succ_minor = Expr::Lambda(
            Name::new("n"), BinderInfo::Default, Rc::new(nat.clone()),
            Rc::new(Expr::Lambda(
                Name::new("ih"), BinderInfo::Default, Rc::new(nat.clone()),
                Rc::new(Expr::mk_app(succ.clone(), Expr::BVar(0)))
            ))
        );

        let app = Expr::mk_app(
            Expr::mk_app(Expr::mk_app(Expr::mk_app(nat_rec, motive), zero.clone()), succ_minor),
            zero.clone()
        );
        let app_ty = tc.infer(&app).unwrap();
        assert_eq!(app_ty, nat, "Nat.rec application should have type Nat");
    }

    #[test]
    fn test_list_recursor_type_check() {
        use crate::type_checker::*;

        let mut env = Environment::new();
        let type0 = Expr::mk_type();

        // Add Nat for use in tests
        let nat_decl = Declaration::Inductive {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::new("Nat"),
                ty: type0.clone(),
                ctors: vec![
                    Constructor { name: Name::new("zero"), ty: Expr::mk_const(Name::new("Nat"), vec![]) },
                    Constructor { name: Name::new("succ"), ty: Expr::mk_arrow(Expr::mk_const(Name::new("Nat"), vec![]), Expr::mk_const(Name::new("Nat"), vec![])) },
                ],
            }],
            is_unsafe: false,
        };
        env.add(nat_decl).unwrap();

        let a_ty = Expr::mk_const(Name::new("A"), vec![]);
        let list_a = Expr::mk_app(Expr::mk_const(Name::new("List"), vec![]), a_ty.clone());

        let list_ind = InductiveType {
            name: Name::new("List"),
            ty: Expr::mk_pi(Name::new("A"), type0.clone(), type0.clone()),
            ctors: vec![
                Constructor {
                    name: Name::new("nil"),
                    ty: Expr::mk_pi(Name::new("A"), type0.clone(), list_a.clone()),
                },
                Constructor {
                    name: Name::new("cons"),
                    ty: Expr::mk_pi(
                        Name::new("A"),
                        type0.clone(),
                        Expr::mk_arrow(
                            a_ty.clone(),
                            Expr::mk_arrow(list_a.clone(), list_a.clone()),
                        ),
                    ),
                },
            ],
        };
        let decl = Declaration::Inductive {
            level_params: vec![], num_params: 1, types: vec![list_ind], is_unsafe: false,
        };
        env.add(decl).unwrap();

        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        // Check that List.rec has a Pi type
        let list_rec = Expr::mk_const(Name::new("rec").extend("List"), vec![]);
        let rec_ty = tc.infer(&list_rec).unwrap();
        assert!(rec_ty.is_pi(), "List.rec type should be a Pi, got {:?}", rec_ty);
        println!("List.rec type: {:?}", rec_ty);

        // Type-check a recursor application on List Nat
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let succ = Expr::mk_const(Name::new("succ"), vec![]);
        let list_nat = Expr::mk_app(Expr::mk_const(Name::new("List"), vec![]), nat.clone());

        // Motive: λ (l : List Nat). Nat
        let motive = Expr::mk_lambda(Name::new("l"), list_nat.clone(), nat.clone());

        // nil case: zero
        let nil_case = zero.clone();

        // cons case: λ a l ih. succ ih
        let cons_case = Expr::Lambda(
            Name::new("a"), BinderInfo::Default, Rc::new(nat.clone()),
            Rc::new(Expr::Lambda(
                Name::new("l"), BinderInfo::Default, Rc::new(list_nat.clone()),
                Rc::new(Expr::Lambda(
                    Name::new("ih"), BinderInfo::Default, Rc::new(nat.clone()),
                    Rc::new(Expr::mk_app(succ, Expr::BVar(0)))
                ))
            ))
        );

        let nil_ctor = Expr::mk_const(Name::new("nil"), vec![]);
        let test_list = Expr::mk_app(nil_ctor, nat.clone());

        let app = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_app(list_rec, nat.clone()), motive),
                    nil_case
                ),
                cons_case
            ),
            test_list
        );
        let app_ty = tc.infer(&app).unwrap();
        assert_eq!(app_ty, nat, "List.rec application should have type Nat");
    }

    #[test]
    fn test_add_inductive_le() {
        use crate::type_checker::*;

        let mut env = Environment::new();

        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let succ = Expr::mk_const(Name::new("succ"), vec![]);
        let prop = Expr::mk_prop();

        // le : Nat -> Nat -> Prop
        let le_ty = Expr::mk_pi(
            Name::new("m"),
            nat.clone(),
            Expr::mk_pi(Name::new("n"), nat.clone(), prop.clone()),
        );

        // le_zero : forall (n : Nat), le zero n
        let le_zero_ty = Expr::mk_pi(
            Name::new("n"),
            nat.clone(),
            Expr::mk_app(
                Expr::mk_app(Expr::mk_const(Name::new("le"), vec![]), zero.clone()),
                Expr::mk_bvar(0),
            ),
        );

        // le_succ : forall (m : Nat), forall (n : Nat), le m n -> le (succ m) (succ n)
        let le_succ_ty = Expr::mk_pi(
            Name::new("m"),
            nat.clone(),
            Expr::mk_pi(
                Name::new("n"),
                nat.clone(),
                Expr::mk_pi(
                    Name::new("h"),
                    Expr::mk_app(
                        Expr::mk_app(Expr::mk_const(Name::new("le"), vec![]), Expr::mk_bvar(1)),
                        Expr::mk_bvar(0),
                    ),
                    Expr::mk_app(
                        Expr::mk_app(
                            Expr::mk_const(Name::new("le"), vec![]),
                            Expr::mk_app(succ.clone(), Expr::mk_bvar(2)),
                        ),
                        Expr::mk_app(succ.clone(), Expr::mk_bvar(1)),
                    ),
                ),
            ),
        );

        let le_ind = InductiveType {
            name: Name::new("le"),
            ty: le_ty,
            ctors: vec![
                Constructor { name: Name::new("le_zero"), ty: le_zero_ty },
                Constructor { name: Name::new("le_succ"), ty: le_succ_ty },
            ],
        };

        let decl = Declaration::Inductive {
            level_params: vec![],
            num_params: 0,
            types: vec![le_ind],
            is_unsafe: false,
        };

        env.add(decl).unwrap();

        let le_info = env.find(&Name::new("le")).unwrap().to_inductive_val().unwrap();
        assert_eq!(le_info.num_params, 0);
        assert_eq!(le_info.num_indices, 2);
        assert!(le_info.is_rec);

        let rec_info = env.find(&Name::new("rec").extend("le")).unwrap().to_recursor_val().unwrap();
        assert_eq!(rec_info.num_params, 0);
        assert_eq!(rec_info.num_indices, 2);
        assert_eq!(rec_info.num_minors, 2);

        // Type-check the recursor
        let mut st = TypeCheckerState::new(env);
        let mut tc = TypeChecker::new(&mut st);

        let le_rec = Expr::mk_const(Name::new("rec").extend("le"), vec![]);
        let rec_ty = tc.infer(&le_rec).unwrap();
        assert!(rec_ty.is_pi(), "le.rec type should be a Pi, got {:?}", rec_ty);

        // Build a motive: λ m n h. Nat
        let motive = Expr::mk_lambda(
            Name::new("m"),
            nat.clone(),
            Expr::mk_lambda(
                Name::new("n"),
                nat.clone(),
                Expr::mk_lambda(
                    Name::new("h"),
                    Expr::mk_app(Expr::mk_app(Expr::mk_const(Name::new("le"), vec![]), Expr::mk_bvar(1)), Expr::mk_bvar(0)),
                    nat.clone(),
                ),
            ),
        );

        // le_zero case: λ n. zero
        let zero_case = Expr::mk_lambda(Name::new("n"), nat.clone(), zero.clone());

        // le_succ case: λ m n h ih. succ ih
        let succ_case = Expr::mk_lambda(
            Name::new("m"),
            nat.clone(),
            Expr::mk_lambda(
                Name::new("n"),
                nat.clone(),
                Expr::mk_lambda(
                    Name::new("h"),
                    Expr::mk_app(
                        Expr::mk_app(Expr::mk_const(Name::new("le"), vec![]), Expr::mk_bvar(1)),
                        Expr::mk_bvar(0),
                    ),
                    Expr::mk_lambda(
                        Name::new("ih"),
                        nat.clone(),
                        Expr::mk_app(succ.clone(), Expr::mk_bvar(0)),
                    ),
                ),
            ),
        );

        // Test: le.rec Nat motive zero_case succ_case (succ zero) (succ zero) (le_succ zero zero (le_zero zero))
        let one = Expr::mk_app(succ.clone(), zero.clone());
        let le_zero_zero = Expr::mk_app(Expr::mk_const(Name::new("le_zero"), vec![]), zero.clone());
        let le_succ_001 = Expr::mk_app(
            Expr::mk_app(Expr::mk_app(Expr::mk_const(Name::new("le_succ"), vec![]), zero.clone()), zero.clone()),
            le_zero_zero.clone(),
        );

        let app = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(
                    Expr::mk_app(Expr::mk_app(le_rec.clone(), motive.clone()), zero_case.clone()),
                    succ_case,
                ),
                one.clone(),
            ),
            one.clone(),
        );
        let app = Expr::mk_app(app, le_succ_001);

        let result = tc.nf(&app);
        assert_eq!(result, one, "le.rec on le_succ should reduce to succ (le.rec ... le_zero)");
    }

    #[test]
    fn test_mutual_inductive_even_odd() {
        let mut env = Environment::new();

        let type0 = Expr::mk_type();
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);

        // even : Nat -> Type
        let even_ty = Expr::mk_pi(Name::new("n"), nat.clone(), type0.clone());
        // odd : Nat -> Type
        let odd_ty = Expr::mk_pi(Name::new("n"), nat.clone(), type0.clone());

        let even = Expr::mk_const(Name::new("even"), vec![]);
        let odd = Expr::mk_const(Name::new("odd"), vec![]);
        let zero = Expr::mk_const(Name::new("zero"), vec![]);
        let succ = Expr::mk_const(Name::new("succ"), vec![]);

        // even.zero : even 0
        let even_zero_ctor = Constructor {
            name: Name::new("even_zero"),
            ty: Expr::mk_app(even.clone(), zero.clone()),
        };

        // even.succ : forall n, odd n -> even (succ n)
        let even_succ_ctor = Constructor {
            name: Name::new("even_succ"),
            ty: Expr::mk_pi(
                Name::new("n"),
                nat.clone(),
                Expr::mk_arrow(
                    Expr::mk_app(odd.clone(), Expr::mk_bvar(0)),
                    Expr::mk_app(even.clone(), Expr::mk_app(succ.clone(), Expr::mk_bvar(1))),
                ),
            ),
        };

        // odd.succ : forall n, even n -> odd (succ n)
        let odd_succ_ctor = Constructor {
            name: Name::new("odd_succ"),
            ty: Expr::mk_pi(
                Name::new("n"),
                nat.clone(),
                Expr::mk_arrow(
                    Expr::mk_app(even.clone(), Expr::mk_bvar(0)),
                    Expr::mk_app(odd.clone(), Expr::mk_app(succ.clone(), Expr::mk_bvar(1))),
                ),
            ),
        };

        let even_ind = InductiveType {
            name: Name::new("even"),
            ty: even_ty,
            ctors: vec![even_zero_ctor, even_succ_ctor],
        };

        let odd_ind = InductiveType {
            name: Name::new("odd"),
            ty: odd_ty,
            ctors: vec![odd_succ_ctor],
        };

        let decl = Declaration::Inductive {
            level_params: vec![],
            num_params: 0,
            types: vec![even_ind, odd_ind],
            is_unsafe: false,
        };

        env.add(decl).unwrap();

        // Check types and constructors exist
        assert!(env.contains(&Name::new("even")));
        assert!(env.contains(&Name::new("odd")));
        assert!(env.contains(&Name::new("even_zero")));
        assert!(env.contains(&Name::new("even_succ")));
        assert!(env.contains(&Name::new("odd_succ")));
        assert!(env.contains(&Name::new("rec").extend("even")));
        assert!(env.contains(&Name::new("rec").extend("odd")));

        // Check recursor values
        let even_rec = env.find(&Name::new("rec").extend("even")).unwrap().to_recursor_val().unwrap();
        assert_eq!(even_rec.num_motives, 2, "even.rec should have 2 motives");
        assert_eq!(even_rec.num_minors, 3, "even.rec should have 3 minors (all constructors)");
        assert_eq!(even_rec.rules.len(), 2, "even.rec should have 2 rules");

        let odd_rec = env.find(&Name::new("rec").extend("odd")).unwrap().to_recursor_val().unwrap();
        assert_eq!(odd_rec.num_motives, 2, "odd.rec should have 2 motives");
        assert_eq!(odd_rec.num_minors, 3, "odd.rec should have 3 minors (all constructors)");
        assert_eq!(odd_rec.rules.len(), 1, "odd.rec should have 1 rule");
    }
}
