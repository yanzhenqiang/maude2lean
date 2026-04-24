use super::expr::*;
use std::collections::HashMap;
use std::rc::Rc;

/// Local declaration in the context
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LocalDecl {
    /// cdecl: regular local declaration (hypothesis)
    CDecl {
        index: u64,
        name: Name,
        user_name: Name,
        ty: Expr,
        bi: BinderInfo,
    },
    /// ldecl: let-binding (implementation detail, not in core syntax)
    LDecl {
        index: u64,
        name: Name,
        user_name: Name,
        ty: Expr,
        value: Expr,
    },
}

impl LocalDecl {
    pub fn get_name(&self) -> &Name {
        match self {
            LocalDecl::CDecl { name, .. } | LocalDecl::LDecl { name, .. } => name,
        }
    }

    pub fn get_user_name(&self) -> &Name {
        match self {
            LocalDecl::CDecl { user_name, .. } | LocalDecl::LDecl { user_name, .. } => user_name,
        }
    }

    pub fn get_type(&self) -> &Expr {
        match self {
            LocalDecl::CDecl { ty, .. } | LocalDecl::LDecl { ty, .. } => ty,
        }
    }

    pub fn get_value(&self) -> Option<&Expr> {
        match self {
            LocalDecl::LDecl { value, .. } => Some(value),
            LocalDecl::CDecl { .. } => None,
        }
    }

    pub fn get_info(&self) -> Option<BinderInfo> {
        match self {
            LocalDecl::CDecl { bi, .. } => Some(*bi),
            LocalDecl::LDecl { .. } => None,
        }
    }

    pub fn get_index(&self) -> u64 {
        match self {
            LocalDecl::CDecl { index, .. } | LocalDecl::LDecl { index, .. } => *index,
        }
    }

    /// Create an FVar reference for this local decl
    pub fn mk_ref(&self) -> Expr {
        Expr::mk_fvar(self.get_name().clone())
    }
}

/// Local context for the kernel type checker
#[derive(Debug, Clone)]
pub struct LocalCtx {
    decls: HashMap<Name, LocalDecl>,
    next_index: u64,
    /// Stack of binder names for BVar -> FVar conversion (index 0 = outermost)
    bvar_names: Vec<Name>,
    /// Stack of binder types for BVar lookup (index 0 = outermost)
    bvar_types: Vec<Expr>,
}

impl LocalCtx {
    pub fn new() -> Self {
        LocalCtx {
            decls: HashMap::new(),
            next_index: 0,
            bvar_names: Vec::new(),
            bvar_types: Vec::new(),
        }
    }

    pub fn empty(&self) -> bool {
        self.decls.is_empty()
    }

    /// Convert a BVar index to the corresponding FVar name in the current context
    fn bvar_to_fvar_name(&self, idx: u64) -> Option<Name> {
        let len = self.bvar_names.len();
        if idx as usize >= len {
            return None;
        }
        self.bvar_names.get(len - 1 - idx as usize).cloned()
    }

    /// Replace BVars that refer to outer context binders with FVars.
    pub fn replace_bvars_with_fvars(&self, e: &Expr) -> Expr {
        self.replace_bvars_with_fvars_depth(e, 0)
    }

    fn replace_bvars_with_fvars_depth(&self, e: &Expr, depth: u64) -> Expr {
        match e {
            Expr::BVar(i) => {
                if *i >= depth {
                    let adjusted = *i - depth;
                    if let Some(name) = self.bvar_to_fvar_name(adjusted) {
                        Expr::mk_fvar(name)
                    } else {
                        e.clone()
                    }
                } else {
                    e.clone()
                }
            }
            Expr::App(f, a) => Expr::App(
                Rc::new(self.replace_bvars_with_fvars_depth(f, depth)),
                Rc::new(self.replace_bvars_with_fvars_depth(a, depth)),
            ),
            Expr::Lambda(name, bi, ty, body) => Expr::Lambda(
                name.clone(),
                *bi,
                Rc::new(self.replace_bvars_with_fvars_depth(ty, depth)),
                Rc::new(self.replace_bvars_with_fvars_depth(body, depth + 1)),
            ),
            Expr::Pi(name, bi, ty, body) => Expr::Pi(
                name.clone(),
                *bi,
                Rc::new(self.replace_bvars_with_fvars_depth(ty, depth)),
                Rc::new(self.replace_bvars_with_fvars_depth(body, depth + 1)),
            ),
            Expr::Eq(a, t, u) => Expr::Eq(
                Rc::new(self.replace_bvars_with_fvars_depth(a, depth)),
                Rc::new(self.replace_bvars_with_fvars_depth(t, depth)),
                Rc::new(self.replace_bvars_with_fvars_depth(u, depth)),
            ),
            Expr::Cast(a, b, e, t) => Expr::Cast(
                Rc::new(self.replace_bvars_with_fvars_depth(a, depth)),
                Rc::new(self.replace_bvars_with_fvars_depth(b, depth)),
                Rc::new(self.replace_bvars_with_fvars_depth(e, depth)),
                Rc::new(self.replace_bvars_with_fvars_depth(t, depth)),
            ),
            _ => e.clone(),
        }
    }

    /// Push a binder for BVar lookup.
    pub fn push_bvar(&mut self, name: Name, ty: Expr) {
        let converted_ty = self.replace_bvars_with_fvars(&ty);
        self.bvar_names.push(name);
        self.bvar_types.push(converted_ty);
    }

    /// Pop the innermost binder
    pub fn pop_bvar(&mut self) {
        self.bvar_names.pop();
        self.bvar_types.pop();
    }

    /// Get the type of a bound variable by de Bruijn index.
    pub fn get_bvar_type(&self, idx: u64) -> Option<&Expr> {
        let len = self.bvar_types.len();
        if idx as usize >= len {
            return None;
        }
        self.bvar_types.get(len - 1 - idx as usize)
    }

    /// Add a cdecl (hypothesis)
    pub fn mk_local_decl(&mut self, name: Name, user_name: Name, ty: Expr, bi: BinderInfo) -> LocalDecl {
        let idx = self.next_index;
        self.next_index += 1;
        let decl = LocalDecl::CDecl {
            index: idx,
            name: name.clone(),
            user_name,
            ty,
            bi,
        };
        self.decls.insert(name, decl.clone());
        decl
    }

    /// Add an ldecl (let-binding)
    pub fn mk_let_decl(&mut self, name: Name, user_name: Name, ty: Expr, value: Expr) -> LocalDecl {
        let idx = self.next_index;
        self.next_index += 1;
        let decl = LocalDecl::LDecl {
            index: idx,
            name: name.clone(),
            user_name,
            ty,
            value,
        };
        self.decls.insert(name, decl.clone());
        decl
    }

    /// Find a local declaration by name
    pub fn find_local_decl(&self, name: &Name) -> Option<&LocalDecl> {
        self.decls.get(name)
    }

    /// Get a local declaration by name (panics if not found)
    pub fn get_local_decl(&self, name: &Name) -> &LocalDecl {
        self.decls.get(name).expect("Local declaration not found")
    }

    /// Get the type of an FVar
    pub fn get_type(&self, e: &Expr) -> Option<&Expr> {
        if let Expr::FVar(name) = e {
            self.find_local_decl(name).map(|d| d.get_type())
        } else {
            None
        }
    }

    /// Get the value of an FVar (if it's a let-binding)
    pub fn get_value(&self, e: &Expr) -> Option<&Expr> {
        if let Expr::FVar(name) = e {
            self.find_local_decl(name).and_then(|d| d.get_value())
        } else {
            None
        }
    }

    /// Check if FVar is a let-binding
    pub fn is_let_fvar(&self, e: &Expr) -> bool {
        if let Expr::FVar(name) = e {
            self.find_local_decl(name).map_or(false, |d| d.get_value().is_some())
        } else {
            false
        }
    }

    /// Remove a local declaration
    pub fn clear(&mut self, decl: &LocalDecl) {
        self.decls.remove(decl.get_name());
    }

    /// Iterate over all local declarations
    pub fn iter_decls(&self) -> impl Iterator<Item = &LocalDecl> {
        self.decls.values()
    }

    /// Get the number of local declarations
    pub fn len(&self) -> usize {
        self.decls.len()
    }

    /// Create lambda expression from local declarations
    pub fn mk_lambda(&self, fvars: &[Expr], body: Expr, remove_dead_let: bool) -> Expr {
        let mut result = body;
        for fvar in fvars.iter().rev() {
            if let Expr::FVar(name) = fvar {
                if let Some(decl) = self.find_local_decl(name) {
                    match decl {
                        LocalDecl::CDecl { user_name, ty, bi, .. } => {
                            result = Expr::Lambda(
                                user_name.clone(),
                                *bi,
                                Rc::new(ty.clone()),
                                Rc::new(result),
                            );
                        }
                        LocalDecl::LDecl { user_name, ty, value, .. } => {
                            if !remove_dead_let || result.has_fvar() {
                                // let-binding: inline by substitution in the outer layer.
                                // For now, encode as (λ(x:ty). result) value
                                result = Expr::App(
                                    Rc::new(Expr::Lambda(
                                        user_name.clone(),
                                        BinderInfo::Default,
                                        Rc::new(ty.clone()),
                                        Rc::new(result),
                                    )),
                                    Rc::new(value.clone()),
                                );
                            }
                        }
                    }
                }
            }
        }
        result
    }

    /// Create Pi expression from local declarations
    pub fn mk_pi(&self, fvars: &[Expr], body: Expr, remove_dead_let: bool) -> Expr {
        let mut result = body;
        for fvar in fvars.iter().rev() {
            if let Expr::FVar(name) = fvar {
                if let Some(decl) = self.find_local_decl(name) {
                    match decl {
                        LocalDecl::CDecl { user_name, ty, bi, .. } => {
                            result = Expr::Pi(
                                user_name.clone(),
                                *bi,
                                Rc::new(ty.clone()),
                                Rc::new(result),
                            );
                        }
                        LocalDecl::LDecl { user_name, ty, value, .. } => {
                            if !remove_dead_let || result.has_fvar() {
                                // let-binding in Pi: (λ(x:ty). result) value
                                result = Expr::App(
                                    Rc::new(Expr::Lambda(
                                        user_name.clone(),
                                        BinderInfo::Default,
                                        Rc::new(ty.clone()),
                                        Rc::new(result),
                                    )),
                                    Rc::new(value.clone()),
                                );
                            }
                        }
                    }
                }
            }
        }
        result
    }
}

impl Default for LocalCtx {
    fn default() -> Self {
        Self::new()
    }
}
