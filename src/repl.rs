use super::declaration::*;
use super::environment::Environment;
use super::expr::*;
use super::format::format_expr;
use super::repl_parser::{ParsedDecl, ParsedExpr, Parser as ReplParser};
use super::tactic::TacticEngine;
use super::type_checker::{TypeChecker, TypeCheckerState};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{self, Write};
use std::rc::Rc;

/// Interactive Lean REPL.
///
/// Commands:
///   :env                          Show current environment
///   :load <file.cic>             Load declarations from a file
///   :axiom <name> : <type>        Add an axiom
///   :def <name> := <value>        Add a definition (type inferred)
///   :def <name> : <type> := <value>  Add a definition with explicit type
///   :theorem <name> : <type> := <proof>  Add a theorem
///   :inductive <name> | <ctor> : <type> | ...   Add an inductive type
///   :infer <expr>                 Infer the type of an expression
///   :reduce <expr>                Reduce to weak head normal form
///   :nf <expr>                    Reduce to full normal form
///   :defeq <e1> = <e2>            Check definitional equality
///   :help                         Show this help
///   :quit                         Exit
pub struct Repl {
    env: Environment,
    tc_state: TypeCheckerState,
    /// Mapping from user-defined names to their Expr representations
    env_bindings: HashMap<String, Expr>,
    quiet: bool,
    /// Variables declared at file scope, implicitly added to subsequent def/theorem params
    file_variables: Vec<(String, super::repl_parser::ParsedExpr)>,
    /// User-defined infix operators persisted across files and REPL sessions
    infix_ops: HashMap<String, (i32, String, bool)>,
    /// User-defined notations: symbol -> expansion expression
    notations: HashMap<String, super::repl_parser::ParsedExpr>,
    /// Stack of section scopes for restoring state on end
    section_stack: Vec<SectionScope>,
    /// Track files loaded in the current session to avoid duplicate imports
    loaded_files: HashSet<String>,
}

/// Scope snapshot for section/end
#[derive(Debug, Clone)]
struct SectionScope {
    file_variables: Vec<(String, super::repl_parser::ParsedExpr)>,
    infix_ops: HashMap<String, (i32, String, bool)>,
    notations: HashMap<String, super::repl_parser::ParsedExpr>,
}

/// Represents a nested occurrence: `App(...App(Const(outer_name), args)...)` where the
/// inductive type being defined appears in `args`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct NestedOccurrence {
    outer_name: Name,
    args: Vec<Expr>,
}

impl NestedOccurrence {
    fn to_expr(&self) -> Expr {
        let mut result = Expr::mk_const(self.outer_name.clone(), vec![]);
        for arg in &self.args {
            result = Expr::mk_app(result, arg.clone());
        }
        result
    }
}

/// Find all nested occurrences of `ind_name` in `e`.
/// A nested occurrence is when `ind_name` appears as an argument to another type constructor.
fn find_nested_occurrences(e: &Expr, ind_name: &Name, out: &mut Vec<NestedOccurrence>) {
    match e {
        Expr::App(f, a) => {
            // Check if this application spine has `ind_name` as an argument
            let mut spine: Vec<Expr> = vec![(**a).clone()];
            let mut head = f;
            while let Expr::App(f2, a2) = head.as_ref() {
                spine.push((**a2).clone());
                head = f2;
            }
            spine.reverse();
            if let Expr::Const(cname, _) = head.as_ref() {
                if *cname != *ind_name && spine.iter().any(|arg| contains_const(arg, ind_name)) {
                    out.push(NestedOccurrence {
                        outer_name: cname.clone(),
                        args: spine,
                    });
                    return; // Don't recurse into found occurrences
                }
            }
            // Recurse into subexpressions
            find_nested_occurrences(f, ind_name, out);
            find_nested_occurrences(a, ind_name, out);
        }
        Expr::Lambda(_, _, ty, body) |
        Expr::Pi(_, _, ty, body) => {
            find_nested_occurrences(ty, ind_name, out);
            find_nested_occurrences(body, ind_name, out);
        }
        Expr::Let(_, ty, value, body, _) => {
            find_nested_occurrences(ty, ind_name, out);
            find_nested_occurrences(value, ind_name, out);
            find_nested_occurrences(body, ind_name, out);
        }
        Expr::MData(_, e) |
        Expr::Proj(_, _, e) => {
            find_nested_occurrences(e, ind_name, out);
        }
        _ => {}
    }
}

fn contains_const(e: &Expr, name: &Name) -> bool {
    match e {
        Expr::Const(cname, _) => cname == name,
        Expr::App(f, a) => contains_const(f, name) || contains_const(a, name),
        Expr::Lambda(_, _, ty, body) |
        Expr::Pi(_, _, ty, body) => contains_const(ty, name) || contains_const(body, name),
        Expr::Let(_, ty, value, body, _) => {
            contains_const(ty, name) || contains_const(value, name) || contains_const(body, name)
        }
        Expr::MData(_, e) |
        Expr::Proj(_, _, e) => contains_const(e, name),
        _ => false,
    }
}

impl Repl {
    pub fn new() -> Self {
        let env = Environment::new();
        let tc_state = TypeCheckerState::new(env.clone());
        let mut repl = Repl {
            env,
            tc_state,
            env_bindings: HashMap::new(),
            quiet: false,
            file_variables: Vec::new(),
            infix_ops: HashMap::new(),
            notations: HashMap::new(),
            section_stack: Vec::new(),
            loaded_files: HashSet::new(),
        };
        repl.load_quot();
        repl
    }

    pub fn set_quiet(&mut self, quiet: bool) {
        self.quiet = quiet;
    }

    /// Generate an auxiliary inductive type for a nested occurrence.
    /// Given `App(App(Const(C), arg1), arg2)` where one arg is the inductive type,
    /// creates an inductive that mirrors `C` but with the inductive type fixed.
    fn generate_aux_inductive(&self, occ: &NestedOccurrence, aux_name: &Name) -> Result<InductiveType, String> {
        let info = self.env.find(&occ.outer_name)
            .ok_or_else(|| format!("Nested type constructor not found: {}", occ.outer_name.to_string()))?;
        let ind_val = info.to_inductive_val()
            .ok_or_else(|| format!("Not an inductive type: {}", occ.outer_name.to_string()))?;

        if occ.args.len() != ind_val.num_params as usize {
            return Err(format!(
                "Nested inductive {} applied to {} args but expects {}",
                occ.outer_name.to_string(), occ.args.len(), ind_val.num_params
            ));
        }

        let occ_expr = occ.to_expr();
        let mut aux_ctors = Vec::new();

        for ctor_name in &ind_val.ctors {
            let ctor_info = self.env.find(ctor_name)
                .ok_or_else(|| format!("Constructor not found: {}", ctor_name.to_string()))?;
            let ctor_val = ctor_info.to_constructor_val()
                .ok_or_else(|| format!("Not a constructor: {}", ctor_name.to_string()))?;

            // Apply constructor type to the occurrence args (strip params)
            let applied_ty = ctor_val.constant_val.ty.apply_pi_binders(&occ.args)
                .ok_or_else(|| format!("Constructor {} has fewer parameters than expected", ctor_name.to_string()))?;

            // Replace occurrence with auxiliary name
            let replaced_ty = applied_ty.replace_expr(&occ_expr, &Expr::mk_const(aux_name.clone(), vec![]));

            // Name the auxiliary constructor: aux_name.ctor_name
            let full_ctor_name = aux_name.extend(&ctor_name.to_string());
            aux_ctors.push(Constructor {
                name: full_ctor_name,
                ty: replaced_ty,
            });
        }

        // The auxiliary type lives in Type
        let aux_ty = Expr::Sort(Level::mk_succ(Level::Zero));

        Ok(InductiveType {
            name: aux_name.clone(),
            ty: aux_ty,
            ctors: aux_ctors,
        })
    }

    pub fn check_files(&mut self, files: &[&str]) -> Result<(), String> {
        for filepath in files {
            // Skip if already loaded (e.g., via import from an earlier file)
            if self.loaded_files.contains(*filepath) {
                if !self.quiet {
                    println!("  Skip: {} (already loaded)", filepath);
                }
                continue;
            }
            // Track this file so imports won't reload it
            self.loaded_files.insert(filepath.to_string());
            // Clear file-scoped state for each new file
            self.file_variables.clear();
            self.infix_ops.clear();
            self.notations.clear();
            self.section_stack.clear();
            let contents = fs::read_to_string(filepath)
                .map_err(|e| format!("Cannot read file '{}': {}", filepath, e))?;
            let mut parser = ReplParser::new_with_state(&contents, self.infix_ops.clone(), self.notations.clone());
            let decls = parser.parse_file()
                .map_err(|e| format!("Parse error in '{}': {}", filepath, e))?;

            let count = decls.len();
            for decl in decls {
                self.process_decl(decl)?;
            }
            if !self.quiet {
                println!("  Loaded {} declarations from {}", count, filepath);
            }
        }
        Ok(())
    }

    pub fn run(&mut self) {
        println!("╔═══════════════════════════════════════════════════════════════════════╗");
        println!("║          Lean 4 Kernel Symbolic Execution REPL v0.1                  ║");
        println!("║     Type :help for available commands. Type :quit to exit.          ║");
        println!("╚═══════════════════════════════════════════════════════════════════════╝");
        println!();

        // Pre-populate with axioms only (Nat/Exists/Eq must be defined in .cic files)
        println!("Pre-loaded: propext, choice");
        println!();
        self.load_axioms();

        loop {
            print!("lean> ");
            io::stdout().flush().unwrap();

            let mut input = String::new();
            if io::stdin().read_line(&mut input).is_err() {
                println!("Error reading input.");
                continue;
            }
            // EOF reached, exit cleanly
            if input.is_empty() {
                break;
            }

            let input = input.trim();
            if input.is_empty() {
                continue;
            }

            match self.handle_command(input) {
                Ok(true) => break,
                Ok(false) => {}
                Err(e) => println!("Error: {}", e),
            }
        }
    }

    fn handle_command(&mut self, input: &str) -> Result<bool, String> {
        if input.starts_with(":quit") {
            println!("Goodbye!");
            return Ok(true);
        }

        if input.starts_with(":help") {
            self.print_help();
            return Ok(false);
        }

        if input.starts_with(":env") {
            self.print_env();
            return Ok(false);
        }

        if input.starts_with(":load ") {
            return self.handle_load(&input[6..]).map(|_| false);
        }

        if input.starts_with(":axiom ") {
            return self.handle_axiom(&input[7..]).map(|_| false);
        }

        if input.starts_with(":def ") {
            return self.handle_def(&input[5..]).map(|_| false);
        }

        if input.starts_with(":theorem ") {
            return self.handle_theorem(&input[9..]).map(|_| false);
        }

        if input.starts_with(":inductive ") {
            return self.handle_inductive(&input[11..]).map(|_| false);
        }

        if input.starts_with(":infer ") {
            return self.handle_infer(&input[7..]).map(|_| false);
        }

        if input.starts_with(":reduce ") {
            return self.handle_reduce(&input[8..]).map(|_| false);
        }

        if input.starts_with(":nf ") {
            return self.handle_nf(&input[4..]).map(|_| false);
        }

        if input.starts_with(":defeq ") {
            return self.handle_defeq(&input[7..]).map(|_| false);
        }

        if input.starts_with(":solve ") {
            return self.handle_solve(&input[7..]).map(|_| false);
        }

        // Default: try to infer and reduce the expression
        let expr = self.parse_and_convert(input)?;
        let mut tc = TypeChecker::with_local_ctx(&mut self.tc_state, super::local_ctx::LocalCtx::new());
        match tc.infer(&expr) {
            Ok(ty) => {
                println!("  type: {}", format_expr(&ty));
                let reduced = tc.whnf(&expr);
                println!("  whnf: {}", format_expr(&reduced));
            }
            Err(e) => println!("  type error: {}", e),
        }
        Ok(false)
    }

    fn parse_and_convert(&self, input: &str) -> Result<Expr, String> {
        let mut parser = ReplParser::new_with_state(input, self.infix_ops.clone(), self.notations.clone());
        let parsed = parser.parse_expr()?;
        Ok(parsed.to_expr(&self.env_bindings, &self.env, &mut Vec::new()))
    }

    fn handle_load(&mut self, filepath: &str) -> Result<(), String> {
        // Clear file-scoped state when loading a new file
        self.file_variables.clear();
        self.infix_ops.clear();
        self.notations.clear();
        self.section_stack.clear();
        let contents = fs::read_to_string(filepath)
            .map_err(|e| format!("Cannot read file '{}': {}", filepath, e))?;
        let mut parser = ReplParser::new_with_state(&contents, self.infix_ops.clone(), self.notations.clone());
        let decls = parser.parse_file()
            .map_err(|e| format!("Parse error in '{}': {}", filepath, e))?;

        let count = decls.len();
        for decl in decls {
            self.process_decl(decl)?;
        }
        if !self.quiet {
            println!("  Loaded {} declarations from {}", count, filepath);
        }
        Ok(())
    }

    fn process_import(&mut self, path: String) -> Result<(), String> {
        let mut filepath = format!("{}.cic", path);

        // If not found in current directory, try lib/
        if !std::path::Path::new(&filepath).exists() {
            let alt = format!("lib/{}.cic", path);
            if std::path::Path::new(&alt).exists() {
                filepath = alt;
            }
        }

        // Avoid loading the same file twice in one session
        if self.loaded_files.contains(&filepath) {
            if !self.quiet {
                println!("  Import: {} (already loaded)", filepath);
            }
            return Ok(());
        }
        self.loaded_files.insert(filepath.clone());

        // Save current file-scoped state
        let saved_variables = self.file_variables.clone();
        let saved_infix = self.infix_ops.clone();
        let saved_notations = self.notations.clone();
        let saved_stack = self.section_stack.clone();

        // Track which infix/notation symbols existed before import
        let prev_infix_keys: HashSet<String> = self.infix_ops.keys().cloned().collect();
        let prev_notation_keys: HashSet<String> = self.notations.keys().cloned().collect();

        // Clear file-scoped state for the imported file (infix/notation are inherited)
        self.file_variables.clear();
        self.section_stack.clear();

        let result = (|| {
            let contents = fs::read_to_string(&filepath)
                .map_err(|e| format!("Cannot import '{}': {}", filepath, e))?;
            let mut parser = ReplParser::new_with_state(&contents, self.infix_ops.clone(), self.notations.clone());
            let decls = parser.parse_file()
                .map_err(|e| format!("Parse error in '{}': {}", filepath, e))?;

            let count = decls.len();
            for decl in decls {
                self.process_decl(decl)?;
            }
            if !self.quiet {
                println!("  Import: {} ({} declarations)", filepath, count);
            }
            Ok(())
        })();

        // Collect new infix/notation definitions from imported file
        let imported_infix: HashMap<String, (i32, String, bool)> = self.infix_ops.iter()
            .filter(|(k, _)| !prev_infix_keys.contains(*k))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        let imported_notations: HashMap<String, super::repl_parser::ParsedExpr> = self.notations.iter()
            .filter(|(k, _)| !prev_notation_keys.contains(*k))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();

        // Restore file-scoped state
        self.file_variables = saved_variables;
        self.infix_ops = saved_infix;
        self.notations = saved_notations;
        self.section_stack = saved_stack;

        // Merge exported infix/notation definitions (current file takes precedence)
        for (k, v) in imported_infix {
            self.infix_ops.entry(k).or_insert(v);
        }
        for (k, v) in imported_notations {
            self.notations.entry(k).or_insert(v);
        }

        result
    }

    fn process_decl(&mut self, decl: ParsedDecl) -> Result<(), String> {
        match decl {
            ParsedDecl::Axiom { name, ty } => {
                let ty_expr = ty.to_expr(&self.env_bindings, &self.env, &mut Vec::new());
                let decl = Declaration::Axiom(AxiomVal {
                    constant_val: ConstantVal {
                        name: Name::new(&name),
                        level_params: vec![],
                        ty: ty_expr,
                    },
                    is_unsafe: false,
                });
                self.env.add(decl).map_err(|e| e)?;
                self.tc_state = TypeCheckerState::new(self.env.clone());
                self.env_bindings.insert(name.clone(), Expr::mk_const(Name::new(&name), vec![]));
                if !self.quiet {
                    println!("  Added axiom: {}", name);
                }
                Ok(())
            }
            ParsedDecl::Def { name, params, ret_ty, value } => {
                self.process_def_or_theorem(name, params, ret_ty, value, false)
            }
            ParsedDecl::Theorem { name, params, ret_ty, value } => {
                self.process_def_or_theorem(name, params, Some(ret_ty), value, true)
            }
            ParsedDecl::Solve { name, params, ret_ty, value } => {
                self.process_solve(name, params, ret_ty, value)
            }
            ParsedDecl::Variable { params } => {
                for (name, pty) in params {
                    self.file_variables.push((name, pty));
                }
                if !self.quiet {
                    let vars = self.file_variables.iter()
                        .map(|(n, _)| n.clone())
                        .collect::<Vec<_>>()
                        .join(", ");
                    println!("  Variables: {}", vars);
                }
                Ok(())
            }
            ParsedDecl::Infix { symbol, func_name, precedence, left_assoc } => {
                self.infix_ops.insert(symbol.clone(), (precedence, func_name.clone(), left_assoc));
                if !self.quiet {
                    println!("  Infix: {} => {}", symbol, func_name);
                }
                Ok(())
            }
            ParsedDecl::Notation { symbol, expansion } => {
                self.notations.insert(symbol.clone(), expansion.clone());
                if !self.quiet {
                    println!("  Notation: {} => {:?}", symbol, expansion);
                }
                Ok(())
            }
            ParsedDecl::Section { name } => {
                self.section_stack.push(SectionScope {
                    file_variables: self.file_variables.clone(),
                    infix_ops: self.infix_ops.clone(),
                    notations: self.notations.clone(),
                });
                if !self.quiet {
                    if let Some(n) = name {
                        println!("  Section: {}", n);
                    } else {
                        println!("  Section");
                    }
                }
                Ok(())
            }
            ParsedDecl::End { name } => {
                let scope = self.section_stack.pop()
                    .ok_or("end without matching section")?;
                self.file_variables = scope.file_variables;
                self.infix_ops = scope.infix_ops;
                self.notations = scope.notations;
                if !self.quiet {
                    if let Some(n) = name {
                        println!("  End: {}", n);
                    } else {
                        println!("  End");
                    }
                }
                Ok(())
            }
            ParsedDecl::Import { path } => {
                self.process_import(path)
            }
            ParsedDecl::Inductive { name, ty, ctors, num_params } => {
                // Prepend file-scoped variables as inductive parameters
                let wrapped_ty = self.wrap_with_file_variables(ty);
                let wrapped_ctors: Vec<(String, super::repl_parser::ParsedExpr)> = ctors.into_iter()
                    .map(|(n, t)| (n, self.wrap_with_file_variables(t)))
                    .collect();
                let total_params = num_params + self.file_variables.len();

                let ty_expr = wrapped_ty.to_expr(&self.env_bindings, &self.env, &mut Vec::new());
                let ind_name = Name::new(&name);
                let mut ctor_exprs = Vec::new();
                for (ctor_name, ctor_ty) in &wrapped_ctors {
                    let ctor_ty_expr = ctor_ty.to_expr(&self.env_bindings, &self.env, &mut Vec::new());
                    // Global rule: constructors are always namespaced as Type.ctor.
                    let full_ctor_name = Name::new(&name).extend(ctor_name);
                    ctor_exprs.push(Constructor {
                        name: full_ctor_name,
                        ty: ctor_ty_expr,
                    });
                }

                // Check for nested occurrences of the inductive type in constructor types
                let mut nested = Vec::new();
                for ctor in &ctor_exprs {
                    find_nested_occurrences(&ctor.ty, &ind_name, &mut nested);
                }

                if !nested.is_empty() {
                    // Generate auxiliary types for nested occurrences
                    let mut aux_types = Vec::new();
                    let mut replacements = Vec::new();
                    let mut seen = std::collections::HashSet::new();

                    for occ in nested {
                        if !seen.insert(occ.clone()) {
                            continue;
                        }
                        let aux_name = Name::new(&format!("{}_{}", name, occ.outer_name.to_string()));
                        let aux_type = self.generate_aux_inductive(&occ, &aux_name)?;
                        replacements.push((occ.to_expr(), Expr::mk_const(aux_name.clone(), vec![])));
                        aux_types.push(aux_type);
                    }

                    // Replace nested occurrences in original constructor types
                    let mut new_ctors = Vec::new();
                    for ctor in ctor_exprs {
                        let mut new_ty = ctor.ty;
                        for (occ_expr, aux_expr) in &replacements {
                            new_ty = new_ty.replace_expr(occ_expr, aux_expr);
                        }
                        new_ctors.push(Constructor {
                            name: ctor.name,
                            ty: new_ty,
                        });
                    }

                    let ind = InductiveType {
                        name: ind_name.clone(),
                        ty: ty_expr,
                        ctors: new_ctors,
                    };

                    let mut all_types = vec![ind];
                    all_types.extend(aux_types);

                    let decl = Declaration::Inductive {
                        level_params: vec![],
                        num_params: total_params as u64,
                        types: all_types,
                        is_unsafe: false,
                    };

                    self.env.add(decl).map_err(|e| e)?;
                    self.tc_state = TypeCheckerState::new(self.env.clone());

                    // Register constructors and recursors for all types
                    for t in self.env.find(&ind_name).unwrap().to_inductive_val().unwrap().all.clone() {
                        let info = self.env.find(&t).unwrap();
                        if let Some(ind_val) = info.to_inductive_val() {
                            for ctor_name in &ind_val.ctors {
                                let cn = ctor_name.to_string();
                                self.env_bindings.insert(cn.clone(), Expr::mk_const(ctor_name.clone(), vec![]));
                            }
                        }
                        self.env_bindings.insert(t.to_string(), Expr::mk_const(t.clone(), vec![]));
                        let rec_name = format!("rec.{}", t.to_string());
                        self.env_bindings.insert(rec_name.clone(), Expr::mk_const(Name::new("rec").extend(&t.to_string()), vec![]));
                        if !self.quiet {
                            println!("  Added inductive: {}", t.to_string());
                        }
                    }
                    return Ok(());
                }

                // No nested occurrences: process as simple inductive
                let ind = InductiveType {
                    name: ind_name.clone(),
                    ty: ty_expr,
                    ctors: ctor_exprs,
                };

                let decl = Declaration::Inductive {
                    level_params: vec![],
                    num_params: total_params as u64,
                    types: vec![ind],
                    is_unsafe: false,
                };

                self.env.add(decl).map_err(|e| e)?;
                self.tc_state = TypeCheckerState::new(self.env.clone());

                // Register constructors and recursor in bindings
                // Constructors are always namespaced as Type.ctor globally.
                let info = self.env.find(&ind_name).unwrap();
                if let Some(ind_val) = info.to_inductive_val() {
                    for ctor_name in &ind_val.ctors {
                        let cn = ctor_name.to_string();
                        self.env_bindings.insert(cn.clone(), Expr::mk_const(ctor_name.clone(), vec![]));
                    }
                }

                self.env_bindings.insert(name.clone(), Expr::mk_const(ind_name.clone(), vec![]));
                let rec_name = format!("rec.{}", name);
                self.env_bindings.insert(rec_name.clone(), Expr::mk_const(Name::new("rec").extend(&name), vec![]));

                if !self.quiet {

                    println!("  Added inductive: {}", name);

                }
                Ok(())
            }
            ParsedDecl::MutualInductive { types } => {
                let mut inductive_types = Vec::new();
                for (name, ty, ctors, _num_params) in &types {
                    let wrapped_ty = self.wrap_with_file_variables(ty.clone());
                    let wrapped_ctors: Vec<_> = ctors.iter()
                        .map(|(n, t)| (n.clone(), self.wrap_with_file_variables(t.clone())))
                        .collect();
                    let ty_expr = wrapped_ty.to_expr(&self.env_bindings, &self.env, &mut Vec::new());
                    let mut ctor_exprs = Vec::new();
                    for (ctor_name, ctor_ty) in &wrapped_ctors {
                        let ctor_ty_expr = ctor_ty.to_expr(&self.env_bindings, &self.env, &mut Vec::new());
                        // Use fully-qualified constructor names: Even.zero, Odd.succ, etc.
                        let full_ctor_name = Name::new(name).extend(ctor_name);
                        ctor_exprs.push(Constructor {
                            name: full_ctor_name,
                            ty: ctor_ty_expr,
                        });
                    }
                    inductive_types.push(InductiveType {
                        name: Name::new(name),
                        ty: ty_expr,
                        ctors: ctor_exprs,
                    });
                }

                // All types in the mutual block share the same num_params (use max for safety)
                let max_params = types.iter().map(|(_, _, _, np)| *np).max().unwrap_or(0) as u64
                    + self.file_variables.len() as u64;

                let decl = Declaration::Inductive {
                    level_params: vec![],
                    num_params: max_params,
                    types: inductive_types,
                    is_unsafe: false,
                };

                self.env.add(decl).map_err(|e| e)?;
                self.tc_state = TypeCheckerState::new(self.env.clone());

                // Register constructors and recursors for all types
                for (name, _, _, _) in &types {
                    let info = self.env.find(&Name::new(name)).unwrap();
                    if let Some(ind_val) = info.to_inductive_val() {
                        for ctor_name in &ind_val.ctors {
                            let cn = ctor_name.to_string();
                            self.env_bindings.insert(cn.clone(), Expr::mk_const(ctor_name.clone(), vec![]));
                            // Also register bare-name alias if not already taken.
                            // e.g. "Even.zero" also registers "zero" -> Const(Even.zero)
                            if let Some(pos) = cn.rfind('.') {
                                let bare = &cn[pos + 1..];
                                self.env_bindings.entry(bare.to_string())
                                    .or_insert(Expr::mk_const(ctor_name.clone(), vec![]));
                            }
                        }
                    }
                    self.env_bindings.insert(name.clone(), Expr::mk_const(Name::new(name), vec![]));
                    let rec_name = format!("rec.{}", name);
                    self.env_bindings.insert(rec_name.clone(), Expr::mk_const(Name::new("rec").extend(name), vec![]));
                    if !self.quiet {
                        println!("  Added inductive: {}", name);
                    }
                }
                Ok(())
            }
            ParsedDecl::Structure { name, ty, fields } => {
                let ty_expr = ty.to_expr(&self.env_bindings, &self.env, &mut Vec::new());
                let struct_const = Expr::mk_const(Name::new(&name), vec![]);

                // Build mk constructor type: field1 -> field2 -> ... -> Struct
                let mut mk_ty = ParsedExpr::Const(name.clone());
                for (_fname, fty) in fields.iter().rev() {
                    mk_ty = ParsedExpr::Pi("_".to_string(), Box::new(fty.clone()), Box::new(mk_ty));
                }
                let mk_ty_expr = mk_ty.to_expr(&self.env_bindings, &self.env, &mut Vec::new());

                let ind = InductiveType {
                    name: Name::new(&name),
                    ty: ty_expr.clone(),
                    ctors: vec![
                        Constructor { name: Name::new("mk"), ty: mk_ty_expr },
                    ],
                };

                let decl = Declaration::Inductive {
                    level_params: vec![],
                    num_params: 0,
                    types: vec![ind],
                    is_unsafe: false,
                };

                self.env.add(decl).map_err(|e| e)?;
                self.tc_state = TypeCheckerState::new(self.env.clone());

                // Register constructors and recursor in bindings
                let info = self.env.find(&Name::new(&name)).unwrap();
                if let Some(ind_val) = info.to_inductive_val() {
                    for ctor_name in &ind_val.ctors {
                        let cn = ctor_name.to_string();
                        self.env_bindings.insert(cn.clone(), Expr::mk_const(ctor_name.clone(), vec![]));
                    }
                }

                self.env_bindings.insert(name.clone(), struct_const.clone());
                let rec_name = Name::new("rec").extend(&name);
                let rec_name_str = format!("rec.{}", name);
                self.env_bindings.insert(rec_name_str.clone(), Expr::mk_const(rec_name.clone(), vec![]));

                // Generate projection definitions
                let num_fields = fields.len();
                for (field_idx, (field_name, field_ty)) in fields.iter().enumerate() {
                    let proj_name = format!("{}.{}", name, field_name);

                    // Build recursor application for projection
                    // rec.Struct (fun _ => FieldTy) (fun f1 => fun f2 => ... => fi) p
                    let field_ty_expr = field_ty.to_expr(&self.env_bindings, &self.env, &mut Vec::new());

                    // motive: fun _ => FieldTy
                    let motive = Expr::Lambda(
                        Name::new("_"),
                        BinderInfo::Default,
                        Rc::new(struct_const.clone()),
                        Rc::new(field_ty_expr.clone()),
                    );

                    // minor: fun f1 => fun f2 => ... => fi
                    // Build lambdas from inside out, using correct field types
                    let mut minor = Expr::mk_bvar((num_fields - 1 - field_idx) as u64);
                    for i in (0..num_fields).rev() {
                        let fty_expr = fields[i].1.to_expr(&self.env_bindings, &self.env, &mut Vec::new());
                        minor = Expr::Lambda(
                            Name::new(&format!("f{}", i)),
                            BinderInfo::Default,
                            Rc::new(fty_expr),
                            Rc::new(minor),
                        );
                    }

                    // parameter p : Struct
                    let p_var = Expr::mk_fvar(Name::new("p"));
                    let body = Expr::mk_app(
                        Expr::mk_app(
                            Expr::mk_app(Expr::mk_const(rec_name.clone(), vec![]), motive),
                            minor,
                        ),
                        p_var.clone(),
                    );

                    let proj_value = Expr::Lambda(
                        Name::new("p"),
                        BinderInfo::Default,
                        Rc::new(struct_const.clone()),
                        Rc::new(body),
                    );

                    let proj_ty = Expr::mk_arrow(struct_const.clone(), field_ty_expr);

                    let proj_decl = Declaration::Definition(DefinitionVal {
                        constant_val: ConstantVal {
                            name: Name::new(&proj_name),
                            level_params: vec![],
                            ty: proj_ty,
                        },
                        value: proj_value,
                        hints: ReducibilityHints::Regular(0),
                        safety: DefinitionSafety::Safe,
                    });

                    self.env.add(proj_decl).map_err(|e| e)?;
                    self.env_bindings.insert(proj_name.clone(), Expr::mk_const(Name::new(&proj_name), vec![]));
                    if !self.quiet {
                        println!("  Added projection: {}", proj_name);
                    }
                }

                self.tc_state = TypeCheckerState::new(self.env.clone());
                if !self.quiet {
                    println!("  Added structure: {}", name);
                }
                Ok(())
            }
        }
    }

    /// Wrap a parsed expression with Pi binders for all file-scoped variables.
    /// Used to prepend variable parameters to inductive types and constructors.
    fn wrap_with_file_variables(&self, expr: super::repl_parser::ParsedExpr) -> super::repl_parser::ParsedExpr {
        let mut result = expr;
        for (pname, pty) in self.file_variables.iter().rev() {
            result = super::repl_parser::ParsedExpr::Pi(pname.clone(), Box::new(pty.clone()), Box::new(result));
        }
        result
    }

    fn process_def_or_theorem(
        &mut self,
        name: String,
        params: Vec<(String, super::repl_parser::ParsedExpr)>,
        ret_ty: Option<super::repl_parser::ParsedExpr>,
        value: super::repl_parser::ParsedExpr,
        is_theorem: bool,
    ) -> Result<(), String> {
        // Prepend file-scoped variables to params
        let mut all_params = self.file_variables.clone();
        all_params.extend(params);

        // Convert parameter types, accumulating bound_vars so later params can reference earlier ones
        let mut param_exprs: Vec<(String, Expr)> = Vec::new();
        let mut bound_vars: Vec<String> = Vec::new();
        for (pname, pty) in &all_params {
            let ty_expr = pty.to_expr(&self.env_bindings, &self.env, &mut bound_vars);
            param_exprs.push((pname.clone(), ty_expr));
            bound_vars.push(pname.clone());
        }

        // Handle tactic block
        let (value_expr, introduced_vars, _param_decl_indices) = match &value {
            ParsedExpr::TacticBlock(tactics) => {
                if !is_theorem {
                    return Err("Tactic blocks are only allowed in theorems".to_string());
                }
                let target = ret_ty.as_ref().ok_or("Theorem with tactic block must have an explicit return type")?;
                let mut target_expr = target.to_expr(&self.env_bindings, &self.env, &mut bound_vars);
                // Wrap target with parameter types as Pi binders
                for (pname, pty) in param_exprs.iter().rev() {
                    target_expr = Expr::Pi(Name::new(pname), BinderInfo::Default, Rc::new(pty.clone()), Rc::new(target_expr));
                }

                let env = &self.env;
                let env_bindings = &self.env_bindings;
                let mut engine = TacticEngine::new(&mut self.tc_state, env, env_bindings, target_expr);
                engine.num_params = param_exprs.len();

                for tactic_cmd in tactics {
                    execute_tactic(env, env_bindings, &self.infix_ops, &self.notations, &mut engine, tactic_cmd)?;
                }

                if engine.num_goals() > 0 {
                    return Err(format!("Unsolved goals remaining: {}", engine.num_goals()));
                }

                let root_mvar = Expr::mk_mvar(Name::new("_tactic_mvar_0"));
                let proof = engine.build_proof(&root_mvar);
                (proof, engine.introduced_vars, engine.param_decl_indices)
            }
            _ => (value.to_expr_with_fn(&self.env_bindings, &self.env, &mut bound_vars, Some(&name)), Vec::new(), std::collections::HashSet::new()),
        };

        // Embed params into value as lambdas
        let mut final_value = value_expr;
        let is_tactic = matches!(&value, ParsedExpr::TacticBlock(_));
        if !is_tactic {
            for (pname, pty) in param_exprs.iter().rev() {
                // The parser already converts parameter names to BVars via bound_vars,
                // so we just wrap with lambdas directly. Calling abstract_fvar here
                // would incorrectly shift existing BVars.
                final_value = Expr::Lambda(
                    Name::new(pname),
                    BinderInfo::Default,
                    Rc::new(pty.clone()),
                    Rc::new(final_value),
                );
            }
        }

        // Determine type
        let final_ty = if let Some(rt) = ret_ty {
            let rt_expr = rt.to_expr(&self.env_bindings, &self.env, &mut bound_vars);
            let mut ty = rt_expr;
            for (pname, pty) in param_exprs.iter().rev() {
                ty = Expr::Pi(Name::new(pname), BinderInfo::Default, Rc::new(pty.clone()), Rc::new(ty));
            }
            ty
        } else {
            let mut tc = TypeChecker::with_local_ctx(&mut self.tc_state, super::local_ctx::LocalCtx::new());
            tc.infer(&final_value).map_err(|e| format!("Cannot infer type: {}", e))?
        };

        if is_theorem {
            // Type-check in relaxed mode (allows unassigned metavariables during solving)
            let mut tc = TypeChecker::with_allow_unassigned_mvar(&mut self.tc_state, super::local_ctx::LocalCtx::new());
            tc.check(&final_value, &final_ty)
                .map_err(|e| format!("Proof does not match theorem type: {}", e))?;

            // Collect solve-variable info: gather all MVars from value and type
            let mut mvar_names = Vec::new();
            final_value.collect_mvars(&mut mvar_names);
            final_ty.collect_mvars(&mut mvar_names);

            let mut solve_vars: Vec<(Name, Expr, Option<Expr>)> = Vec::new();
            for mvar_name in &mvar_names {
                let mut ty = self.tc_state.get_mvar_type(mvar_name).cloned();
                let assignment = self.tc_state.get_mvar_assignment(mvar_name).cloned();
                if ty.is_none() {
                    if let Some(ref val) = assignment {
                        let mut tc = TypeChecker::with_allow_unassigned_mvar(
                            &mut self.tc_state, super::local_ctx::LocalCtx::new());
                        ty = tc.infer(val).ok();
                    }
                }
                if let Some(t) = ty {
                    solve_vars.push((mvar_name.clone(), t, assignment));
                }
            }

            // Theorem requires all metavariables to be assigned
            let unassigned: Vec<_> = solve_vars.iter().filter(|(_, _, val)| val.is_none()).collect();
            if !unassigned.is_empty() {
                let names = unassigned.iter()
                    .map(|(n, ty, _)| format!("?{} : {}", n.to_string(), format_expr(ty)))
                    .collect::<Vec<_>>()
                    .join(", ");
                return Err(format!("Theorem has unassigned solve variables: {}", names));
            }
            let decl = Declaration::Theorem(TheoremVal {
                constant_val: ConstantVal {
                    name: Name::new(&name),
                    level_params: vec![],
                    ty: final_ty,
                },
                value: final_value.clone(),
            });
            self.env.add(decl).map_err(|e| e)?;
            self.tc_state = TypeCheckerState::new(self.env.clone());
            self.env_bindings.insert(name.clone(), Expr::mk_const(Name::new(&name), vec![]));
            if !self.quiet {
                println!("  Added theorem: {}", name);
            }
        } else {
            let decl = Declaration::Definition(DefinitionVal {
                constant_val: ConstantVal {
                    name: Name::new(&name),
                    level_params: vec![],
                    ty: final_ty,
                },
                value: final_value,
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Safe,
            });
            self.env.add(decl).map_err(|e| e)?;
            self.tc_state = TypeCheckerState::new(self.env.clone());
            self.env_bindings.insert(name.clone(), Expr::mk_const(Name::new(&name), vec![]));
            if !self.quiet {
                println!("  Added definition: {}", name);
            }
        }
        Ok(())
    }

    fn process_solve(
        &mut self,
        name: String,
        params: Vec<(String, super::repl_parser::ParsedExpr)>,
        ret_ty: super::repl_parser::ParsedExpr,
        value: super::repl_parser::ParsedExpr,
    ) -> Result<(), String> {
        // Prepend file-scoped variables to params
        let mut all_params = self.file_variables.clone();
        all_params.extend(params);

        // Convert parameter types
        let mut param_exprs: Vec<(String, Expr)> = Vec::new();
        let mut bound_vars: Vec<String> = Vec::new();
        for (pname, pty) in &all_params {
            let ty_expr = pty.to_expr(&self.env_bindings, &self.env, &mut bound_vars);
            param_exprs.push((pname.clone(), ty_expr));
            bound_vars.push(pname.clone());
        }

        // Convert return type
        let ret_ty_expr = ret_ty.to_expr(&self.env_bindings, &self.env, &mut bound_vars);

        // Handle tactic block for solve (like theorem does)
        let (value_expr, introduced_vars, _param_decl_indices) = match &value {
            ParsedExpr::TacticBlock(tactics) => {
                let mut target_expr = ret_ty_expr.clone();
                // Wrap target with parameter types as Pi binders
                for (pname, pty) in param_exprs.iter().rev() {
                    target_expr = Expr::Pi(Name::new(pname), BinderInfo::Default, Rc::new(pty.clone()), Rc::new(target_expr));
                }

                let env = &self.env;
                let env_bindings = &self.env_bindings;
                let mut engine = TacticEngine::new(&mut self.tc_state, env, env_bindings, target_expr);
                engine.num_params = param_exprs.len();

                for tactic_cmd in tactics {
                    execute_tactic(env, env_bindings, &self.infix_ops, &self.notations, &mut engine, tactic_cmd)?;
                }

                if engine.num_goals() > 0 {
                    return Err(format!("Unsolved goals remaining: {}", engine.num_goals()));
                }

                let root_mvar = Expr::mk_mvar(Name::new("_tactic_mvar_0"));
                let proof = engine.build_proof(&root_mvar);
                (proof, engine.introduced_vars, engine.param_decl_indices)
            }
            _ => (value.to_expr_with_fn(&self.env_bindings, &self.env, &mut bound_vars, Some(&name)), Vec::new(), std::collections::HashSet::new()),
        };

        // Embed params into value as lambdas
        let mut final_value = value_expr;
        let is_tactic = matches!(&value, ParsedExpr::TacticBlock(_));
        if !is_tactic {
            for (pname, pty) in param_exprs.iter().rev() {
                // The parser already converts parameter names to BVars via bound_vars,
                // so we just wrap with lambdas directly. Calling abstract_fvar here
                // would incorrectly shift existing BVars.
                final_value = Expr::Lambda(
                    Name::new(pname),
                    BinderInfo::Default,
                    Rc::new(pty.clone()),
                    Rc::new(final_value),
                );
            }
        }

        // Build final type: Pi params, ret_ty
        let mut final_ty = ret_ty_expr;
        for (pname, pty) in param_exprs.iter().rev() {
            final_ty = Expr::Pi(Name::new(pname), BinderInfo::Default, Rc::new(pty.clone()), Rc::new(final_ty));
        }

        // Clear any stale mvar type registrations
        self.tc_state.clear_mvar_types();

        // Type-check in solve mode (allows unassigned metavariables)
        let mut tc = TypeChecker::with_allow_unassigned_mvar(&mut self.tc_state, super::local_ctx::LocalCtx::new());
        match tc.check(&final_value, &final_ty) {
            Ok(_) => {}
            Err(e) => return Err(format!("Solve type check failed: {}", e)),
        }

        // Collect solve-variable info: gather all MVars from value and type
        let mut mvar_names = Vec::new();
        final_value.collect_mvars(&mut mvar_names);
        final_ty.collect_mvars(&mut mvar_names);

        let mut solve_vars: Vec<(Name, Expr, Option<Expr>)> = Vec::new();
        for mvar_name in &mvar_names {
            let mut ty = self.tc_state.get_mvar_type(mvar_name).cloned();
            let assignment = self.tc_state.get_mvar_assignment(mvar_name).cloned();
            if ty.is_none() {
                if let Some(ref val) = assignment {
                    let mut tc = TypeChecker::with_allow_unassigned_mvar(
                        &mut self.tc_state, super::local_ctx::LocalCtx::new());
                    ty = tc.infer(val).ok();
                }
            }
            if let Some(t) = ty {
                solve_vars.push((mvar_name.clone(), t, assignment));
            }
        }

        if !self.quiet {
            println!("  Solved: {}", name);
            if solve_vars.is_empty() {
                println!("    (no solve variables)");
            } else {
                for (mvar_name, ty, val) in &solve_vars {
                    match val {
                        Some(v) => println!("    ?{} : {} = {}", mvar_name.to_string(), format_expr(ty), format_expr(v)),
                        None => println!("    ?{} : {} (unassigned)", mvar_name.to_string(), format_expr(ty)),
                    }
                }
            }
        }

        // Solve is a one-shot derivation check: its result is never registered
        // for later reference. Use theorem for permanent declarations.

        Ok(())
    }

    fn handle_axiom(&mut self, rest: &str) -> Result<(), String> {
        let parts: Vec<&str> = rest.splitn(2, ':').collect();
        if parts.len() != 2 {
            return Err("Usage: :axiom <name> : <type>".to_string());
        }
        let name = parts[0].trim().to_string();
        let ty_str = parts[1].trim();

        let ty = self.parse_and_convert(ty_str)?;

        let decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new(&name),
                level_params: vec![],
                ty,
            },
            is_unsafe: false,
        });

        self.env.add(decl).map_err(|e| e)?;
        self.tc_state = TypeCheckerState::new(self.env.clone());
        self.env_bindings.insert(name.clone(), Expr::mk_const(Name::new(&name), vec![]));
        if !self.quiet {
            println!("  Added axiom: {}", name);
        }
        Ok(())
    }

    fn handle_def(&mut self, rest: &str) -> Result<(), String> {
        let name_end = rest.find(|c: char| c.is_whitespace() || c == ':' || c == '=')
            .unwrap_or(rest.len());
        let name = rest[..name_end].trim().to_string();
        let rest_after_name = rest[name_end..].trim_start().to_string();
        let (ty, val_str) = if rest_after_name.starts_with(":=") {
            (None, rest_after_name[2..].trim().to_string())
        } else if rest_after_name.starts_with(':') {
            let rest = &rest_after_name[1..]; // skip ':'
            let parts: Vec<&str> = rest.splitn(2, ":=").collect();
            if parts.len() != 2 {
                return Err("Usage: :def <name> : <type> := <value>".to_string());
            }
            let ty_str = parts[0].trim();
            let val_str = parts[1].trim();
            let ty = self.parse_and_convert(ty_str)?;
            (Some(ty), val_str.to_string())
        } else {
            return Err("Usage: :def <name> := <value> or :def <name> : <type> := <value>".to_string());
        };

        let value = self.parse_and_convert(&val_str)?;

        let inferred_ty = match &ty {
            Some(t) => t.clone(),
            None => {
                let mut tc = TypeChecker::with_local_ctx(&mut self.tc_state, super::local_ctx::LocalCtx::new());
                tc.infer(&value).map_err(|e| format!("Cannot infer type: {}", e))?
            }
        };

        let decl = Declaration::Definition(DefinitionVal {
            constant_val: ConstantVal {
                name: Name::new(&name),
                level_params: vec![],
                ty: inferred_ty,
            },
            value,
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
        });

        self.env.add(decl).map_err(|e| e)?;
        self.tc_state = TypeCheckerState::new(self.env.clone());
        self.env_bindings.insert(name.clone(), Expr::mk_const(Name::new(&name), vec![]));
        if !self.quiet {
            println!("  Added definition: {}", name);
        }
        Ok(())
    }

    fn handle_theorem(&mut self, rest: &str) -> Result<(), String> {
        let name_end = rest.find(|c: char| c.is_whitespace() || c == ':' || c == '=')
            .unwrap_or(rest.len());
        let name = rest[..name_end].trim().to_string();
        let rest_after_name = rest[name_end..].trim_start().to_string();

        if !rest_after_name.starts_with(':') {
            return Err("Usage: :theorem <name> : <type> := <proof>".to_string());
        }
        let rest = &rest_after_name[1..];
        let parts: Vec<&str> = rest.splitn(2, ":=").collect();
        if parts.len() != 2 {
            return Err("Usage: :theorem <name> : <type> := <proof>".to_string());
        }
        let ty_str = parts[0].trim();
        let proof_str = parts[1].trim();

        let ty = self.parse_and_convert(ty_str)?;
        let proof = self.parse_and_convert(proof_str)?;

        let mut tc = TypeChecker::with_local_ctx(&mut self.tc_state, super::local_ctx::LocalCtx::new());
        tc.check(&proof, &ty).map_err(|e| format!("Proof does not match theorem type: {}", e))?;

        let decl = Declaration::Theorem(TheoremVal {
            constant_val: ConstantVal {
                name: Name::new(&name),
                level_params: vec![],
                ty,
            },
            value: proof,
        });

        self.env.add(decl).map_err(|e| e)?;
        self.tc_state = TypeCheckerState::new(self.env.clone());
        self.env_bindings.insert(name.clone(), Expr::mk_const(Name::new(&name), vec![]));
        if !self.quiet {
            println!("  Added theorem: {}", name);
        }
        Ok(())
    }

    fn handle_solve(&mut self, rest: &str) -> Result<(), String> {
        let name_end = rest.find(|c: char| c.is_whitespace() || c == ':' || c == '=')
            .unwrap_or(rest.len());
        let name = rest[..name_end].trim().to_string();
        let rest_after_name = rest[name_end..].trim_start().to_string();

        if !rest_after_name.starts_with(':') {
            return Err("Usage: :solve <name> : <type> := <expr>".to_string());
        }
        let rest = &rest_after_name[1..];
        let parts: Vec<&str> = rest.splitn(2, ":=").collect();
        if parts.len() != 2 {
            return Err("Usage: :solve <name> : <type> := <expr>".to_string());
        }
        let ty_str = parts[0].trim();
        let expr_str = parts[1].trim();

        let ty = self.parse_and_convert(ty_str)?;
        let expr = self.parse_and_convert(expr_str)?;

        self.tc_state.clear_mvar_types();
        let mut tc = TypeChecker::with_allow_unassigned_mvar(&mut self.tc_state, super::local_ctx::LocalCtx::new());
        tc.check(&expr, &ty).map_err(|e| format!("Solve type check failed: {}", e))?;

        let mut solve_vars: Vec<(Name, Expr, Option<Expr>)> = Vec::new();
        for (mvar_name, mvar_ty) in self.tc_state.iter_mvar_types() {
            let assigned = self.tc_state.get_mvar_assignment(mvar_name).cloned();
            solve_vars.push((mvar_name.clone(), mvar_ty.clone(), assigned));
        }

        println!("  Solved: {}", name);
        if solve_vars.is_empty() {
            println!("    (no solve variables)");
        } else {
            for (mvar_name, mvar_ty, val) in &solve_vars {
                match val {
                    Some(v) => println!("    ?{} : {} = {}", mvar_name.to_string(), format_expr(mvar_ty), format_expr(v)),
                    None => println!("    ?{} : {} (unassigned)", mvar_name.to_string(), format_expr(mvar_ty)),
                }
            }
        }

        self.env_bindings.insert(name.clone(), expr.clone());
        Ok(())
    }

    fn handle_inductive(&mut self, rest: &str) -> Result<(), String> {
        let mut parts = rest.split('|');
        let name = parts.next().unwrap_or("").trim().to_string();
        if name.is_empty() {
            return Err("Usage: :inductive <name> | <ctor1> : <type1> | ...".to_string());
        }

        let mut ctors = Vec::new();
        for part in parts {
            let part = part.trim();
            if part.is_empty() {
                continue;
            }
            let ctor_parts: Vec<&str> = part.splitn(2, ':').collect();
            if ctor_parts.len() != 2 {
                return Err(format!("Invalid constructor syntax: {}", part));
            }
            let ctor_name = ctor_parts[0].trim().to_string();
            let ctor_ty_str = ctor_parts[1].trim();
            let ctor_ty = self.parse_and_convert(ctor_ty_str)?;
            ctors.push(Constructor {
                name: Name::new(&ctor_name),
                ty: ctor_ty,
            });
        }

        let ind_ty = Expr::mk_type();
        let ind = InductiveType {
            name: Name::new(&name),
            ty: ind_ty,
            ctors,
        };

        let decl = Declaration::Inductive {
            level_params: vec![],
            num_params: 0,
            types: vec![ind],
            is_unsafe: false,
        };

        self.env.add(decl).map_err(|e| e)?;
        self.tc_state = TypeCheckerState::new(self.env.clone());

        // Register constructors and recursor in bindings
        let info = self.env.find(&Name::new(&name)).unwrap();
        if let Some(ind_val) = info.to_inductive_val() {
            for ctor_name in &ind_val.ctors {
                let cn = ctor_name.to_string();
                self.env_bindings.insert(cn.clone(), Expr::mk_const(ctor_name.clone(), vec![]));
            }
        }

        self.env_bindings.insert(name.clone(), Expr::mk_const(Name::new(&name), vec![]));
        let rec_name = format!("rec.{}", name);
        self.env_bindings.insert(rec_name.clone(), Expr::mk_const(Name::new("rec").extend(&name), vec![]));

        if !self.quiet {

            println!("  Added inductive: {}", name);

        }
        Ok(())
    }

    fn handle_infer(&mut self, rest: &str) -> Result<(), String> {
        let expr = self.parse_and_convert(rest)?;
        let mut tc = TypeChecker::with_local_ctx(&mut self.tc_state, super::local_ctx::LocalCtx::new());
        let ty = tc.infer(&expr).map_err(|e| e)?;
        println!("  {}", format_expr(&ty));
        Ok(())
    }

    fn handle_reduce(&mut self, rest: &str) -> Result<(), String> {
        let expr = self.parse_and_convert(rest)?;
        let mut tc = TypeChecker::with_local_ctx(&mut self.tc_state, super::local_ctx::LocalCtx::new());
        let reduced = tc.whnf(&expr);
        println!("  {}", format_expr(&reduced));
        Ok(())
    }

    fn handle_nf(&mut self, rest: &str) -> Result<(), String> {
        let expr = self.parse_and_convert(rest)?;
        let mut tc = TypeChecker::with_local_ctx(&mut self.tc_state, super::local_ctx::LocalCtx::new());
        let reduced = tc.nf(&expr);
        println!("  {}", format_expr(&reduced));
        Ok(())
    }

    fn handle_defeq(&mut self, rest: &str) -> Result<(), String> {
        let parts: Vec<&str> = rest.splitn(2, '=').collect();
        if parts.len() != 2 {
            return Err("Usage: :defeq <expr1> = <expr2>".to_string());
        }
        let e1 = self.parse_and_convert(parts[0].trim())?;
        let e2 = self.parse_and_convert(parts[1].trim())?;
        let mut tc = TypeChecker::with_local_ctx(&mut self.tc_state, super::local_ctx::LocalCtx::new());
        let result = tc.is_def_eq(&e1, &e2);
        println!("  {}", result);
        Ok(())
    }

    fn print_env(&self) {
        println!("  Current environment:");
        println!("    Constants: {}", self.env.num_constants());
        self.env.for_each_constant(|info| {
            println!("      {} : {}", info.name().to_string(), format_expr(info.get_type()));
        });
    }

    fn print_help(&self) {
        println!("Commands:");
        println!("  :env                          Show current environment");
        println!("  :load <file.cic>             Load declarations from a file");
        println!("  :axiom <name> : <type>        Add an axiom");
        println!("  :def <name> := <value>        Add a definition");
        println!("  :def <name> : <type> := <val> Add a definition with type");
        println!("  :theorem <name> : <type> := <proof>  Add a theorem");
        println!("  :inductive <name> | <c>:<t>|..Add an inductive type");
        println!("  :infer <expr>                 Infer the type");
        println!("  :reduce <expr>                Reduce to WHNF");
        println!("  :nf <expr>                    Reduce to full NF");
        println!("  :defeq <e1> = <e2>            Check definitional equality");
        println!("  :solve <name> : <type> := <expr>  Solve with metavariables");
        println!("  :help                         Show this help");
        println!("  :quit                         Exit");
        println!();
        println!("Expression syntax:");
        println!("  Constants: Nat, zero, succ, Bool, true, ...");
        println!("  Application: f a b (left-associative)");
        println!("  Lambda: \\x : Nat . x  or  fun x => x");
        println!("  Pi: Nat -> Nat  or  (x : Nat) -> Nat");
        println!("  Let: let x := zero in x");
        println!("  Have: have h : P := proof in e");
        println!("  Match: match e : T with | ctor => e1 | ctor x => e2");
        println!("  Sort: Type, Prop");
        println!("  Parens: (e)");
        println!("  Numbers: 0, 1, 2, ...");
        println!();
        println!("File syntax (:load)");
        println!("  inductive Name where");
        println!("  | ctor : Type");
        println!("  def name (params) : type := value");
        println!("  theorem name (params) : type := proof");
    }

    fn load_axioms(&mut self) {
        let prop = Expr::mk_sort(Level::Zero);
        let ty = Expr::mk_type();

        // propext : Π (P : Prop), Π (Q : Prop), Π (_ : P → Q), Π (_ : Q → P), Eq Prop P Q
        let eq_const = Expr::mk_const(Name::new("Eq"), vec![]);
        let eq_app = |a, b, c| Expr::mk_app(Expr::mk_app(Expr::mk_app(eq_const.clone(), a), b), c);
        let propext_ty = Expr::mk_pi(Name::new("P"), prop.clone(),
            Expr::mk_pi(Name::new("Q"), prop.clone(),
                Expr::mk_pi(Name::new("_"), Expr::mk_arrow(Expr::mk_bvar(1), Expr::mk_bvar(1)),
                    Expr::mk_pi(Name::new("_"), Expr::mk_arrow(Expr::mk_bvar(2), Expr::mk_bvar(2)),
                        eq_app(Expr::mk_bvar(3), Expr::mk_bvar(2), Expr::mk_bvar(1))))));

        let propext_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("propext"),
                level_params: vec![],
                ty: propext_ty,
            },
            is_unsafe: false,
        });
        let _ = self.env.add(propext_decl);

        // choice : Π (A : Type), Π (P : A → Prop), Π (_ : Exists A P), A
        let exists_app = Expr::mk_app(Expr::mk_app(Expr::mk_const(Name::new("Exists"), vec![]), Expr::mk_bvar(1)), Expr::mk_bvar(0));
        let choice_ty = Expr::mk_pi(Name::new("A"), ty.clone(),
            Expr::mk_pi(Name::new("P"), Expr::mk_arrow(Expr::mk_bvar(0), prop.clone()),
                Expr::mk_pi(Name::new("_"), exists_app, Expr::mk_bvar(2))));

        let choice_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("choice"),
                level_params: vec![],
                ty: choice_ty,
            },
            is_unsafe: false,
        });
        let _ = self.env.add(choice_decl);

        // sorry_prop : Π (P : Prop), P
        let sorry_prop_ty = Expr::mk_pi(Name::new("P"), prop.clone(), Expr::mk_bvar(0));
        let sorry_prop_decl = Declaration::Axiom(AxiomVal {
            constant_val: ConstantVal {
                name: Name::new("sorry_prop"),
                level_params: vec![],
                ty: sorry_prop_ty,
            },
            is_unsafe: false,
        });
        let _ = self.env.add(sorry_prop_decl);

        self.tc_state = TypeCheckerState::new(self.env.clone());
        self.env_bindings.insert("propext".to_string(), Expr::mk_const(Name::new("propext"), vec![]));
        self.env_bindings.insert("choice".to_string(), Expr::mk_const(Name::new("choice"), vec![]));
        self.env_bindings.insert("sorry_prop".to_string(), Expr::mk_const(Name::new("sorry_prop"), vec![]));
    }

    fn load_quot(&mut self) {
        let _ = self.env.add(Declaration::Quot);
        self.tc_state = TypeCheckerState::new(self.env.clone());
        self.env_bindings.insert("Quot".to_string(), Expr::mk_const(Name::new("Quot"), vec![]));
        self.env_bindings.insert("Quot.mk".to_string(), Expr::mk_const(Name::new("Quot").extend("mk"), vec![]));
        self.env_bindings.insert("Quot.lift".to_string(), Expr::mk_const(Name::new("Quot").extend("lift"), vec![]));
        self.env_bindings.insert("Quot.ind".to_string(), Expr::mk_const(Name::new("Quot").extend("ind"), vec![]));
        self.env_bindings.insert("Quot.sound".to_string(), Expr::mk_const(Name::new("Quot").extend("sound"), vec![]));
    }

    /// Extract internal state for external tools (e.g., TUI).
    pub fn into_state(self) -> (Environment, TypeCheckerState, HashMap<String, Expr>, HashMap<String, (i32, String, bool)>, HashMap<String, super::repl_parser::ParsedExpr>) {
        (self.env, self.tc_state, self.env_bindings, self.infix_ops, self.notations)
    }
}

/// Parse an expression for tactic use (standalone to avoid borrow conflicts)
pub fn parse_tactic_expr(env_bindings: &HashMap<String, Expr>, env: &Environment, infix_ops: &HashMap<String, (i32, String, bool)>, notations: &HashMap<String, super::repl_parser::ParsedExpr>, input: &str) -> Result<Expr, String> {
    let mut parser = ReplParser::new_with_state(input, infix_ops.clone(), notations.clone());
    let parsed = parser.parse_expr().map_err(|e| format!("parse error: {}", e))?;
    Ok(parsed.to_expr(env_bindings, env, &mut Vec::new()))
}

/// Resolve Const references to FVar if the name exists in the current tactic goal's local context.
fn resolve_tactic_vars(expr: &Expr, engine: &TacticEngine) -> Expr {
    match expr {
        Expr::Const(name, _) => {
            if let Some(decl) = engine.current_goal().and_then(|g| g.lctx.find_local_decl(name)) {
                Expr::mk_fvar(decl.get_name().clone())
            } else {
                expr.clone()
            }
        }
        Expr::App(f, a) => {
            let new_f = resolve_tactic_vars(f, engine);
            let new_a = resolve_tactic_vars(a, engine);
            Expr::App(Rc::new(new_f), Rc::new(new_a))
        }
        Expr::Lambda(name, bi, ty, body) => {
            let new_ty = resolve_tactic_vars(ty, engine);
            let new_body = resolve_tactic_vars(body, engine);
            Expr::Lambda(name.clone(), *bi, Rc::new(new_ty), Rc::new(new_body))
        }
        Expr::Pi(name, bi, ty, body) => {
            let new_ty = resolve_tactic_vars(ty, engine);
            let new_body = resolve_tactic_vars(body, engine);
            Expr::Pi(name.clone(), *bi, Rc::new(new_ty), Rc::new(new_body))
        }
        Expr::Let(name, ty, value, body, nondep) => {
            let new_ty = resolve_tactic_vars(ty, engine);
            let new_value = resolve_tactic_vars(value, engine);
            let new_body = resolve_tactic_vars(body, engine);
            Expr::Let(name.clone(), Rc::new(new_ty), Rc::new(new_value), Rc::new(new_body), *nondep)
        }
        Expr::MData(d, e) => Expr::MData(d.clone(), Rc::new(resolve_tactic_vars(e, engine))),
        Expr::Proj(s, i, e) => Expr::Proj(s.clone(), *i, Rc::new(resolve_tactic_vars(e, engine))),
        _ => expr.clone(),
    }
}

/// Parse rewrite argument list for `rw [h1, h2]` or `rw [←h]` syntax.
/// Returns a list of (is_reverse, expr_string).
fn parse_rewrite_list(input: &str) -> Result<Vec<(bool, String)>, String> {
    let input = input.trim();
    if input.starts_with('[') {
        if !input.ends_with(']') {
            return Err("rewrite: expected closing ']'".to_string());
        }
        let inner = &input[1..input.len()-1];
        let parts: Vec<&str> = inner.split(',').collect();
        let mut result = Vec::new();
        for part in parts {
            let part = part.trim();
            if part.is_empty() {
                continue;
            }
            let (is_reverse, expr_str) = if part.starts_with('←') {
                (true, part[3..].trim().to_string())
            } else if part.starts_with("<-") {
                (true, part[2..].trim().to_string())
            } else {
                (false, part.to_string())
            };
            result.push((is_reverse, expr_str));
        }
        if result.is_empty() {
            return Err("rewrite: empty list".to_string());
        }
        Ok(result)
    } else {
        let (is_reverse, expr_str) = if input.starts_with('←') {
            (true, input[3..].trim().to_string())
        } else if input.starts_with("<-") {
            (true, input[2..].trim().to_string())
        } else {
            (false, input.to_string())
        };
        Ok(vec![(is_reverse, expr_str)])
    }
}

/// Execute a single tactic command (standalone to avoid borrow conflicts)
pub fn execute_tactic(
    env: &Environment,
    env_bindings: &HashMap<String, Expr>,
    infix_ops: &HashMap<String, (i32, String, bool)>,
    notations: &HashMap<String, super::repl_parser::ParsedExpr>,
    engine: &mut TacticEngine,
    cmd: &str,
) -> Result<(), String> {
    let cmd = cmd.trim();
    if cmd.is_empty() {
        return Ok(());
    }

    let parts: Vec<&str> = cmd.splitn(2, ' ').collect();
    let tactic_name = parts[0];
    let rest = parts.get(1).map(|s| s.trim()).unwrap_or("");

    match tactic_name {
        "intro" | "intros" => {
            if rest.is_empty() {
                engine.tactic_intro("_x")?;
            } else {
                for name in rest.split_whitespace() {
                    engine.tactic_intro(name)?;
                }
            }
            Ok(())
        }
        "exact" => {
            if rest.is_empty() {
                return Err("exact requires an expression".to_string());
            }
            let expr = parse_tactic_expr(env_bindings, env, infix_ops, notations, rest)?;
            let expr = resolve_tactic_vars(&expr, engine);
            engine.tactic_exact(&expr)
        }
        "apply" => {
            if rest.is_empty() {
                return Err("apply requires an expression".to_string());
            }
            let expr = parse_tactic_expr(env_bindings, env, infix_ops, notations, rest)?;
            let expr = resolve_tactic_vars(&expr, engine);
            engine.tactic_apply(&expr)
        }
        "refl" | "reflexivity" | "rfl" => {
            engine.tactic_refl()
        }
        "assumption" => {
            engine.tactic_assumption()
        }
        "rewrite" | "rw" => {
            if rest.is_empty() {
                return Err("rewrite requires an equality hypothesis".to_string());
            }
            let rewrites = parse_rewrite_list(rest)?;
            for (is_reverse, expr_str) in rewrites {
                let expr = parse_tactic_expr(env_bindings, env, infix_ops, notations, &expr_str)?;
                let expr = resolve_tactic_vars(&expr, engine);
                engine.tactic_rewrite(&expr, is_reverse)?;
            }
            Ok(())
        }
        "induction" => {
            if rest.is_empty() {
                return Err("induction requires a variable name".to_string());
            }
            let var_name = rest.trim();
            let user_name = Name::new(var_name);
            let var_expr = if let Some(goal) = engine.current_goal() {
                if let Some(decl) = goal.lctx.find_local_decl(&user_name) {
                    Expr::mk_fvar(decl.get_name().clone())
                } else {
                    Expr::mk_fvar(user_name)
                }
            } else {
                Expr::mk_fvar(user_name)
            };
            engine.tactic_induction(&var_expr)
        }
        "exists" => {
            if rest.is_empty() {
                return Err("exists requires a witness expression".to_string());
            }
            let expr = parse_tactic_expr(env_bindings, env, infix_ops, notations, rest)?;
            let expr = resolve_tactic_vars(&expr, engine);
            engine.tactic_exists(&expr)
        }
        "have" => {
            if rest.is_empty() {
                return Err("have requires name, type and proof".to_string());
            }
            let have_rest = rest.trim();
            let name_end = have_rest.find(|c: char| c == ':' || c == ' ')
                .unwrap_or(have_rest.len());
            let name = have_rest[..name_end].trim().to_string();
            let after_name = have_rest[name_end..].trim_start();

            if !after_name.starts_with(':') {
                return Err("have syntax: have <name> : <type> := <proof>".to_string());
            }
            let after_colon = after_name[1..].trim_start();

            let assign_pos = after_colon.find(":=");
            if assign_pos.is_none() {
                return Err("have syntax: have <name> : <type> := <proof>".to_string());
            }
            let assign_pos = assign_pos.unwrap();
            let ty_str = after_colon[..assign_pos].trim();
            let proof_str = after_colon[assign_pos + 2..].trim();

            let ty = parse_tactic_expr(env_bindings, env, infix_ops, notations, ty_str)?;
            let ty = resolve_tactic_vars(&ty, engine);
            let proof = parse_tactic_expr(env_bindings, env, infix_ops, notations, proof_str)?;
            let proof = resolve_tactic_vars(&proof, engine);
            engine.tactic_have(&name, &ty, &proof)
        }
        _ => Err(format!("Unknown tactic: {}", tactic_name)),
    }
}

