use super::declaration::*;
use super::environment::Environment;
use super::expr::*;
use super::repl_parser::{ParsedDecl, Parser as ReplParser};
use super::kernel_ext::{ConstructorInfo, RecursorInfo};
use super::type_checker::{TypeChecker, TypeCheckerState};
use std::collections::HashMap;
use std::fs;
use std::io::{self, Write};
use std::rc::Rc;

/// Interactive TTobs REPL.
///
/// Commands:
///   :env                          Show current environment
///   :load <file.ott>              Load declarations from a file
///   :axiom <name> : <type>        Add an axiom
///   :def <name> := <value>        Add a definition (type inferred)
///   :def <name> : <type> := <value>  Add a definition with explicit type
///   :theorem <name> : <type> := <proof>  Add a theorem
///   :infer <expr>                 Infer the type of an expression
///   :check <expr> : <type>        Check expression against type
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
}

impl Repl {
    pub fn new() -> Self {
        let env = Environment::new();
        let mut tc_state = TypeCheckerState::new(env.clone());

        // Register quotient primitives
        for name in [
            Name::new("Quot"),
            Name::new("Quot").extend("mk"),
            Name::new("Quot").extend("lift"),
            Name::new("Quot").extend("ind"),
            Name::new("Quot").extend("sound"),
        ] {
            tc_state.register_quot(name);
        }

        Repl {
            env,
            tc_state,
            env_bindings: HashMap::new(),
            quiet: false,
        }
    }

    pub fn set_quiet(&mut self, quiet: bool) {
        self.quiet = quiet;
    }

    pub fn check_files(&mut self, files: &[&str]) -> Result<(), String> {
        for filepath in files {
            let contents = fs::read_to_string(filepath)
                .map_err(|e| format!("Cannot read file '{}': {}", filepath, e))?;
            let mut parser = ReplParser::new(&contents);
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
        println!("║          TTobs Kernel REPL v0.1 (Observational Type Theory)          ║");
        println!("║     Type :help for available commands. Type :quit to exit.          ║");
        println!("╚═══════════════════════════════════════════════════════════════════════╝");
        println!();

        loop {
            print!("ttobs> ");
            io::stdout().flush().unwrap();

            let mut input = String::new();
            if io::stdin().read_line(&mut input).is_err() {
                println!("Error reading input.");
                continue;
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
            return self.handle_theorem_cmd(&input[9..]).map(|_| false);
        }

        if input.starts_with(":infer ") {
            return self.handle_infer(&input[7..]).map(|_| false);
        }

        if input.starts_with(":check ") {
            return self.handle_check(&input[7..]).map(|_| false);
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
        let mut parser = ReplParser::new(input);
        let parsed = parser.parse_expr()?;
        Ok(parsed.to_expr(&self.env_bindings, &self.env, &mut Vec::new()))
    }

    fn handle_load(&mut self, filepath: &str) -> Result<(), String> {
        let contents = fs::read_to_string(filepath)
            .map_err(|e| format!("Cannot read file '{}': {}", filepath, e))?;
        let mut parser = ReplParser::new(&contents);
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
                self.tc_state = self.tc_state.with_env(self.env.clone());
                self.env_bindings.insert(name.clone(), Expr::mk_const(Name::new(&name), vec![]));
                if !self.quiet {
                    println!("  Added axiom: {}", name);
                }
                Ok(())
            }
            ParsedDecl::Def { name, params, ret_ty, value } => {
                self.process_def(name, params, ret_ty, value)
            }
            ParsedDecl::Theorem { name, params, ret_ty, value } => {
                self.process_theorem(name, params, ret_ty, value)
            }
            ParsedDecl::Inductive { name, ctors } => {
                self.process_inductive(name, ctors)
            }
        }
    }

    fn process_def(
        &mut self,
        name: String,
        params: Vec<(String, super::repl_parser::ParsedExpr)>,
        ret_ty: Option<super::repl_parser::ParsedExpr>,
        value: super::repl_parser::ParsedExpr,
    ) -> Result<(), String> {
        // Convert parameter types, accumulating bound_vars so later params can reference earlier ones
        let mut param_exprs: Vec<(String, Expr)> = Vec::new();
        let mut bound_vars: Vec<String> = Vec::new();
        for (pname, pty) in &params {
            let ty_expr = pty.to_expr(&self.env_bindings, &self.env, &mut bound_vars);
            param_exprs.push((pname.clone(), ty_expr));
            bound_vars.push(pname.clone());
        }

        let value_expr = value.to_expr(&self.env_bindings, &self.env, &mut bound_vars);

        // Embed params into value as lambdas
        let mut final_value = value_expr;
        for (pname, pty) in param_exprs.iter().rev() {
            final_value = Expr::Lambda(
                Name::new(pname),
                BinderInfo::Default,
                Rc::new(pty.clone()),
                Rc::new(final_value),
            );
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
        self.tc_state = self.tc_state.with_env(self.env.clone());
        self.env_bindings.insert(name.clone(), Expr::mk_const(Name::new(&name), vec![]));
        if !self.quiet {
            println!("  Added definition: {}", name);
        }
        Ok(())
    }

    fn process_theorem(
        &mut self,
        name: String,
        params: Vec<(String, super::repl_parser::ParsedExpr)>,
        ret_ty: super::repl_parser::ParsedExpr,
        value: super::repl_parser::ParsedExpr,
    ) -> Result<(), String> {
        let mut param_exprs: Vec<(String, Expr)> = Vec::new();
        let mut bound_vars: Vec<String> = Vec::new();
        for (pname, pty) in &params {
            let ty_expr = pty.to_expr(&self.env_bindings, &self.env, &mut bound_vars);
            param_exprs.push((pname.clone(), ty_expr));
            bound_vars.push(pname.clone());
        }

        let value_expr = value.to_expr(&self.env_bindings, &self.env, &mut bound_vars);
        let ret_ty_expr = ret_ty.to_expr(&self.env_bindings, &self.env, &mut bound_vars);

        // Embed params into value as lambdas
        let mut final_value = value_expr;
        for (pname, pty) in param_exprs.iter().rev() {
            final_value = Expr::Lambda(
                Name::new(pname),
                BinderInfo::Default,
                Rc::new(pty.clone()),
                Rc::new(final_value),
            );
        }

        // Build final type as Pi binders
        let mut final_ty = ret_ty_expr;
        for (pname, pty) in param_exprs.iter().rev() {
            final_ty = Expr::Pi(Name::new(pname), BinderInfo::Default, Rc::new(pty.clone()), Rc::new(final_ty));
        }

        // Check that the theorem type lives in Omega (i.e., is a proposition)
        let mut tc = TypeChecker::with_local_ctx(&mut self.tc_state, super::local_ctx::LocalCtx::new());
        let ty_of_ty = tc.infer(&final_ty).map_err(|e| format!("Cannot infer type of theorem type: {}", e))?;
        let ty_of_ty_whnf = tc.whnf(&ty_of_ty);
        if !matches!(ty_of_ty_whnf, Expr::Omega(_)) {
            return Err(format!(
                "Theorem type must be a proposition (Omega), got {}",
                format_expr(&ty_of_ty_whnf)
            ));
        }

        // Check that the proof matches the theorem type
        tc.check(&final_value, &final_ty)
            .map_err(|e| format!("Proof does not match theorem type: {}", e))?;

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
        self.tc_state = self.tc_state.with_env(self.env.clone());
        self.env_bindings.insert(name.clone(), Expr::mk_const(Name::new(&name), vec![]));
        if !self.quiet {
            println!("  Added theorem: {}", name);
        }
        Ok(())
    }

    fn process_inductive(
        &mut self,
        name: String,
        ctors: Vec<(String, super::repl_parser::ParsedExpr)>,
    ) -> Result<(), String> {
        let ind_name = Name::new(&name);
        let ind_const = Expr::mk_const(ind_name.clone(), vec![]);

        // 1. Type axiom: Name : U
        self.env
            .add(Declaration::Axiom(AxiomVal {
                constant_val: ConstantVal {
                    name: ind_name.clone(),
                    level_params: vec![],
                    ty: Expr::U(Level::Zero),
                },
                is_unsafe: false,
            }))
            .map_err(|e| e)?;
        self.env_bindings.insert(name.clone(), ind_const.clone());

        // 2. Constructor axioms
        let mut ctor_infos: Vec<(Name, Expr, Vec<Expr>)> = Vec::new();
        for (ctor_name_str, ctor_ty_parsed) in &ctors {
            let ctor_ty = ctor_ty_parsed.to_expr(&self.env_bindings, &self.env, &mut Vec::new());
            let ctor_name = ind_name.extend(ctor_name_str);

            // Extract argument types from Pi chain
            let mut args = Vec::new();
            let mut current = &ctor_ty;
            while let Expr::Pi(_, _, domain, body) = current {
                args.push((**domain).clone());
                current = body;
            }
            // Verify return type is the inductive type
            match current {
                Expr::Const(n, _) if *n == ind_name => {}
                _ => {
                    return Err(format!(
                        "Constructor {} return type must be {}",
                        ctor_name_str, name
                    ));
                }
            }

            self.env
                .add(Declaration::Axiom(AxiomVal {
                    constant_val: ConstantVal {
                        name: ctor_name.clone(),
                        level_params: vec![],
                        ty: ctor_ty.clone(),
                    },
                    is_unsafe: false,
                }))
                .map_err(|e| e)?;
            self.env_bindings
                .insert(ctor_name_str.clone(), Expr::mk_const(ctor_name.clone(), vec![]));
            ctor_infos.push((ctor_name, ctor_ty, args));
        }
        self.tc_state = self.tc_state.with_env(self.env.clone());

        // 3. Generate recursor
        let rec_name = Name::new("rec").extend(&name);
        let c_ty = Expr::mk_arrow(ind_const.clone(), Expr::U(Level::Zero));
        let c_depth = ctor_infos.len() as u64;

        // Build recursor body: Π(n:Name). C n
        let mut rec_body: Expr = Expr::Pi(
            Name::new("n"),
            BinderInfo::Default,
            Rc::new(ind_const.clone()),
            Rc::new(Expr::mk_app(Expr::BVar(c_depth + 1), Expr::BVar(0))),
        );

        // Prepend minor premises from last to first
        let mut ctor_rec_infos: Vec<Vec<usize>> = Vec::new();
        for (idx, (ctor_name, _ctor_ty, args)) in ctor_infos.iter().enumerate().rev() {
            let (minor, rec_args) = self.build_minor_premise(ctor_name, args, &ind_name, c_depth)?;
            ctor_rec_infos.push(rec_args);
            rec_body = Expr::Pi(
                Name::new(&format!("m{}", idx)),
                BinderInfo::Default,
                Rc::new(minor),
                Rc::new(rec_body),
            );
        }
        ctor_rec_infos.reverse();

        let rec_ty = Expr::Pi(
            Name::new("C"),
            BinderInfo::Default,
            Rc::new(c_ty),
            Rc::new(rec_body),
        );

        // Recursor as axiom (reduction rules are hard-coded in type checker)
        self.env
            .add(Declaration::Axiom(AxiomVal {
                constant_val: ConstantVal {
                    name: rec_name.clone(),
                    level_params: vec![],
                    ty: rec_ty,
                },
                is_unsafe: false,
            }))
            .map_err(|e| e)?;
        self.env_bindings.insert(
            format!("rec.{}", name),
            Expr::mk_const(rec_name.clone(), vec![]),
        );

        // Register recursor info for iota reduction
        let constructors: Vec<ConstructorInfo> = ctor_infos
            .iter()
            .zip(ctor_rec_infos.iter())
            .map(|((ctor_name, _ctor_ty, args), rec_args)| ConstructorInfo {
                name: ctor_name.clone(),
                num_args: args.len(),
                recursive_args: rec_args.clone(),
            })
            .collect();
        self.tc_state.register_recursor(
            rec_name.clone(),
            RecursorInfo {
                inductive_name: ind_name.clone(),
                constructors,
            },
        );

        if !self.quiet {
            println!(
                "  Added inductive: {} ({} constructors, recursor: {})",
                name,
                ctors.len(),
                rec_name.to_string()
            );
        }
        Ok(())
    }

    /// Build a minor premise for a constructor.
    /// `args` are the constructor argument types.
    /// `c_depth` is the de Bruijn index of C in the final recursor type.
    fn build_minor_premise(
        &self,
        ctor_name: &Name,
        args: &[Expr],
        ind_name: &Name,
        c_depth: u64,
    ) -> Result<(Expr, Vec<usize>), String> {
        // Build ctor application: ctor x0 x1 ...
        let mut ctor_app = Expr::mk_const(ctor_name.clone(), vec![]);
        for i in 0..args.len() {
            ctor_app = Expr::mk_app(ctor_app, Expr::BVar((args.len() - 1 - i) as u64));
        }

        // Result: C (ctor_app)
        let mut result = Expr::mk_app(Expr::BVar(c_depth + args.len() as u64), ctor_app);
        let mut recursive_args = Vec::new();

        // Add argument binders from inside out
        for (i, arg) in args.iter().enumerate().rev() {
            let arg_idx = (args.len() - 1 - i) as u64;

            // If arg type references the inductive type, add a recursive premise
            if arg.contains_const(ind_name) {
                recursive_args.push(i);
                let rec_ty = Expr::mk_app(
                    Expr::BVar(c_depth + args.len() as u64 + 1),
                    Expr::BVar(arg_idx),
                );
                result = Expr::Pi(
                    Name::new(&format!("ih{}", i)),
                    BinderInfo::Default,
                    Rc::new(rec_ty),
                    Rc::new(result),
                );
            }

            result = Expr::Pi(
                Name::new(&format!("x{}", i)),
                BinderInfo::Default,
                Rc::new(arg.clone()),
                Rc::new(result),
            );
        }

        // Reverse to get args in left-to-right order
        recursive_args.reverse();
        Ok((result, recursive_args))
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
        self.tc_state = self.tc_state.with_env(self.env.clone());
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
        let has_type = rest_after_name.starts_with(':');

        let (ty, val_str) = if has_type {
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
            if !rest_after_name.starts_with(":=") {
                return Err("Usage: :def <name> := <value>".to_string());
            }
            (None, rest_after_name[2..].trim().to_string())
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
        self.tc_state = self.tc_state.with_env(self.env.clone());
        self.env_bindings.insert(name.clone(), Expr::mk_const(Name::new(&name), vec![]));
        if !self.quiet {
            println!("  Added definition: {}", name);
        }
        Ok(())
    }

    fn handle_check(&mut self, rest: &str) -> Result<(), String> {
        let parts: Vec<&str> = rest.splitn(2, ':').collect();
        if parts.len() != 2 {
            return Err("Usage: :check <expr> : <type>".to_string());
        }
        let expr_str = parts[0].trim();
        let ty_str = parts[1].trim();

        let expr = self.parse_and_convert(expr_str)?;
        let ty = self.parse_and_convert(ty_str)?;

        let mut tc = TypeChecker::with_local_ctx(&mut self.tc_state, super::local_ctx::LocalCtx::new());
        match tc.check(&expr, &ty) {
            Ok(_) => println!("  ✓ Type checks: {}", format_expr(&ty)),
            Err(e) => println!("  ✗ Type error: {}", e),
        }
        Ok(())
    }

    fn handle_theorem_cmd(&mut self, rest: &str) -> Result<(), String> {
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

        // Check that the theorem type lives in Omega
        let ty_of_ty = tc.infer(&ty).map_err(|e| format!("Cannot infer type of theorem type: {}", e))?;
        let ty_of_ty_whnf = tc.whnf(&ty_of_ty);
        if !matches!(ty_of_ty_whnf, Expr::Omega(_)) {
            return Err(format!(
                "Theorem type must be a proposition (Omega), got {}",
                format_expr(&ty_of_ty_whnf)
            ));
        }

        tc.check(&proof, &ty).map_err(|e| format!("Proof does not match theorem type: {}", e))?;

        let decl = Declaration::Definition(DefinitionVal {
            constant_val: ConstantVal {
                name: Name::new(&name),
                level_params: vec![],
                ty: ty,
            },
            value: proof,
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
        });

        self.env.add(decl).map_err(|e| e)?;
        self.tc_state = self.tc_state.with_env(self.env.clone());
        self.env_bindings.insert(name.clone(), Expr::mk_const(Name::new(&name), vec![]));
        if !self.quiet {
            println!("  Added theorem: {}", name);
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
        println!("  :load <file.ott>              Load declarations from a file");
        println!("  :axiom <name> : <type>        Add an axiom");
        println!("  :def <name> := <value>        Add a definition");
        println!("  :def <name> : <type> := <val> Add a definition with type");
        println!("  :theorem <name> : <type> := <proof>  Add a theorem (type must be in Omega)");
        println!("  :infer <expr>                 Infer the type");
        println!("  :check <expr> : <type>        Check expression against type");
        println!("  :reduce <expr>                Reduce to WHNF");
        println!("  :nf <expr>                    Reduce to full NF");
        println!("  :defeq <e1> = <e2>            Check definitional equality");
        println!("  :help                         Show this help");
        println!("  :quit                         Exit");
        println!();
        println!("Expression syntax:");
        println!("  Constants: Nat, zero, succ, f, x, ...");
        println!("  Application: f a b (left-associative)");
        println!("  Lambda: \\x : Nat . x  or  fun x => x");
        println!("  Pi: Nat -> Nat  or  (x : Nat) -> Nat");
        println!("  Let: let x : Nat := zero in x");
        println!("  Have: have h : Nat := zero in h");
        println!("  Universe: U, U1, U2, ... (proof-relevant)");
        println!("  Universe: Omega, Omega1, ... (proof-irrelevant)");
        println!("  Observational equality: eq(A, t, u)");
        println!("  Cast: cast(A, B, e, t)");
        println!("  Parens: (e)");
        println!();
        println!("File syntax (:load)");
        println!("  def name (params) : type := value");
        println!("  theorem name (params) : type := proof");
        println!("  axiom name : type");
    }

    /// Extract internal state for external tools.
    pub fn into_state(self) -> (Environment, TypeCheckerState, HashMap<String, Expr>) {
        (self.env, self.tc_state, self.env_bindings)
    }
}

/// Pretty-print an Expr for REPL output
pub fn format_expr(e: &Expr) -> String {
    match e {
        Expr::BVar(n) => format!("x{}", n),
        Expr::FVar(name) => name.to_string(),
        Expr::Const(name, _) => name.to_string(),
        Expr::App(_, _) => {
            let (head, args) = e.get_app_args();
            let head_str = if let Some(h) = head {
                match h {
                    Expr::Const(n, _) => n.to_string(),
                    _ => format_expr(h),
                }
            } else {
                "?".to_string()
            };
            let args_str: Vec<String> = args.iter().map(|a| format_expr(*a)).collect();
            format!("{}({})", head_str, args_str.join(", "))
        }
        Expr::Lambda(_, _, ty, body) => {
            format!("λ(_ : {}). {}", format_expr(ty), format_expr(body))
        }
        Expr::Pi(_, _, ty, body) => {
            format!("Π(_ : {}). {}", format_expr(ty), format_expr(body))
        }
        Expr::U(l) => {
            if let Some(n) = l.to_explicit() {
                if n == 0 {
                    "U".to_string()
                } else {
                    format!("U{}", n)
                }
            } else {
                format!("U({:?})", l)
            }
        }
        Expr::Omega(l) => {
            if let Some(n) = l.to_explicit() {
                if n == 0 {
                    "Omega".to_string()
                } else {
                    format!("Omega{}", n)
                }
            } else {
                format!("Omega({:?})", l)
            }
        }
        Expr::Eq(a, t, u) => {
            format!("eq({}, {}, {})", format_expr(a), format_expr(t), format_expr(u))
        }
        Expr::Cast(a, b, proof, term) => {
            format!("cast({}, {}, {}, {})", format_expr(a), format_expr(b), format_expr(proof), format_expr(term))
        }
    }
}
