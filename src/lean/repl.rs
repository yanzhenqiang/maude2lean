use super::declaration::*;
use super::environment::Environment;
use super::expr::*;
use super::maude_bridge::reduce_expr_with_env;
use super::repl_parser::{ParsedDecl, Parser as ReplParser};
use super::type_checker::{TypeChecker, TypeCheckerState};
use std::collections::HashMap;
use std::fs;
use std::io::{self, Write};
use std::rc::Rc;

/// Interactive Lean REPL.
///
/// Commands:
///   :env                          Show current environment
///   :load <file.lean>             Load declarations from a file
///   :axiom <name> : <type>        Add an axiom
///   :def <name> := <value>        Add a definition (type inferred)
///   :def <name> : <type> := <value>  Add a definition with explicit type
///   :theorem <name> : <type> := <proof>  Add a theorem
///   :inductive <name> | <ctor> : <type> | ...   Add an inductive type
///   :infer <expr>                 Infer the type of an expression
///   :reduce <expr>                Reduce to weak head normal form
///   :nf <expr>                    Reduce to full normal form
///   :defeq <e1> = <e2>            Check definitional equality
///   :maude <expr>                 Reduce via Maude engine
///   :help                         Show this help
///   :quit                         Exit
pub struct Repl {
    env: Environment,
    tc_state: TypeCheckerState,
    /// Mapping from user-defined names to their Expr representations
    env_bindings: HashMap<String, Expr>,
}

impl Repl {
    pub fn new() -> Self {
        let env = Environment::new();
        let tc_state = TypeCheckerState::new(env.clone());
        let mut repl = Repl {
            env,
            tc_state,
            env_bindings: HashMap::new(),
        };
        repl.load_nat();
        repl.load_exists();
        repl.load_quot();
        repl
    }

    pub fn run(&mut self) {
        println!("╔═══════════════════════════════════════════════════════════════════════╗");
        println!("║          Lean 4 Kernel Symbolic Execution REPL v0.1                  ║");
        println!("║     Type :help for available commands. Type :quit to exit.          ║");
        println!("╚═══════════════════════════════════════════════════════════════════════╝");
        println!();

        // Pre-populate with Nat and Exists
        println!("Pre-loaded: Nat (inductive), zero : Nat, succ : Nat → Nat");
        println!("Pre-loaded: Exists (inductive), intro : Π(A : Type). Π(P : A → Prop). Π(w : A). P w → Exists A P");
        println!();
        self.load_nat();
        self.load_exists();

        loop {
            print!("lean> ");
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

        if input.starts_with(":maude ") {
            return self.handle_maude(&input[7..]).map(|_| false);
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
        println!("  Loaded {} declarations from {}", count, filepath);
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
                self.tc_state = TypeCheckerState::new(self.env.clone());
                self.env_bindings.insert(name.clone(), Expr::mk_const(Name::new(&name), vec![]));
                println!("  Added axiom: {}", name);
                Ok(())
            }
            ParsedDecl::Def { name, params, ret_ty, value } => {
                self.process_def_or_theorem(name, params, ret_ty, value, false)
            }
            ParsedDecl::Theorem { name, params, ret_ty, value } => {
                self.process_def_or_theorem(name, params, Some(ret_ty), value, true)
            }
            ParsedDecl::Inductive { name, ty, ctors, num_params } => {
                let ty_expr = ty.to_expr(&self.env_bindings, &self.env, &mut Vec::new());
                let mut ctor_exprs = Vec::new();
                for (ctor_name, ctor_ty) in ctors {
                    let ctor_ty_expr = ctor_ty.to_expr(&self.env_bindings, &self.env, &mut Vec::new());
                    ctor_exprs.push(Constructor {
                        name: Name::new(&ctor_name),
                        ty: ctor_ty_expr,
                    });
                }

                let ind = InductiveType {
                    name: Name::new(&name),
                    ty: ty_expr,
                    ctors: ctor_exprs,
                };

                let decl = Declaration::Inductive {
                    level_params: vec![],
                    num_params: num_params as u64,
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

                println!("  Added inductive: {}", name);
                Ok(())
            }
        }
    }

    fn process_def_or_theorem(
        &mut self,
        name: String,
        params: Vec<(String, super::repl_parser::ParsedExpr)>,
        ret_ty: Option<super::repl_parser::ParsedExpr>,
        value: super::repl_parser::ParsedExpr,
        is_theorem: bool,
    ) -> Result<(), String> {
        // Convert parameter types, accumulating bound_vars so later params can reference earlier ones
        let mut param_exprs: Vec<(String, Expr)> = Vec::new();
        let mut bound_vars: Vec<String> = Vec::new();
        for (pname, pty) in &params {
            let ty_expr = pty.to_expr(&self.env_bindings, &self.env, &mut bound_vars);
            param_exprs.push((pname.clone(), ty_expr));
            bound_vars.push(pname.clone());
        }

        // Convert value with parameters in bound_vars
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

        if is_theorem {
            let mut tc = TypeChecker::with_local_ctx(&mut self.tc_state, super::local_ctx::LocalCtx::new());
            tc.check(&final_value, &final_ty)
                .map_err(|e| format!("Proof does not match theorem type: {}", e))?;

            let decl = Declaration::Theorem(TheoremVal {
                constant_val: ConstantVal {
                    name: Name::new(&name),
                    level_params: vec![],
                    ty: final_ty,
                },
                value: final_value,
            });
            self.env.add(decl).map_err(|e| e)?;
            self.tc_state = TypeCheckerState::new(self.env.clone());
            self.env_bindings.insert(name.clone(), Expr::mk_const(Name::new(&name), vec![]));
            println!("  Added theorem: {}", name);
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
            println!("  Added definition: {}", name);
        }
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
        println!("  Added axiom: {}", name);
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
        self.tc_state = TypeCheckerState::new(self.env.clone());
        self.env_bindings.insert(name.clone(), Expr::mk_const(Name::new(&name), vec![]));
        println!("  Added definition: {}", name);
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
        println!("  Added theorem: {}", name);
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

        println!("  Added inductive: {}", name);
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

    fn handle_maude(&mut self, rest: &str) -> Result<(), String> {
        let expr = self.parse_and_convert(rest)?;
        let result = reduce_expr_with_env(&expr, &self.env).map_err(|e| e)?;
        println!("  {}", format_expr(&result));
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
        println!("  :load <file.lean>             Load declarations from a file");
        println!("  :axiom <name> : <type>        Add an axiom");
        println!("  :def <name> := <value>        Add a definition");
        println!("  :def <name> : <type> := <val> Add a definition with type");
        println!("  :theorem <name> : <type> := <proof>  Add a theorem");
        println!("  :inductive <name> | <c>:<t>|..Add an inductive type");
        println!("  :infer <expr>                 Infer the type");
        println!("  :reduce <expr>                Reduce to WHNF");
        println!("  :nf <expr>                    Reduce to full NF");
        println!("  :defeq <e1> = <e2>            Check definitional equality");
        println!("  :maude <expr>                 Reduce via Maude engine");
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

    fn load_nat(&mut self) {
        let nat = Expr::mk_const(Name::new("Nat"), vec![]);
        let ind = InductiveType {
            name: Name::new("Nat"),
            ty: Expr::mk_type(),
            ctors: vec![
                Constructor { name: Name::new("zero"), ty: nat.clone() },
                Constructor { name: Name::new("succ"), ty: Expr::mk_arrow(nat.clone(), nat.clone()) },
            ],
        };
        let _ = self.env.add(Declaration::Inductive {
            level_params: vec![],
            num_params: 0,
            types: vec![ind],
            is_unsafe: false,
        });

        self.tc_state = TypeCheckerState::new(self.env.clone());
        self.env_bindings.insert("Nat".to_string(), Expr::mk_const(Name::new("Nat"), vec![]));
        self.env_bindings.insert("zero".to_string(), Expr::mk_const(Name::new("zero"), vec![]));
        self.env_bindings.insert("succ".to_string(), Expr::mk_const(Name::new("succ"), vec![]));
        self.env_bindings.insert("rec.Nat".to_string(), Expr::mk_const(Name::new("rec").extend("Nat"), vec![]));
    }

    fn load_exists(&mut self) {
        let prop = Expr::mk_sort(Level::Zero);
        let ty = Expr::mk_type();
        // Exists : Π (A : Type), Π (P : A → Prop), Prop
        let exists_ty = Expr::mk_pi(Name::new("A"), ty.clone(),
            Expr::mk_pi(Name::new("P"),
                Expr::mk_pi(Name::new("_"), Expr::mk_bvar(0), prop.clone()),
                prop.clone()));

        // intro : Π (A : Type), Π (P : A → Prop), Π (w : A), Π (h : P w), Exists A P
        let h_ty = Expr::mk_app(Expr::mk_bvar(1), Expr::mk_bvar(0));
        let ret_ty = Expr::mk_app(
            Expr::mk_app(
                Expr::mk_const(Name::new("Exists"), vec![]),
                Expr::mk_bvar(3),
            ),
            Expr::mk_bvar(2),
        );
        let intro_ty = Expr::mk_pi(Name::new("A"), ty.clone(),
            Expr::mk_pi(Name::new("P"),
                Expr::mk_pi(Name::new("_"), Expr::mk_bvar(0), prop.clone()),
                Expr::mk_pi(Name::new("w"), Expr::mk_bvar(1),
                    Expr::mk_pi(Name::new("h"), h_ty, ret_ty))));

        let ind = InductiveType {
            name: Name::new("Exists"),
            ty: exists_ty,
            ctors: vec![
                Constructor { name: Name::new("intro"), ty: intro_ty },
            ],
        };
        let _ = self.env.add(Declaration::Inductive {
            level_params: vec![],
            num_params: 0,
            types: vec![ind],
            is_unsafe: false,
        });

        self.tc_state = TypeCheckerState::new(self.env.clone());
        self.env_bindings.insert("Exists".to_string(), Expr::mk_const(Name::new("Exists"), vec![]));
        self.env_bindings.insert("intro".to_string(), Expr::mk_const(Name::new("intro"), vec![]));
        self.env_bindings.insert("rec.Exists".to_string(), Expr::mk_const(Name::new("rec").extend("Exists"), vec![]));
    }

    fn load_quot(&mut self) {
        let _ = self.env.add(Declaration::Quot);
        self.tc_state = TypeCheckerState::new(self.env.clone());
        self.env_bindings.insert("Quot".to_string(), Expr::mk_const(Name::new("Quot"), vec![]));
        self.env_bindings.insert("Quot.mk".to_string(), Expr::mk_const(Name::new("Quot").extend("mk"), vec![]));
        self.env_bindings.insert("Quot.lift".to_string(), Expr::mk_const(Name::new("Quot").extend("lift"), vec![]));
        self.env_bindings.insert("Quot.ind".to_string(), Expr::mk_const(Name::new("Quot").extend("ind"), vec![]));
    }
}

/// Pretty-print an Expr for REPL output
pub fn format_expr(e: &Expr) -> String {
    match e {
        Expr::BVar(n) => format!("x{}", n),
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
        Expr::Let(_, ty, val, body, _) => {
            format!("let _ : {} := {} in {}", format_expr(ty), format_expr(val), format_expr(body))
        }
        Expr::Sort(l) => format!("Sort({:?})", l),
        Expr::Lit(Literal::Nat(n)) => n.to_string(),
        _ => format!("{:?}", e),
    }
}
