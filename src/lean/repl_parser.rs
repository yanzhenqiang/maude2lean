use super::environment::Environment;
use super::expr::*;
use std::collections::HashMap;
use std::rc::Rc;

/// A simple parser for Lean-like expressions in the REPL.
///
/// Supported syntax:
///   - Constants/variables: Nat, zero, succ, x
///   - Application: f a b (left-associative)
///   - Lambda: \x : Nat . x   or   fun x => x
///   - Pi: Nat -> Nat   or   (x : Nat) -> Nat
///   - Let: let x := zero in x   or   let x : Nat := zero in x
///   - Have: have h : P := proof in e
///   - Match: match e : T with | ctor1 => e1 | ctor2 x => e2
///   - Sort: Type, Prop
///   - Parens: (e)
///   - Nat literals: 0, 1, 2, ...

#[derive(Debug, Clone)]
pub enum ParsedExpr {
    BVar(u64),
    Const(String),
    App(Box<ParsedExpr>, Box<ParsedExpr>),
    Lambda(String, Box<ParsedExpr>, Box<ParsedExpr>), // name, type, body
    Pi(String, Box<ParsedExpr>, Box<ParsedExpr>),     // name, type, body
    Let(String, Box<ParsedExpr>, Box<ParsedExpr>, Box<ParsedExpr>), // name, ty, val, body
    Sort(u64), // 0 = Prop, 1 = Type
    NatLit(u64),
    /// match scrutinee : motive with | pat1 => e1 | pat2 x => e2
    Match(Box<ParsedExpr>, Box<ParsedExpr>, Vec<(ParsedExpr, ParsedExpr)>),
}

impl ParsedExpr {
    /// Convert parsed expression to Expr, resolving names via environment.
    /// `env_bindings` maps user-facing names to Expr constants.
    /// `env` is the kernel Environment for looking up constructors/recursors.
    /// `bound_vars` maps local bound variable names to de Bruijn indices.
    pub fn to_expr(&self, env_bindings: &HashMap<String, Expr>, env: &Environment, bound_vars: &mut Vec<String>) -> Expr {
        match self {
            ParsedExpr::BVar(n) => Expr::mk_bvar(*n),
            ParsedExpr::Const(name) => {
                // Check bound variables first (de Bruijn index = distance from right/end)
                for (i, bv) in bound_vars.iter().enumerate().rev() {
                    if bv == name {
                        return Expr::mk_bvar((bound_vars.len() - 1 - i) as u64);
                    }
                }
                // Check environment constants
                if let Some(e) = env_bindings.get(name) {
                    return e.clone();
                }
                // Parse hierarchical names like "rec.Nat"
                let name_parts: Vec<&str> = name.split('.').collect();
                let mut lean_name = Name::new(name_parts[0]);
                for part in &name_parts[1..] {
                    lean_name = lean_name.extend(part);
                }
                Expr::mk_const(lean_name, vec![])
            }
            ParsedExpr::App(f, a) => {
                let f_expr = f.to_expr(env_bindings, env, bound_vars);
                let a_expr = a.to_expr(env_bindings, env, bound_vars);
                Expr::mk_app(f_expr, a_expr)
            }
            ParsedExpr::Lambda(name, ty, body) => {
                let ty_expr = ty.to_expr(env_bindings, env, bound_vars);
                bound_vars.push(name.clone());
                let body_expr = body.to_expr(env_bindings, env, bound_vars);
                bound_vars.pop();
                Expr::Lambda(Name::new(name), BinderInfo::Default, Rc::new(ty_expr), Rc::new(body_expr))
            }
            ParsedExpr::Pi(name, ty, body) => {
                let ty_expr = ty.to_expr(env_bindings, env, bound_vars);
                bound_vars.push(name.clone());
                let body_expr = body.to_expr(env_bindings, env, bound_vars);
                bound_vars.pop();
                Expr::Pi(Name::new(name), BinderInfo::Default, Rc::new(ty_expr), Rc::new(body_expr))
            }
            ParsedExpr::Let(name, ty, val, body) => {
                let ty_expr = ty.to_expr(env_bindings, env, bound_vars);
                let val_expr = val.to_expr(env_bindings, env, bound_vars);
                bound_vars.push(name.clone());
                let body_expr = body.to_expr(env_bindings, env, bound_vars);
                bound_vars.pop();
                Expr::Let(Name::new(name), Rc::new(ty_expr), Rc::new(val_expr), Rc::new(body_expr), false)
            }
            ParsedExpr::Sort(u) => {
                if *u == 0 {
                    Expr::mk_prop()
                } else {
                    Expr::mk_type()
                }
            }
            ParsedExpr::NatLit(n) => Expr::Lit(Literal::Nat(*n)),
            ParsedExpr::Match(scrutinee, motive, branches) => {
                self.desugar_match(scrutinee, motive, branches, env_bindings, env, bound_vars)
            }
        }
    }

    fn desugar_match(&self, scrutinee: &ParsedExpr, motive: &ParsedExpr, branches: &[(ParsedExpr, ParsedExpr)], env_bindings: &HashMap<String, Expr>, env: &Environment, bound_vars: &mut Vec<String>) -> Expr {
        // Extract constructor info from first pattern
        let (first_ctor_name, _) = extract_ctor_and_vars(&branches[0].0);
        let ctor_name_obj = Name::new(&first_ctor_name);

        let ctor_info = match env.find(&ctor_name_obj) {
            Some(info) => info,
            None => panic!("Constructor not found in environment: {}", first_ctor_name),
        };
        let ctor_val = match ctor_info.to_constructor_val() {
            Some(v) => v,
            None => panic!("Not a constructor: {}", first_ctor_name),
        };
        let induct_name = ctor_val.induct.clone();

        // Find recursor
        let rec_name = Name::new("rec").extend(&induct_name.to_string());
        let rec_info = match env.find(&rec_name) {
            Some(info) => info,
            None => panic!("Recursor not found: {}", rec_name.to_string()),
        };
        let _rec_val = match rec_info.to_recursor_val() {
            Some(v) => v,
            None => panic!("Not a recursor: {}", rec_name.to_string()),
        };

        // Get all constructor names in order
        let ind_info = match env.find(&induct_name) {
            Some(info) => info,
            None => panic!("Inductive type not found: {}", induct_name.to_string()),
        };
        let ind_val = match ind_info.to_inductive_val() {
            Some(v) => v,
            None => panic!("Not an inductive type: {}", induct_name.to_string()),
        };
        let all_ctors = ind_val.ctors.clone();

        // Build motive lambda: λ (_m : induct_ty) . motive_expr
        let induct_ty_expr = Expr::mk_const(induct_name.clone(), vec![]);
        let motive_expr = motive.to_expr(env_bindings, env, bound_vars);
        let motive_lambda = Expr::Lambda(
            Name::new("_m"), BinderInfo::Default,
            Rc::new(induct_ty_expr),
            Rc::new(motive_expr.clone()),
        );

        // Build minors for each constructor
        let mut minors = Vec::new();
        for ctor_name in &all_ctors {
            let ctor_name_str = ctor_name.to_string();
            let branch = branches.iter()
                .find(|(pat, _)| {
                    let (c, _) = extract_ctor_and_vars(pat);
                    c == ctor_name_str
                })
                .unwrap_or_else(|| panic!("Missing branch for constructor: {}", ctor_name_str));

            let (_, vars) = extract_ctor_and_vars(&branch.0);
            let param_types = get_ctor_param_types(env, ctor_name);

            // Bind pattern variables
            for var in &vars {
                bound_vars.push(var.clone());
            }
            let body_expr = branch.1.to_expr(env_bindings, env, bound_vars);
            for _ in &vars {
                bound_vars.pop();
            }

            let mut minor = body_expr;

            // For constructors with recursive fields, add ih lambdas BEFORE pattern variable lambdas.
            // ih is innermost because it binds over the branch body, while pattern variables
            // bind over both the body and ih.
            for param_ty in param_types.iter().rev() {
                if expr_contains_const(param_ty, &induct_name) {
                    let ih_ty = motive_expr.clone();
                    minor = minor.lift_loose_bvars(1, 0);
                    minor = Expr::Lambda(Name::new("ih"), BinderInfo::Default, Rc::new(ih_ty), Rc::new(minor));
                }
            }

            // Wrap with lambdas for pattern variables (in reverse order)
            for (i, var) in vars.iter().enumerate().rev() {
                let ty = if i < param_types.len() {
                    param_types[i].clone()
                } else {
                    Expr::mk_type() // fallback
                };
                minor = Expr::Lambda(Name::new(var), BinderInfo::Default, Rc::new(ty), Rc::new(minor));
            }

            minors.push(minor);
        }

        // Build recursor application: rec motive minor_0 minor_1 ... scrutinee
        let mut app = Expr::mk_const(rec_name, vec![]);
        app = Expr::mk_app(app, motive_lambda);
        for minor in minors {
            app = Expr::mk_app(app, minor);
        }
        let scrut_expr = scrutinee.to_expr(env_bindings, env, bound_vars);
        Expr::mk_app(app, scrut_expr)
    }
}

/// Extract constructor name and bound variable names from a pattern.
/// e.g., `zero` -> ("zero", []), `succ n` -> ("succ", ["n"]), `ofNat m` -> ("ofNat", ["m"])
fn extract_ctor_and_vars(pat: &ParsedExpr) -> (String, Vec<String>) {
    match pat {
        ParsedExpr::Const(name) => (name.clone(), vec![]),
        ParsedExpr::App(f, a) => {
            let (ctor, mut vars) = extract_ctor_and_vars(f);
            match a.as_ref() {
                ParsedExpr::Const(var) => vars.push(var.clone()),
                _ => panic!("Pattern must be a constructor applied to variables, got {:?}", a),
            }
            (ctor, vars)
        }
        _ => panic!("Invalid pattern: {:?}", pat),
    }
}

/// Get the parameter types of a constructor from the environment.
fn get_ctor_param_types(env: &Environment, ctor_name: &Name) -> Vec<Expr> {
    let ctor_info = env.find(ctor_name).expect("Constructor not found");
    let ctor_val = ctor_info.to_constructor_val().expect("Not a constructor");
    let mut domains = Vec::new();
    let mut current = &ctor_val.constant_val.ty;
    while let Expr::Pi(_, _, domain, body) = current {
        domains.push((**domain).clone());
        current = body;
    }
    domains
}

/// Check if an expression contains a reference to a given constant name.
fn expr_contains_const(e: &Expr, name: &Name) -> bool {
    match e {
        Expr::Const(n, _) => n == name,
        Expr::App(f, a) => expr_contains_const(f, name) || expr_contains_const(a, name),
        Expr::Lambda(_, _, ty, body) => expr_contains_const(ty, name) || expr_contains_const(body, name),
        Expr::Pi(_, _, ty, body) => expr_contains_const(ty, name) || expr_contains_const(body, name),
        Expr::Let(_, ty, val, body, _) => expr_contains_const(ty, name) || expr_contains_const(val, name) || expr_contains_const(body, name),
        Expr::Proj(_, _, e) => expr_contains_const(e, name),
        Expr::MData(_, e) => expr_contains_const(e, name),
        _ => false,
    }
}

/// A parsed top-level declaration.
#[derive(Debug, Clone)]
pub enum ParsedDecl {
    Def {
        name: String,
        params: Vec<(String, ParsedExpr)>, // (param_name, param_type)
        ret_ty: Option<ParsedExpr>,
        value: ParsedExpr,
    },
    Theorem {
        name: String,
        params: Vec<(String, ParsedExpr)>,
        ret_ty: ParsedExpr,
        value: ParsedExpr,
    },
    Inductive {
        name: String,
        ty: ParsedExpr,
        ctors: Vec<(String, ParsedExpr)>,
        num_params: usize,
    },
    Axiom {
        name: String,
        ty: ParsedExpr,
    },
}

#[derive(Debug, Clone)]
pub struct Parser {
    input: Vec<char>,
    pos: usize,
}

impl Parser {
    pub fn new(input: &str) -> Self {
        Parser {
            input: input.chars().collect(),
            pos: 0,
        }
    }

    /// Parse a single expression.
    pub fn parse_expr(&mut self) -> Result<ParsedExpr, String> {
        self.parse_pi_or_arrow()
    }

    /// Parse a file into a list of declarations.
    pub fn parse_file(&mut self) -> Result<Vec<ParsedDecl>, String> {
        let mut decls = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek().is_none() {
                break;
            }
            let decl = self.parse_decl()?;
            decls.push(decl);
        }
        Ok(decls)
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            self.skip_whitespace();
            // Skip line comments: -- ...\n
            if self.peek() == Some('-') && self.input.get(self.pos + 1) == Some(&'-') {
                while let Some(c) = self.peek() {
                    self.advance();
                    if c == '\n' {
                        break;
                    }
                }
                continue;
            }
            // Skip block comments: /- ... -/
            if self.peek() == Some('/') && self.input.get(self.pos + 1) == Some(&'-') {
                self.advance();
                self.advance();
                let mut depth = 1;
                while depth > 0 {
                    if let Some(c) = self.peek() {
                        if c == '/' && self.input.get(self.pos + 1) == Some(&'-') {
                            self.advance();
                            self.advance();
                            depth += 1;
                        } else if c == '-' && self.input.get(self.pos + 1) == Some(&'/') {
                            self.advance();
                            self.advance();
                            depth -= 1;
                        } else {
                            self.advance();
                        }
                    } else {
                        break;
                    }
                }
                continue;
            }
            break;
        }
    }

    fn parse_decl(&mut self) -> Result<ParsedDecl, String> {
        self.skip_whitespace_and_comments();
        if self.starts_with_keyword("def") {
            self.parse_def_decl()
        } else if self.starts_with_keyword("theorem") {
            self.parse_theorem_decl()
        } else if self.starts_with_keyword("inductive") {
            self.parse_inductive_decl()
        } else if self.starts_with_keyword("axiom") {
            self.parse_axiom_decl()
        } else {
            Err(format!("Expected declaration, got {:?}", self.peek()))
        }
    }

    fn parse_def_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(3); // consume "def"
        self.skip_whitespace();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        let (params, ret_ty, value) = self.parse_decl_body()?;
        Ok(ParsedDecl::Def { name, params, ret_ty, value })
    }

    fn parse_theorem_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(7); // consume "theorem"
        self.skip_whitespace();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        let (params, ret_ty, value) = self.parse_decl_body()?;
        let ret_ty = ret_ty.ok_or("Theorem must have an explicit return type".to_string())?;
        Ok(ParsedDecl::Theorem { name, params, ret_ty, value })
    }

    fn parse_axiom_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(5); // consume "axiom"
        self.skip_whitespace();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        if self.peek() != Some(':') {
            return Err("Expected ':' after axiom name".to_string());
        }
        self.advance();
        let ty = self.parse_pi_or_arrow()?;
        Ok(ParsedDecl::Axiom { name, ty })
    }

    /// Parse the common body of def/theorem: params [: ret_ty] := value
    fn parse_decl_body(&mut self) -> Result<(Vec<(String, ParsedExpr)>, Option<ParsedExpr>, ParsedExpr), String> {
        // Parse optional parameters: (x : T) or {x : T}
        let mut params = Vec::new();
        while self.peek() == Some('(') || self.peek() == Some('{') {
            let implicit = self.peek() == Some('{');
            self.advance(); // consume '(' or '{'
            let pname = self.parse_ident_raw()?;
            self.skip_whitespace();
            if self.peek() != Some(':') {
                return Err("Expected ':' in parameter".to_string());
            }
            self.advance();
            let pty = self.parse_pi_or_arrow()?;
            self.skip_whitespace();
            let close = if implicit { '}' } else { ')' };
            if self.peek() != Some(close) {
                return Err(format!("Expected '{}'", close));
            }
            self.advance();
            params.push((pname, pty));
            self.skip_whitespace();
        }

        // Optional return type (distinguish ':' from ':=')
        let ret_ty = if self.peek() == Some(':') && self.input.get(self.pos + 1) != Some(&'=') {
            self.advance();
            Some(self.parse_pi_or_arrow()?)
        } else {
            None
        };

        self.skip_whitespace();
        if !self.starts_with_keyword(":=") {
            return Err("Expected ':=' in declaration".to_string());
        }
        self.advance_by(2);
        let value = self.parse_expr()?;

        Ok((params, ret_ty, value))
    }

    fn parse_inductive_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(9); // consume "inductive"
        self.skip_whitespace();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        // Parse optional parameters
        let mut params = Vec::new();
        while self.peek() == Some('(') || self.peek() == Some('{') {
            let implicit = self.peek() == Some('{');
            self.advance();
            let pname = self.parse_ident_raw()?;
            self.skip_whitespace();
            if self.peek() != Some(':') {
                return Err("Expected ':' in parameter".to_string());
            }
            self.advance();
            let pty = self.parse_pi_or_arrow()?;
            self.skip_whitespace();
            let close = if implicit { '}' } else { ')' };
            if self.peek() != Some(close) {
                return Err(format!("Expected '{}'", close));
            }
            self.advance();
            params.push((pname, pty));
            self.skip_whitespace();
        }

        // Return type (usually Type or Prop)
        let ty = if self.peek() == Some(':') {
            self.advance();
            self.parse_pi_or_arrow()?
        } else {
            ParsedExpr::Sort(1) // default to Type
        };

        self.skip_whitespace();
        if !self.starts_with_keyword("where") {
            return Err("Expected 'where' after inductive type".to_string());
        }
        self.advance_by(5);
        self.skip_whitespace();

        // Parse constructors: | ctor : type | ctor : type
        let mut ctors = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek() != Some('|') {
                break;
            }
            self.advance(); // consume '|'
            self.skip_whitespace();
            let ctor_name = self.parse_ident_raw()?;
            self.skip_whitespace();
            if self.peek() != Some(':') {
                return Err("Expected ':' in constructor".to_string());
            }
            self.advance();
            let ctor_ty = self.parse_pi_or_arrow()?;
            ctors.push((ctor_name, ctor_ty));
        }

        // Wrap constructor types with parameters if any
        let final_ty = if params.is_empty() {
            ty
        } else {
            let mut result = ty;
            for (pname, pty) in params.iter().rev() {
                result = ParsedExpr::Pi(pname.clone(), Box::new(pty.clone()), Box::new(result));
            }
            result
        };

        let final_ctors = ctors.into_iter().map(|(n, t)| {
            if params.is_empty() {
                (n, t)
            } else {
                let mut ct = t;
                for (pname, pty) in params.iter().rev() {
                    ct = ParsedExpr::Pi(pname.clone(), Box::new(pty.clone()), Box::new(ct));
                }
                (n, ct)
            }
        }).collect();

        Ok(ParsedDecl::Inductive { name, ty: final_ty, ctors: final_ctors, num_params: params.len() })
    }

    fn peek(&self) -> Option<char> {
        self.input.get(self.pos).copied()
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    fn consume(&mut self, expected: char) -> Result<(), String> {
        self.skip_whitespace();
        if let Some(c) = self.peek() {
            if c == expected {
                self.advance();
                return Ok(());
            }
        }
        Err(format!("Expected '{}', got {:?}", expected, self.peek()))
    }

    fn parse_pi_or_arrow(&mut self) -> Result<ParsedExpr, String> {
        self.skip_whitespace();

        // Check for dependent pi: (x : A) -> B
        if self.peek() == Some('(') {
            let saved_pos = self.pos;
            self.advance(); // consume '('
            self.skip_whitespace();

            // Try to parse as dependent pi
            if let Ok(name) = self.parse_ident_raw() {
                self.skip_whitespace();
                if self.peek() == Some(':') {
                    self.advance(); // consume ':'
                    let ty = self.parse_pi_or_arrow()?;
                    self.consume(')')?;
                    self.skip_whitespace();

                    if self.peek() == Some('-') && self.input.get(self.pos + 1) == Some(&'>') {
                        self.advance();
                        self.advance();
                        let body = self.parse_pi_or_arrow()?;
                        return Ok(ParsedExpr::Pi(name, Box::new(ty), Box::new(body)));
                    }
                }
            }

            // Not a pi, restore and parse as parens
            self.pos = saved_pos;
        }

        let left = self.parse_infix(0)?;
        self.skip_whitespace();

        // Arrow: A -> B
        if self.peek() == Some('-') && self.input.get(self.pos + 1) == Some(&'>') {
            self.advance();
            self.advance();
            let right = self.parse_pi_or_arrow()?;
            return Ok(ParsedExpr::Pi("_".to_string(), Box::new(left), Box::new(right)));
        }

        Ok(left)
    }

    /// Parse infix operators (+, -, *) with precedence climbing.
    fn parse_infix(&mut self, min_prec: i32) -> Result<ParsedExpr, String> {
        let mut left = self.parse_app_or_atom()?;
        loop {
            self.skip_whitespace_and_comments();

            // Determine operator and precedence
            let (op, prec) = if self.peek() == Some('+') {
                ("+", 6)
            } else if self.peek() == Some('-') {
                // Distinguish from arrow ->
                if self.input.get(self.pos + 1) == Some(&'>') {
                    break;
                }
                ("-", 6)
            } else if self.peek() == Some('*') {
                ("*", 7)
            } else {
                break;
            };

            if prec < min_prec {
                break;
            }

            self.advance(); // consume operator

            // Left-associative: right side needs higher precedence
            let right = self.parse_infix(prec + 1)?;

            // Desugar a + b to add a b
            let op_name = match op {
                "+" => "add",
                "-" => "sub",
                "*" => "mul",
                _ => op,
            };

            left = ParsedExpr::App(
                Box::new(ParsedExpr::App(
                    Box::new(ParsedExpr::Const(op_name.to_string())),
                    Box::new(left),
                )),
                Box::new(right),
            );
        }
        Ok(left)
    }

    fn parse_app_or_atom(&mut self) -> Result<ParsedExpr, String> {
        let mut atoms = vec![self.parse_atom()?];

        loop {
            self.skip_whitespace_and_comments();
            let c = self.peek();
            if c.is_none() || c == Some(')') || c == Some('.') || c == Some(',')
                || c == Some(':') || c == Some('=') || c == Some('|')
                || (c == Some('-') && self.input.get(self.pos + 1) == Some(&'>'))
                || c == Some('}') || c == Some('{')
                || c == Some('+') || c == Some('-') || c == Some('*') {
                break;
            }
            // Keywords that end the application chain
            if self.starts_with_keyword("in") || self.starts_with_keyword("with") || self.starts_with_keyword("where")
                || self.starts_with_keyword("def") || self.starts_with_keyword("theorem")
                || self.starts_with_keyword("inductive") || self.starts_with_keyword("axiom")
                || self.starts_with_keyword("postulate") || self.starts_with_keyword("module") {
                break;
            }
            atoms.push(self.parse_atom()?);
        }

        if atoms.len() == 1 {
            Ok(atoms.into_iter().next().unwrap())
        } else {
            let mut result = atoms[0].clone();
            for atom in atoms.into_iter().skip(1) {
                result = ParsedExpr::App(Box::new(result), Box::new(atom));
            }
            Ok(result)
        }
    }

    fn parse_atom(&mut self) -> Result<ParsedExpr, String> {
        self.skip_whitespace();
        let c = self.peek();

        match c {
            None => Err("Unexpected end of input".to_string()),
            Some('(') => {
                self.advance();
                let expr = self.parse_expr()?;
                self.consume(')')?;
                Ok(expr)
            }
            Some('\\') => self.parse_lambda(),
            Some('0'..='9') => self.parse_nat_lit(),
            Some(_) => {
                if self.starts_with_keyword("fun") {
                    self.parse_fun()
                } else if self.starts_with_keyword("let") {
                    self.parse_let()
                } else if self.starts_with_keyword("have") {
                    self.parse_have()
                } else if self.starts_with_keyword("match") {
                    self.parse_match()
                } else if self.starts_with_keyword("forall") {
                    self.parse_forall()
                } else if self.starts_with_keyword("exists") {
                    self.parse_exists()
                } else if self.starts_with_keyword("Type") {
                    self.advance_by(4);
                    Ok(ParsedExpr::Sort(1))
                } else if self.starts_with_keyword("Prop") {
                    self.advance_by(4);
                    Ok(ParsedExpr::Sort(0))
                } else {
                    self.parse_ident_or_bvar()
                }
            }
        }
    }

    fn parse_lambda(&mut self) -> Result<ParsedExpr, String> {
        self.advance(); // consume '\'
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        let ty = if self.peek() == Some(':') {
            self.advance();
            self.parse_pi_or_arrow()?
        } else {
            ParsedExpr::Const("?".to_string())
        };

        self.skip_whitespace();
        self.consume('.')?;
        let body = self.parse_expr()?;

        Ok(ParsedExpr::Lambda(name, Box::new(ty), Box::new(body)))
    }

    fn parse_fun(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(3); // consume "fun"
        self.skip_whitespace();

        // Parse one or more parameter names
        let mut params = vec![self.parse_ident_raw()?];
        self.skip_whitespace();

        // Additional parameters for multi-param lambda: fun x y z => body
        while self.peek() != Some(':') && !self.starts_with_keyword("=>") {
            if let Some(c) = self.peek() {
                if c.is_alphanumeric() || c == '_' || c == '\'' {
                    params.push(self.parse_ident_raw()?);
                    self.skip_whitespace();
                    continue;
                }
            }
            break;
        }

        let ty = if self.peek() == Some(':') {
            self.advance();
            self.parse_pi_or_arrow()?
        } else {
            ParsedExpr::Const("?".to_string())
        };

        self.skip_whitespace();
        if self.starts_with_keyword("=>") {
            self.advance_by(2);
        } else {
            return Err("Expected '=>' after fun parameter".to_string());
        }

        let mut body = self.parse_expr()?;
        let first_param = params[0].clone();

        // Nest lambdas for multiple parameters: fun x y z => body ~ fun x => fun y => fun z => body
        for param in params.into_iter().skip(1).rev() {
            body = ParsedExpr::Lambda(param, Box::new(ParsedExpr::Const("?".to_string())), Box::new(body));
        }

        Ok(ParsedExpr::Lambda(first_param, Box::new(ty), Box::new(body)))
    }

    fn parse_let(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(3); // consume "let"
        self.skip_whitespace();

        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        let (ty, val) = if self.peek() == Some(':') && self.input.get(self.pos + 1) != Some(&'=') {
            self.advance();
            let ty = self.parse_pi_or_arrow()?;
            self.skip_whitespace();
            if !self.starts_with_keyword(":=") {
                return Err("Expected ':=' in let binding".to_string());
            }
            self.advance_by(2);
            let val = self.parse_expr()?;
            (ty, val)
        } else {
            self.skip_whitespace();
            if !self.starts_with_keyword(":=") {
                return Err("Expected ':=' in let binding".to_string());
            }
            self.advance_by(2);
            let val = self.parse_expr()?;
            (ParsedExpr::Const("?".to_string()), val)
        };

        self.skip_whitespace();
        if !self.starts_with_keyword("in") {
            return Err("Expected 'in' after let binding".to_string());
        }
        self.advance_by(2);
        let body = self.parse_expr()?;

        Ok(ParsedExpr::Let(name, Box::new(ty), Box::new(val), Box::new(body)))
    }

    fn parse_have(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(4); // consume "have"
        self.skip_whitespace();

        let name = self.parse_ident_raw()?;
        self.skip_whitespace();

        let (ty, val) = if self.peek() == Some(':') && self.input.get(self.pos + 1) != Some(&'=') {
            self.advance();
            let ty = self.parse_pi_or_arrow()?;
            self.skip_whitespace();
            if !self.starts_with_keyword(":=") {
                return Err("Expected ':=' in have binding".to_string());
            }
            self.advance_by(2);
            let val = self.parse_expr()?;
            (ty, val)
        } else {
            self.skip_whitespace();
            if !self.starts_with_keyword(":=") {
                return Err("Expected ':=' in have binding".to_string());
            }
            self.advance_by(2);
            let val = self.parse_expr()?;
            (ParsedExpr::Const("?".to_string()), val)
        };

        self.skip_whitespace();
        if !self.starts_with_keyword("in") {
            return Err("Expected 'in' after have binding".to_string());
        }
        self.advance_by(2);
        let body = self.parse_expr()?;

        Ok(ParsedExpr::Let(name, Box::new(ty), Box::new(val), Box::new(body)))
    }

    fn parse_match(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(5); // consume "match"
        self.skip_whitespace();

        let scrutinee = self.parse_expr()?;
        self.skip_whitespace();

        if self.peek() != Some(':') {
            return Err("Expected ':' after match scrutinee (match e : T with ...)".to_string());
        }
        self.advance();
        let motive = self.parse_expr()?;
        self.skip_whitespace();

        if !self.starts_with_keyword("with") {
            return Err("Expected 'with' after match motive".to_string());
        }
        self.advance_by(4);
        self.skip_whitespace();

        // Parse branches: | pat => expr | pat => expr
        let mut branches = Vec::new();
        loop {
            self.skip_whitespace();
            if self.peek() != Some('|') {
                break;
            }
            self.advance(); // consume '|'
            self.skip_whitespace();

            // Parse pattern: ctor or ctor var
            let pat = self.parse_pattern()?;
            self.skip_whitespace();

            if self.peek() != Some('=') || self.input.get(self.pos + 1) != Some(&'>') {
                return Err("Expected '=>' after pattern".to_string());
            }
            self.advance_by(2);
            let body = self.parse_expr()?;
            branches.push((pat, body));
            self.skip_whitespace();
        }

        if branches.is_empty() {
            return Err("Match must have at least one branch".to_string());
        }

        Ok(ParsedExpr::Match(Box::new(scrutinee), Box::new(motive), branches))
    }

    /// Parse forall: forall (x : A), B  or  forall (x : A) -> B
    fn parse_forall(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(7); // consume "forall"
        self.skip_whitespace();

        if self.peek() != Some('(') && self.peek() != Some('{') {
            return Err("Expected '(' or '{' after forall".to_string());
        }
        let implicit = self.peek() == Some('{');
        self.advance();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();
        if self.peek() != Some(':') {
            return Err("Expected ':' in forall binder".to_string());
        }
        self.advance();
        let ty = self.parse_pi_or_arrow()?;
        let close = if implicit { '}' } else { ')' };
        if self.peek() != Some(close) {
            return Err(format!("Expected '{}'", close));
        }
        self.advance();

        self.skip_whitespace();
        // Optional comma or arrow
        if self.peek() == Some(',') {
            self.advance();
        } else if self.peek() == Some('-') && self.input.get(self.pos + 1) == Some(&'>') {
            self.advance();
            self.advance();
        }

        let body = self.parse_pi_or_arrow()?;
        Ok(ParsedExpr::Pi(name, Box::new(ty), Box::new(body)))
    }

    /// Parse exists: exists (x : A), B  desugars to Exists A (\x : A . B)
    fn parse_exists(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(6); // consume "exists"
        self.skip_whitespace();

        if self.peek() != Some('(') && self.peek() != Some('{') {
            return Err("Expected '(' or '{' after exists".to_string());
        }
        let implicit = self.peek() == Some('{');
        self.advance();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();
        if self.peek() != Some(':') {
            return Err("Expected ':' in exists binder".to_string());
        }
        self.advance();
        let ty = self.parse_pi_or_arrow()?;
        let close = if implicit { '}' } else { ')' };
        if self.peek() != Some(close) {
            return Err(format!("Expected '{}'", close));
        }
        self.advance();

        self.skip_whitespace();
        if self.peek() == Some(',') {
            self.advance();
        }

        let body = self.parse_pi_or_arrow()?;
        // Desugar to Exists ty (\name : ty . body)
        let lambda = ParsedExpr::Lambda(name.clone(), Box::new(ty.clone()), Box::new(body));
        Ok(ParsedExpr::App(
            Box::new(ParsedExpr::App(
                Box::new(ParsedExpr::Const("Exists".to_string())),
                Box::new(ty),
            )),
            Box::new(lambda),
        ))
    }

    /// Parse a pattern: constructor optionally applied to variable names.
    fn parse_pattern(&mut self) -> Result<ParsedExpr, String> {
        let ctor = self.parse_ident_raw()?;
        let mut result = ParsedExpr::Const(ctor);

        // Parse variables after constructor: ctor v1 v2 ...
        loop {
            self.skip_whitespace();
            if let Some(c) = self.peek() {
                if c.is_alphabetic() || c == '_' {
                    let var = self.parse_ident_raw()?;
                    result = ParsedExpr::App(Box::new(result), Box::new(ParsedExpr::Const(var)));
                    continue;
                }
            }
            break;
        }

        Ok(result)
    }

    fn parse_nat_lit(&mut self) -> Result<ParsedExpr, String> {
        let mut num = 0u64;
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                num = num * 10 + (c as u64 - '0' as u64);
                self.advance();
            } else {
                break;
            }
        }
        Ok(ParsedExpr::NatLit(num))
    }

    fn parse_ident_or_bvar(&mut self) -> Result<ParsedExpr, String> {
        let name = self.parse_ident_raw()?;
        if name.starts_with("x") {
            if let Ok(n) = name[1..].parse::<u64>() {
                return Ok(ParsedExpr::BVar(n));
            }
        }
        Ok(ParsedExpr::Const(name))
    }

    fn parse_ident_raw(&mut self) -> Result<String, String> {
        self.skip_whitespace();
        let mut name = String::new();

        // Special case for := and =>
        if self.peek() == Some(':') && self.input.get(self.pos + 1) == Some(&'=') {
            return Err("Unexpected ':='".to_string());
        }

        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' || c == '.' || c == '\'' {
                name.push(c);
                self.advance();
            } else {
                break;
            }
        }

        if name.is_empty() {
            Err(format!("Expected identifier, got {:?}", self.peek()))
        } else {
            Ok(name)
        }
    }

    fn starts_with_keyword(&self, kw: &str) -> bool {
        let saved = self.pos;
        let mut tmp = Parser { input: self.input.clone(), pos: saved };
        tmp.skip_whitespace();
        for expected in kw.chars() {
            if let Some(c) = tmp.peek() {
                if c != expected {
                    return false;
                }
                tmp.advance();
            } else {
                return false;
            }
        }
        // Make sure it's not a prefix of a longer identifier
        if let Some(c) = tmp.peek() {
            if c.is_alphanumeric() || c == '_' || c == '\'' {
                return false;
            }
        }
        true
    }

    fn advance_by(&mut self, n: usize) {
        self.pos += n;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(s: &str) -> ParsedExpr {
        let mut p = Parser::new(s);
        p.parse_expr().unwrap()
    }

    #[test]
    fn test_parse_const() {
        let e = parse("Nat");
        assert!(matches!(e, ParsedExpr::Const(name) if name == "Nat"));
    }

    #[test]
    fn test_parse_app() {
        let e = parse("succ zero");
        match e {
            ParsedExpr::App(f, a) => {
                assert!(matches!(f.as_ref(), ParsedExpr::Const(name) if name == "succ"));
                assert!(matches!(a.as_ref(), ParsedExpr::Const(name) if name == "zero"));
            }
            _ => panic!("Expected App"),
        }
    }

    #[test]
    fn test_parse_lambda() {
        let e = parse("\\x : Nat . x");
        match e {
            ParsedExpr::Lambda(name, ty, body) => {
                assert_eq!(name, "x");
                assert!(matches!(ty.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
                assert!(matches!(body.as_ref(), ParsedExpr::Const(name) if name == "x"));
            }
            _ => panic!("Expected Lambda"),
        }
    }

    #[test]
    fn test_parse_arrow() {
        let e = parse("Nat -> Nat");
        match e {
            ParsedExpr::Pi(name, ty, body) => {
                assert_eq!(name, "_");
                assert!(matches!(ty.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
                assert!(matches!(body.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
            }
            _ => panic!("Expected Pi"),
        }
    }

    #[test]
    fn test_parse_dependent_pi() {
        let e = parse("(x : Nat) -> Nat");
        match e {
            ParsedExpr::Pi(name, ty, body) => {
                assert_eq!(name, "x");
                assert!(matches!(ty.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
                assert!(matches!(body.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
            }
            _ => panic!("Expected Pi"),
        }
    }

    #[test]
    fn test_parse_let() {
        let e = parse("let x := zero in x");
        match e {
            ParsedExpr::Let(name, _, val, body) => {
                assert_eq!(name, "x");
                assert!(matches!(val.as_ref(), ParsedExpr::Const(name) if name == "zero"));
                assert!(matches!(body.as_ref(), ParsedExpr::Const(name) if name == "x"));
            }
            _ => panic!("Expected Let"),
        }
    }

    #[test]
    fn test_parse_nat_lit() {
        let e = parse("42");
        assert!(matches!(e, ParsedExpr::NatLit(42)));
    }

    #[test]
    fn test_parse_sort() {
        let e = parse("Type");
        assert!(matches!(e, ParsedExpr::Sort(1)));
        let e = parse("Prop");
        assert!(matches!(e, ParsedExpr::Sort(0)));
    }

    #[test]
    fn test_parse_match_nat() {
        let e = parse("match succ zero : Nat with | zero => zero | succ n => n");
        assert!(matches!(e, ParsedExpr::Match(_, _, branches) if branches.len() == 2));
    }

    #[test]
    fn test_parse_simple_def() {
        let src = "def not (b : Bool) : Bool := true\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 1);
        assert!(matches!(&decls[0], ParsedDecl::Def { name, .. } if name == "not"));
    }

    #[test]
    fn test_parse_match_expr() {
        let src = "match b : Bool with\n| true => false\n| false => true";
        let mut p = Parser::new(src);
        let expr = p.parse_expr().unwrap();
        assert!(matches!(expr, ParsedExpr::Match(..)));
    }

    #[test]
    fn test_parse_def_with_match() {
        let src = "def not (b : Bool) : Bool :=\n  match b : Bool with\n  | true => false\n  | false => true\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 1);
        assert!(matches!(&decls[0], ParsedDecl::Def { name, .. } if name == "not"));
    }

    #[test]
    fn test_parse_inductive_only() {
        let src = "inductive Bool where\n| true : Bool\n| false : Bool\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 1);
        assert!(matches!(&decls[0], ParsedDecl::Inductive { .. }));
    }

    #[test]
    fn test_parse_inductive_then_simple_def() {
        let src = "inductive Bool where\n| true : Bool\n| false : Bool\n\ndef not (b : Bool) : Bool := true\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 2);
        assert!(matches!(&decls[0], ParsedDecl::Inductive { .. }));
        assert!(matches!(&decls[1], ParsedDecl::Def { .. }));
    }

    #[test]
    fn test_parse_alias_def() {
        let src = "def add := nat_add\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 1);
        assert!(matches!(&decls[0], ParsedDecl::Def { name, .. } if name == "add"));
    }

    #[test]
    fn test_parse_nat_sub_and_alias() {
        let src = "def nat_sub (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat -> Nat)\n    (fun n => zero)\n    (\\m' : Nat . \\ih : Nat -> Nat . fun n : Nat =>\n      rec.Nat (fun _ => Nat)\n        (succ m')\n        (fun n' : Nat => fun _ : Nat => ih n')\n        n)\n    m\n    n\n\ndef add := nat_add\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 2);
    }

    #[test]
    fn test_parse_full_nat_lean_inline() {
        let src = "def nat_add (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat) n (\\m' : Nat . \\ih : Nat . succ ih) m\n\ndef nat_sub (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat -> Nat)\n    (fun n => zero)\n    (\\m' : Nat . \\ih : Nat -> Nat . fun n : Nat =>\n      rec.Nat (fun _ => Nat)\n        (succ m')\n        (fun n' : Nat => fun _ : Nat => ih n')\n        n)\n    m\n    n\n\ndef nat_mul (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat) zero (\\m' : Nat . \\ih : Nat . nat_add ih n) m\n\n-- Aliases for infix operators\ndef add := nat_add\ndef sub := nat_sub\ndef mul := nat_mul\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 6);
    }

    #[test]
    fn test_parse_defs_with_comment_and_aliases() {
        let src = "def nat_mul (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat) zero (\\m' : Nat . \\ih : Nat . nat_add ih n) m\n\n-- Aliases for infix operators\ndef add := nat_add\ndef sub := nat_sub\ndef mul := nat_mul\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 4);
    }

    #[test]
    fn test_parse_three_defs_no_aliases() {
        let src = "def nat_add (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat) n (\\m' : Nat . \\ih : Nat . succ ih) m\n\ndef nat_sub (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat -> Nat)\n    (fun n => zero)\n    (\\m' : Nat . \\ih : Nat -> Nat . fun n : Nat =>\n      rec.Nat (fun _ => Nat)\n        (succ m')\n        (fun n' : Nat => fun _ : Nat => ih n')\n        n)\n    m\n    n\n\ndef nat_mul (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat) zero (\\m' : Nat . \\ih : Nat . nat_add ih n) m\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 3);
    }

    #[test]
    fn test_parse_nat_lean_file() {
        let path = std::path::Path::new("Nat.lean");
        let src = std::fs::read_to_string(path).unwrap();
        let mut p = Parser::new(&src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 6);
    }

    #[test]
    fn test_parse_nat_sub_only() {
        let src = "def nat_sub (m : Nat) (n : Nat) : Nat :=\n  rec.Nat (fun _ => Nat -> Nat)\n    (fun n => zero)\n    (\\m' : Nat . \\ih : Nat -> Nat . fun n : Nat =>\n      rec.Nat (fun _ => Nat)\n        (succ m')\n        (fun n' : Nat => fun _ : Nat => ih n')\n        n)\n    m\n    n\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn test_parse_fun_with_arrow_type() {
        // fun _ => Nat -> Nat should parse correctly
        let e = parse("fun _ => Nat -> Nat");
        match e {
            ParsedExpr::Lambda(name, ty, body) => {
                assert_eq!(name, "_");
                // body should be Nat -> Nat = Pi(_, Nat, Nat)
                match body.as_ref() {
                    ParsedExpr::Pi(_, _, _) => {}
                    _ => panic!("Expected Pi in body, got {:?}", body),
                }
            }
            _ => panic!("Expected Lambda, got {:?}", e),
        }
    }

    #[test]
    fn test_parse_file_declarations() {
        let src = "inductive Bool where\n| true : Bool\n| false : Bool\n\ndef not (b : Bool) : Bool :=\n  match b : Bool with\n  | true => false\n  | false => true\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 2);
        assert!(matches!(&decls[0], ParsedDecl::Inductive { .. }));
        assert!(matches!(&decls[1], ParsedDecl::Def { .. }));
    }

    #[test]
    fn test_parse_infix_add() {
        let e = parse("2 + 3");
        // Should desugar to add 2 3 = App(App(Const("add"), NatLit(2)), NatLit(3))
        match e {
            ParsedExpr::App(f, rhs) => {
                match f.as_ref() {
                    ParsedExpr::App(op, lhs) => {
                        assert!(matches!(op.as_ref(), ParsedExpr::Const(name) if name == "add"));
                        assert!(matches!(lhs.as_ref(), ParsedExpr::NatLit(2)));
                        assert!(matches!(rhs.as_ref(), ParsedExpr::NatLit(3)));
                    }
                    _ => panic!("Expected App(App(add, 2), 3)"),
                }
            }
            _ => panic!("Expected App"),
        }
    }

    #[test]
    fn test_parse_infix_precedence() {
        let e = parse("2 + 3 * 4");
        // Should be add 2 (mul 3 4)
        match e {
            ParsedExpr::App(f, rhs) => {
                match f.as_ref() {
                    ParsedExpr::App(op, lhs) => {
                        assert!(matches!(op.as_ref(), ParsedExpr::Const(name) if name == "add"));
                        assert!(matches!(lhs.as_ref(), ParsedExpr::NatLit(2)));
                        // rhs should be mul 3 4
                        match rhs.as_ref() {
                            ParsedExpr::App(f2, rhs2) => {
                                match f2.as_ref() {
                                    ParsedExpr::App(op2, lhs2) => {
                                        assert!(matches!(op2.as_ref(), ParsedExpr::Const(name) if name == "mul"));
                                        assert!(matches!(lhs2.as_ref(), ParsedExpr::NatLit(3)));
                                        assert!(matches!(rhs2.as_ref(), ParsedExpr::NatLit(4)));
                                    }
                                    _ => panic!("Expected mul"),
                                }
                            }
                            _ => panic!("Expected App for mul"),
                        }
                    }
                    _ => panic!("Expected App(App(add, 2), ...)"),
                }
            }
            _ => panic!("Expected App"),
        }
    }

    #[test]
    fn test_parse_forall() {
        let e = parse("forall (n : Nat), Nat");
        match e {
            ParsedExpr::Pi(name, ty, body) => {
                assert_eq!(name, "n");
                assert!(matches!(ty.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
                assert!(matches!(body.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
            }
            _ => panic!("Expected Pi, got {:?}", e),
        }
    }

    #[test]
    fn test_parse_forall_arrow() {
        let e = parse("forall (n : Nat) -> Nat");
        match e {
            ParsedExpr::Pi(name, ty, body) => {
                assert_eq!(name, "n");
                assert!(matches!(ty.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
                assert!(matches!(body.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
            }
            _ => panic!("Expected Pi, got {:?}", e),
        }
    }
}
