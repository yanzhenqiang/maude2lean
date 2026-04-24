use super::environment::Environment;
use super::expr::*;
use std::collections::HashMap;
use std::rc::Rc;

/// Parser for TTobs core surface syntax.
///
/// Supported syntax:
///   - Constants/variables: Nat, zero, succ, x
///   - Application: f a b (left-associative)
///   - Lambda: \x : Nat . x   or   fun x => x
///   - Pi: Nat -> Nat   or   (x : Nat) -> Nat
///   - Universe: U, U1, U2, ...  and  Omega, Omega1, Omega2, ...
///   - Observational equality: t ==_A u  or  eq(A, t, u)
///   - Cast: cast(A, B, e, t)
///   - Parens: (e)

#[derive(Debug, Clone)]
pub enum ParsedExpr {
    BVar(u64),
    Const(String),
    App(Box<ParsedExpr>, Box<ParsedExpr>),
    Lambda(String, Box<ParsedExpr>, Box<ParsedExpr>),
    Pi(String, Box<ParsedExpr>, Box<ParsedExpr>),
    U(u64),
    Omega(u64),
    Eq(Box<ParsedExpr>, Box<ParsedExpr>, Box<ParsedExpr>),
    Cast(Box<ParsedExpr>, Box<ParsedExpr>, Box<ParsedExpr>, Box<ParsedExpr>),
    /// let x : T := v in e  (syntactic sugar for (λx:T. e) v)
    Let(String, Box<ParsedExpr>, Box<ParsedExpr>, Box<ParsedExpr>),
    /// have h : P := p in e  (syntactic sugar for (λh:P. e) p)
    Have(String, Box<ParsedExpr>, Box<ParsedExpr>, Box<ParsedExpr>),
}

impl ParsedExpr {
    pub fn to_expr(&self, env_bindings: &HashMap<String, Expr>, _env: &Environment, bound_vars: &mut Vec<String>) -> Expr {
        match self {
            ParsedExpr::BVar(n) => Expr::mk_bvar(*n),
            ParsedExpr::Const(name) => {
                for (i, bv) in bound_vars.iter().enumerate().rev() {
                    if bv == name {
                        return Expr::mk_bvar((bound_vars.len() - 1 - i) as u64);
                    }
                }
                if let Some(e) = env_bindings.get(name) {
                    return e.clone();
                }
                let name_parts: Vec<&str> = name.split('.').collect();
                let mut lean_name = Name::new(name_parts[0]);
                for part in &name_parts[1..] {
                    lean_name = lean_name.extend(part);
                }
                Expr::mk_const(lean_name, vec![])
            }
            ParsedExpr::App(f, a) => {
                let f_expr = f.to_expr(env_bindings, _env, bound_vars);
                let a_expr = a.to_expr(env_bindings, _env, bound_vars);
                Expr::mk_app(f_expr, a_expr)
            }
            ParsedExpr::Lambda(name, ty, body) => {
                let ty_expr = ty.to_expr(env_bindings, _env, bound_vars);
                bound_vars.push(name.clone());
                let body_expr = body.to_expr(env_bindings, _env, bound_vars);
                bound_vars.pop();
                Expr::Lambda(Name::new(name), BinderInfo::Default, Rc::new(ty_expr), Rc::new(body_expr))
            }
            ParsedExpr::Pi(name, ty, body) => {
                let ty_expr = ty.to_expr(env_bindings, _env, bound_vars);
                bound_vars.push(name.clone());
                let body_expr = body.to_expr(env_bindings, _env, bound_vars);
                bound_vars.pop();
                Expr::Pi(Name::new(name), BinderInfo::Default, Rc::new(ty_expr), Rc::new(body_expr))
            }
            ParsedExpr::U(n) => Expr::U(Level::from_explicit(*n)),
            ParsedExpr::Omega(n) => Expr::Omega(Level::from_explicit(*n)),
            ParsedExpr::Eq(a, t, u) => {
                let a_expr = a.to_expr(env_bindings, _env, bound_vars);
                let t_expr = t.to_expr(env_bindings, _env, bound_vars);
                let u_expr = u.to_expr(env_bindings, _env, bound_vars);
                Expr::mk_eq(a_expr, t_expr, u_expr)
            }
            ParsedExpr::Cast(a, b, e, t) => {
                let a_expr = a.to_expr(env_bindings, _env, bound_vars);
                let b_expr = b.to_expr(env_bindings, _env, bound_vars);
                let e_expr = e.to_expr(env_bindings, _env, bound_vars);
                let t_expr = t.to_expr(env_bindings, _env, bound_vars);
                Expr::mk_cast(a_expr, b_expr, e_expr, t_expr)
            }
            ParsedExpr::Let(name, ty, value, body) => {
                let ty_expr = ty.to_expr(env_bindings, _env, bound_vars);
                let value_expr = value.to_expr(env_bindings, _env, bound_vars);
                bound_vars.push(name.clone());
                let body_expr = body.to_expr(env_bindings, _env, bound_vars);
                bound_vars.pop();
                let lam = Expr::Lambda(Name::new(name), BinderInfo::Default, Rc::new(ty_expr), Rc::new(body_expr));
                Expr::mk_app(lam, value_expr)
            }
            ParsedExpr::Have(name, ty, proof, body) => {
                let ty_expr = ty.to_expr(env_bindings, _env, bound_vars);
                let proof_expr = proof.to_expr(env_bindings, _env, bound_vars);
                bound_vars.push(name.clone());
                let body_expr = body.to_expr(env_bindings, _env, bound_vars);
                bound_vars.pop();
                let lam = Expr::Lambda(Name::new(name), BinderInfo::Default, Rc::new(ty_expr), Rc::new(body_expr));
                Expr::mk_app(lam, proof_expr)
            }
        }
    }
}

impl Level {
    fn from_explicit(n: u64) -> Level {
        let mut result = Level::Zero;
        for _ in 0..n {
            result = Level::mk_succ(result);
        }
        result
    }
}

#[derive(Debug, Clone)]
pub enum ParsedDecl {
    Def {
        name: String,
        params: Vec<(String, ParsedExpr)>,
        ret_ty: Option<ParsedExpr>,
        value: ParsedExpr,
    },
    Theorem {
        name: String,
        params: Vec<(String, ParsedExpr)>,
        ret_ty: ParsedExpr,
        value: ParsedExpr,
    },
    Axiom {
        name: String,
        ty: ParsedExpr,
    },
    Inductive {
        name: String,
        ctors: Vec<(String, ParsedExpr)>,
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

    pub fn parse_expr(&mut self) -> Result<ParsedExpr, String> {
        self.parse_pi_or_arrow()
    }

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
            if self.peek() == Some('-') && self.input.get(self.pos + 1) == Some(&'-') {
                while let Some(c) = self.peek() {
                    self.advance();
                    if c == '\n' { break; }
                }
                continue;
            }
            if self.peek() == Some('/') && self.input.get(self.pos + 1) == Some(&'-') {
                self.advance(); self.advance();
                let mut depth = 1;
                while depth > 0 {
                    if let Some(c) = self.peek() {
                        if c == '/' && self.input.get(self.pos + 1) == Some(&'-') {
                            self.advance(); self.advance(); depth += 1;
                        } else if c == '-' && self.input.get(self.pos + 1) == Some(&'/') {
                            self.advance(); self.advance(); depth -= 1;
                        } else {
                            self.advance();
                        }
                    } else { break; }
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
        self.advance_by(3);
        self.skip_whitespace();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();
        let (params, ret_ty, value) = self.parse_decl_body()?;
        Ok(ParsedDecl::Def { name, params, ret_ty, value })
    }

    fn parse_theorem_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(7);
        self.skip_whitespace();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();
        let (params, ret_ty, value) = self.parse_decl_body()?;
        let ret_ty = ret_ty.ok_or("Theorem must have an explicit return type".to_string())?;
        Ok(ParsedDecl::Theorem { name, params, ret_ty, value })
    }

    fn parse_inductive_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(9); // "inductive"
        self.skip_whitespace();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();
        // Optional type annotation: e.g., ": Omega" or ": U"
        if self.peek() == Some(':') {
            self.advance(); // skip ':'
            let _ty = self.parse_pi_or_arrow()?;
            self.skip_whitespace();
        }
        if self.starts_with_keyword("where") {
            self.advance_by(5);
        }
        self.skip_whitespace();

        let mut ctors = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek() != Some('|') {
                break;
            }
            self.advance(); // skip '|'
            self.skip_whitespace();
            let ctor_name = self.parse_ident_raw()?;
            self.skip_whitespace();
            if self.peek() != Some(':') {
                return Err(format!("Expected ':' after constructor name '{}'", ctor_name));
            }
            self.advance();
            let ctor_ty = self.parse_pi_or_arrow()?;
            ctors.push((ctor_name, ctor_ty));
        }

        Ok(ParsedDecl::Inductive { name, ctors })
    }

    fn parse_axiom_decl(&mut self) -> Result<ParsedDecl, String> {
        self.advance_by(5);
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

    fn parse_decl_body(&mut self) -> Result<(Vec<(String, ParsedExpr)>, Option<ParsedExpr>, ParsedExpr), String> {
        let mut params = Vec::new();
        while self.peek() == Some('(') || self.peek() == Some('{') {
            let implicit = self.peek() == Some('{');
            self.advance();
            let mut names = vec![self.parse_ident_raw()?];
            self.skip_whitespace();
            while self.peek() != Some(':') {
                names.push(self.parse_ident_raw()?);
                self.skip_whitespace();
            }
            self.advance();
            let pty = self.parse_pi_or_arrow()?;
            self.skip_whitespace();
            let close = if implicit { '}' } else { ')' };
            if self.peek() != Some(close) {
                return Err(format!("Expected '{}'", close));
            }
            self.advance();
            for name in names {
                params.push((name, pty.clone()));
            }
            self.skip_whitespace();
        }

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

    fn peek(&self) -> Option<char> {
        self.input.get(self.pos).copied()
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() { self.advance(); } else { break; }
        }
    }

    fn consume(&mut self, expected: char) -> Result<(), String> {
        self.skip_whitespace();
        if let Some(c) = self.peek() {
            if c == expected { self.advance(); return Ok(()); }
        }
        Err(format!("Expected '{}'", expected))
    }

    fn parse_pi_or_arrow(&mut self) -> Result<ParsedExpr, String> {
        self.skip_whitespace();
        if self.peek() == Some('(') {
            let saved_pos = self.pos;
            self.advance();
            self.skip_whitespace();
            if let Ok(name) = self.parse_ident_raw() {
                self.skip_whitespace();
                if self.peek() == Some(':') {
                    self.advance();
                    let ty = self.parse_pi_or_arrow()?;
                    self.consume(')')?;
                    self.skip_whitespace();
                    if self.peek() == Some('-') && self.input.get(self.pos + 1) == Some(&'>') {
                        self.advance(); self.advance();
                        let body = self.parse_pi_or_arrow()?;
                        return Ok(ParsedExpr::Pi(name, Box::new(ty), Box::new(body)));
                    } else if self.peek() == Some(',') {
                        self.advance();
                        let body = self.parse_pi_or_arrow()?;
                        return Ok(ParsedExpr::Pi(name, Box::new(ty), Box::new(body)));
                    }
                }
            }
            self.pos = saved_pos;
        }
        let left = self.parse_infix(0)?;
        self.skip_whitespace();
        if self.peek() == Some('-') && self.input.get(self.pos + 1) == Some(&'>') {
            self.advance(); self.advance();
            let right = self.parse_pi_or_arrow()?;
            return Ok(ParsedExpr::Pi("_".to_string(), Box::new(left), Box::new(right)));
        }
        Ok(left)
    }

    fn parse_infix(&mut self, min_prec: i32) -> Result<ParsedExpr, String> {
        let mut left = self.parse_app_or_atom()?;
        loop {
            self.skip_whitespace_and_comments();
            let (op, prec) = if self.peek() == Some('+') {
                ("+", 6)
            } else if self.peek() == Some('-') {
                if self.input.get(self.pos + 1) == Some(&'>') { break; }
                ("-", 6)
            } else if self.peek() == Some('*') {
                ("*", 7)
            } else {
                break;
            };
            if prec < min_prec { break; }
            self.advance();
            let right = self.parse_infix(prec + 1)?;
            let op_name = match op { "+" => "add", "-" => "sub", "*" => "mul", _ => op };
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
            if self.starts_with_keyword("def") || self.starts_with_keyword("axiom")
                || self.starts_with_keyword("theorem") || self.starts_with_keyword("inductive")
                || self.starts_with_keyword("where") || self.starts_with_keyword("end")
                || self.starts_with_keyword("in") || self.starts_with_keyword("let")
                || self.starts_with_keyword("have") {
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
                } else if self.starts_with_keyword("forall") {
                    self.parse_forall()
                } else if self.starts_with_keyword("eq") {
                    self.parse_eq()
                } else if self.starts_with_keyword("cast") {
                    self.parse_cast()
                } else if self.starts_with_keyword("let") {
                    self.parse_let()
                } else if self.starts_with_keyword("have") {
                    self.parse_have()
                } else if self.starts_with_universe() {
                    self.parse_universe()
                } else if self.starts_with_omega() {
                    self.parse_omega()
                } else {
                    self.parse_ident_or_bvar()
                }
            }
        }
    }

    fn parse_lambda(&mut self) -> Result<ParsedExpr, String> {
        self.advance();
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
        self.advance_by(3);
        self.skip_whitespace();
        let mut params = vec![self.parse_ident_raw()?];
        self.skip_whitespace();
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
        for param in params.into_iter().skip(1).rev() {
            body = ParsedExpr::Lambda(param, Box::new(ParsedExpr::Const("?".to_string())), Box::new(body));
        }
        Ok(ParsedExpr::Lambda(first_param, Box::new(ty), Box::new(body)))
    }

    fn parse_forall(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(7);
        self.skip_whitespace();
        if self.peek() != Some('(') && self.peek() != Some('{') {
            return Err("Expected '(' or '{' after forall".to_string());
        }
        let mut binders = Vec::new();
        while self.peek() == Some('(') || self.peek() == Some('{') {
            let implicit = self.peek() == Some('{');
            self.advance();
            let mut names = vec![self.parse_ident_raw()?];
            self.skip_whitespace();
            while self.peek() != Some(':') {
                names.push(self.parse_ident_raw()?);
                self.skip_whitespace();
            }
            self.advance();
            let ty = self.parse_pi_or_arrow()?;
            let close = if implicit { '}' } else { ')' };
            if self.peek() != Some(close) {
                return Err(format!("Expected '{}'", close));
            }
            self.advance();
            for name in names {
                binders.push((name, ty.clone()));
            }
            self.skip_whitespace();
        }
        if self.peek() == Some(',') { self.advance(); }
        else if self.peek() == Some('-') && self.input.get(self.pos + 1) == Some(&'>') {
            self.advance(); self.advance();
        }
        let body = self.parse_pi_or_arrow()?;
        let mut result = body;
        for (name, ty) in binders.into_iter().rev() {
            result = ParsedExpr::Pi(name, Box::new(ty), Box::new(result));
        }
        Ok(result)
    }

    fn parse_eq(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(2); // "eq"
        self.skip_whitespace();
        if self.peek() != Some('(') {
            return Err("Expected '(' after eq".to_string());
        }
        self.advance();
        let a = self.parse_expr()?;
        self.skip_whitespace();
        if self.peek() != Some(',') {
            return Err("Expected ',' in eq".to_string());
        }
        self.advance();
        let t = self.parse_expr()?;
        self.skip_whitespace();
        if self.peek() != Some(',') {
            return Err("Expected ',' in eq".to_string());
        }
        self.advance();
        let u = self.parse_expr()?;
        self.skip_whitespace();
        self.consume(')')?;
        Ok(ParsedExpr::Eq(Box::new(a), Box::new(t), Box::new(u)))
    }

    fn parse_cast(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(4); // "cast"
        self.skip_whitespace();
        if self.peek() != Some('(') {
            return Err("Expected '(' after cast".to_string());
        }
        self.advance();
        let a = self.parse_expr()?;
        self.skip_whitespace();
        if self.peek() != Some(',') {
            return Err("Expected ',' in cast".to_string());
        }
        self.advance();
        let b = self.parse_expr()?;
        self.skip_whitespace();
        if self.peek() != Some(',') {
            return Err("Expected ',' in cast".to_string());
        }
        self.advance();
        let e = self.parse_expr()?;
        self.skip_whitespace();
        if self.peek() != Some(',') {
            return Err("Expected ',' in cast".to_string());
        }
        self.advance();
        let t = self.parse_expr()?;
        self.skip_whitespace();
        self.consume(')')?;
        Ok(ParsedExpr::Cast(Box::new(a), Box::new(b), Box::new(e), Box::new(t)))
    }

    fn parse_let(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(3); // "let"
        self.skip_whitespace();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();
        if self.peek() != Some(':') {
            return Err("Expected ':' in let binding".to_string());
        }
        self.advance();
        let ty = self.parse_expr()?;
        self.skip_whitespace();
        if !self.starts_with_keyword(":=") {
            return Err("Expected ':=' in let binding".to_string());
        }
        self.advance_by(2);
        let value = self.parse_expr()?;
        self.skip_whitespace();
        if !self.starts_with_keyword("in") {
            return Err("Expected 'in' after let binding".to_string());
        }
        self.advance_by(2);
        let body = self.parse_expr()?;
        Ok(ParsedExpr::Let(name, Box::new(ty), Box::new(value), Box::new(body)))
    }

    fn parse_have(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(4); // "have"
        self.skip_whitespace();
        let name = self.parse_ident_raw()?;
        self.skip_whitespace();
        if self.peek() != Some(':') {
            return Err("Expected ':' in have binding".to_string());
        }
        self.advance();
        let ty = self.parse_expr()?;
        self.skip_whitespace();
        if !self.starts_with_keyword(":=") {
            return Err("Expected ':=' in have binding".to_string());
        }
        self.advance_by(2);
        let proof = self.parse_expr()?;
        self.skip_whitespace();
        if !self.starts_with_keyword("in") {
            return Err("Expected 'in' after have binding".to_string());
        }
        self.advance_by(2);
        let body = self.parse_expr()?;
        Ok(ParsedExpr::Have(name, Box::new(ty), Box::new(proof), Box::new(body)))
    }

    fn parse_universe(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(1); // "U"
        let mut num = 0u64;
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                num = num * 10 + (c as u64 - '0' as u64);
                self.advance();
            } else { break; }
        }
        Ok(ParsedExpr::U(num))
    }

    fn parse_omega(&mut self) -> Result<ParsedExpr, String> {
        self.advance_by(5); // "Omega"
        let mut num = 0u64;
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                num = num * 10 + (c as u64 - '0' as u64);
                self.advance();
            } else { break; }
        }
        Ok(ParsedExpr::Omega(num))
    }

    fn parse_nat_lit(&mut self) -> Result<ParsedExpr, String> {
        let mut num = 0u64;
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                num = num * 10 + (c as u64 - '0' as u64);
                self.advance();
            } else { break; }
        }
        // Desugar nat literals to zero / succ applications
        if num == 0 {
            Ok(ParsedExpr::Const("zero".to_string()))
        } else {
            let mut expr = ParsedExpr::Const("zero".to_string());
            for _ in 0..num {
                expr = ParsedExpr::App(
                    Box::new(ParsedExpr::Const("succ".to_string())),
                    Box::new(expr),
                );
            }
            Ok(expr)
        }
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
        if self.peek() == Some(':') && self.input.get(self.pos + 1) == Some(&'=') {
            return Err("Unexpected ':='".to_string());
        }
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' || c == '.' || c == '\'' {
                name.push(c);
                self.advance();
            } else { break; }
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
                if c != expected { return false; }
                tmp.advance();
            } else { return false; }
        }
        if let Some(c) = tmp.peek() {
            if c.is_alphanumeric() || c == '_' || c == '\'' { return false; }
        }
        true
    }

    fn starts_with_universe(&self) -> bool {
        let saved = self.pos;
        let mut tmp = Parser { input: self.input.clone(), pos: saved };
        tmp.skip_whitespace();
        tmp.peek() == Some('U')
    }

    fn starts_with_omega(&self) -> bool {
        let saved = self.pos;
        let mut tmp = Parser { input: self.input.clone(), pos: saved };
        tmp.skip_whitespace();
        for expected in "Omega".chars() {
            if let Some(c) = tmp.peek() {
                if c != expected { return false; }
                tmp.advance();
            } else { return false; }
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
    fn test_parse_universe() {
        let e = parse("U");
        assert!(matches!(e, ParsedExpr::U(0)));
        let e = parse("U1");
        assert!(matches!(e, ParsedExpr::U(1)));
    }

    #[test]
    fn test_parse_omega() {
        let e = parse("Omega");
        assert!(matches!(e, ParsedExpr::Omega(0)));
        let e = parse("Omega2");
        assert!(matches!(e, ParsedExpr::Omega(2)));
    }

    #[test]
    fn test_parse_eq() {
        let e = parse("eq(Nat, zero, zero)");
        match e {
            ParsedExpr::Eq(a, t, u) => {
                assert!(matches!(a.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
                assert!(matches!(t.as_ref(), ParsedExpr::Const(name) if name == "zero"));
                assert!(matches!(u.as_ref(), ParsedExpr::Const(name) if name == "zero"));
            }
            _ => panic!("Expected Eq"),
        }
    }

    #[test]
    fn test_parse_cast() {
        let e = parse("cast(Nat, Nat, e, zero)");
        match e {
            ParsedExpr::Cast(a, b, e, t) => {
                assert!(matches!(a.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
                assert!(matches!(b.as_ref(), ParsedExpr::Const(name) if name == "Nat"));
                assert!(matches!(e.as_ref(), ParsedExpr::Const(name) if name == "e"));
                assert!(matches!(t.as_ref(), ParsedExpr::Const(name) if name == "zero"));
            }
            _ => panic!("Expected Cast"),
        }
    }

    #[test]
    fn test_parse_let() {
        let e = parse("let x : Nat := zero in x");
        match e {
            ParsedExpr::Let(name, ty, value, body) => {
                assert_eq!(name, "x");
                assert!(matches!(ty.as_ref(), ParsedExpr::Const(n) if n == "Nat"));
                assert!(matches!(value.as_ref(), ParsedExpr::Const(n) if n == "zero"));
                assert!(matches!(body.as_ref(), ParsedExpr::Const(n) if n == "x"));
            }
            _ => panic!("Expected Let, got {:?}", e),
        }
    }

    #[test]
    fn test_parse_have() {
        let e = parse("have h : Nat := zero in h");
        match e {
            ParsedExpr::Have(name, ty, proof, body) => {
                assert_eq!(name, "h");
                assert!(matches!(ty.as_ref(), ParsedExpr::Const(n) if n == "Nat"));
                assert!(matches!(proof.as_ref(), ParsedExpr::Const(n) if n == "zero"));
                assert!(matches!(body.as_ref(), ParsedExpr::Const(n) if n == "h"));
            }
            _ => panic!("Expected Have, got {:?}", e),
        }
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
    fn test_parse_theorem() {
        let src = "theorem id_nat (x : Nat) : Nat := x\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 1);
        assert!(matches!(&decls[0], ParsedDecl::Theorem { name, .. } if name == "id_nat"));
    }

    #[test]
    fn test_parse_axiom() {
        let src = "axiom Nat : U\n";
        let mut p = Parser::new(src);
        let decls = p.parse_file().unwrap();
        assert_eq!(decls.len(), 1);
        assert!(matches!(&decls[0], ParsedDecl::Axiom { name, .. } if name == "Nat"));
    }
}
