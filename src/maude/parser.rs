use std::collections::HashMap;

use super::ast::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    // Keywords
    Fmod, Endfm, Mod, Endm,
    Sort, Sorts, Subsort,
    Op, Ops, Var, Vars,
    Eq, Ceq, Rl, Crl,
    Mb, Cmb,
    If,
    Protecting, Extending, Including, Using,
    Inc,                      // abbreviation for including
    // Commands (not part of module syntax, but used in scripts)
    Select, Red, Rew, Search, Load,
    Set, In, To,
    // Punctuation
    Dot,                      // .
    Comma,                    // ,
    Colon,                    // :
    Semi,                     // ;
    LParen, RParen,           // ( )
    LBracket, RBracket,       // [ ]
    LBrace, RBrace,           // { }
    Arrow,                    // ->
    DArrow,                   // =>
    EqSign,                   // =
    Lt,                       // <
    // Special
    Underscore,               // _
    Hat,                      // ^
    Apostrophe,               // '
    Minus,                    // -
    // Literals
    Ident(String),            // identifier or operator name
    StringLit(String),        // "..."
    NatLit(u64),              // 123
    // End of input
    Eof,
}

pub struct Lexer<'a> {
    input: &'a str,
    pos: usize,
    keywords: HashMap<String, Token>,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        let mut keywords = HashMap::new();
        let kw = [
            ("fmod", Token::Fmod), ("endfm", Token::Endfm),
            ("mod", Token::Mod), ("endm", Token::Endm),
            ("sort", Token::Sort), ("sorts", Token::Sorts),
            ("subsort", Token::Subsort),
            ("op", Token::Op), ("ops", Token::Ops),
            ("var", Token::Var), ("vars", Token::Vars),
            ("eq", Token::Eq), ("ceq", Token::Ceq),
            ("rl", Token::Rl), ("crl", Token::Crl),
            ("if", Token::If),
            ("protecting", Token::Protecting),
            ("extending", Token::Extending),
            ("including", Token::Including),
            ("using", Token::Using),
            ("inc", Token::Inc),
            ("select", Token::Select),
            ("red", Token::Red), ("rew", Token::Rew),
            ("search", Token::Search),
            ("load", Token::Load),
            ("set", Token::Set), ("in", Token::In), ("to", Token::To),
        ];
        for (s, t) in kw {
            keywords.insert(s.to_string(), t);
        }
        Lexer { input, pos: 0, keywords }
    }

    fn peek(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    fn advance(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.pos += ch.len_utf8();
        Some(ch)
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            // whitespace
            while let Some(c) = self.peek() {
                if c.is_whitespace() { self.advance(); }
                else { break; }
            }
            // single-line comment: ---... or ***...
            if let Some(c) = self.peek() {
                if c == '-' || c == '*' {
                    let start = self.pos;
                    let ch = self.advance().unwrap();
                    if self.peek() == Some(ch) && self.input[self.pos+1..].starts_with(ch) {
                        // it's a comment
                        self.advance(); self.advance();
                        while let Some(c) = self.peek() {
                            if c == '\n' { break; }
                            self.advance();
                        }
                        continue;
                    } else {
                        self.pos = start; // rollback
                    }
                }
            }
            break;
        }
    }

    pub fn next_token(&mut self) -> Result<Token, String> {
        self.skip_whitespace_and_comments();
        let start = self.pos;
        let c = match self.peek() {
            Some(c) => c,
            None => return Ok(Token::Eof),
        };

        // String literal
        if c == '"' {
            self.advance(); // skip "
            let mut s = String::new();
            while let Some(ch) = self.peek() {
                if ch == '"' { self.advance(); break; }
                if ch == '\\' {
                    self.advance();
                    if let Some(esc) = self.advance() {
                        s.push(match esc {
                            'n' => '\n', 't' => '\t', 'r' => '\r', '\\' => '\\', '"' => '"',
                            _ => esc,
                        });
                    }
                } else {
                    s.push(ch);
                    self.advance();
                }
            }
            return Ok(Token::StringLit(s));
        }

        // Number literal
        if c.is_ascii_digit() {
            let mut n = 0u64;
            while let Some(ch) = self.peek() {
                if ch.is_ascii_digit() {
                    self.advance();
                    n = n.wrapping_mul(10).wrapping_add(ch.to_digit(10).unwrap() as u64);
                } else { break; }
            }
            return Ok(Token::NatLit(n));
        }

        // Multi-char operators and punctuation
        match c {
            '(' => { self.advance(); return Ok(Token::LParen); }
            ')' => { self.advance(); return Ok(Token::RParen); }
            '[' => { self.advance(); return Ok(Token::LBracket); }
            ']' => { self.advance(); return Ok(Token::RBracket); }
            '{' => { self.advance(); return Ok(Token::LBrace); }
            '}' => { self.advance(); return Ok(Token::RBrace); }
            ',' => { self.advance(); return Ok(Token::Comma); }
            ';' => { self.advance(); return Ok(Token::Semi); }
            ':' => { self.advance(); return Ok(Token::Colon); }
            '<' => { self.advance(); return Ok(Token::Lt); }
            '^' => { self.advance(); return Ok(Token::Hat); }
            '\'' => { self.advance(); return Ok(Token::Apostrophe); }
            '.' => { self.advance(); return Ok(Token::Dot); }
            '=' => {
                self.advance();
                if self.peek() == Some('>') { self.advance(); return Ok(Token::DArrow); }
                return Ok(Token::EqSign);
            }
            '-' => {
                self.advance();
                if self.peek() == Some('>') { self.advance(); return Ok(Token::Arrow); }
                // could be negative number or part of identifier
                self.pos = start;
            }
            _ => {}
        }

        // Identifier (including operator symbols like _+_, if_then_else_fi)
        if c.is_alphabetic() || c == '_' || c == '\'' || c == '?' {
            let mut s = String::new();
            while let Some(ch) = self.peek() {
                if ch.is_alphanumeric() || ch == '_' || ch == '\'' || ch == '?' {
                    s.push(ch);
                    self.advance();
                } else { break; }
            }
            let lower = s.to_lowercase();
            if let Some(t) = self.keywords.get(&lower) {
                return Ok(t.clone());
            }
            return Ok(Token::Ident(s));
        }

        // Operator symbols (mixfix operators like _+_, if_then_else_fi, etc.)
        if is_op_symbol(c) {
            let mut s = String::new();
            while let Some(ch) = self.peek() {
                if is_op_symbol(ch) || ch.is_alphanumeric() || ch == '_' {
                    s.push(ch);
                    self.advance();
                } else { break; }
            }
            // Check if it's a keyword disguised as operator (unlikely)
            let lower = s.to_lowercase();
            if let Some(t) = self.keywords.get(&lower) {
                return Ok(t.clone());
            }
            return Ok(Token::Ident(s));
        }

        self.advance();
        Err(format!("Unexpected character '{}' at position {}", c, start))
    }
}

fn is_op_symbol(c: char) -> bool {
    matches!(c, '+' | '-' | '*' | '/' | '%' | '~' | '&' | '|' | '!' |
             '<' | '>' | '=' | '@' | '$' | '#' | '`' | '^' | '?' | ':' |
             '.' | ';' | '\\')
}

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    current: Token,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str) -> Result<Self, String> {
        let mut lexer = Lexer::new(input);
        let current = lexer.next_token()?;
        Ok(Parser { lexer, current })
    }

    fn advance(&mut self) -> Result<(), String> {
        self.current = self.lexer.next_token()?;
        Ok(())
    }

    fn expect(&mut self, tok: Token) -> Result<(), String> {
        if std::mem::discriminant(&self.current) == std::mem::discriminant(&tok) {
            self.advance()?;
            Ok(())
        } else {
            Err(format!("Expected {:?}, got {:?}", tok, self.current))
        }
    }

    fn expect_keyword(&mut self, keyword: &str) -> Result<(), String> {
        match &self.current {
            Token::Ident(s) if s.eq_ignore_ascii_case(keyword) => {
                self.advance()?;
                Ok(())
            }
            _ => Err(format!("Expected keyword '{}', got {:?}", keyword, self.current)),
        }
    }

    pub fn parse(&mut self) -> Result<Vec<Module>, String> {
        let mut modules = Vec::new();
        while self.current != Token::Eof {
            match self.current {
                Token::Fmod => modules.push(self.parse_fmod()?),
                Token::Mod => modules.push(self.parse_mod()?),
                _ => {
                    // Skip non-module tokens (commands, etc.) for now
                    self.advance()?;
                }
            }
        }
        Ok(modules)
    }

    /// Parse a script (modules and commands interleaved).
    pub fn parse_script(&mut self) -> Result<(Vec<Module>, Vec<Command>), String> {
        let mut modules = Vec::new();
        let mut commands = Vec::new();
        while self.current != Token::Eof {
            match self.current {
                Token::Fmod => modules.push(self.parse_fmod()?),
                Token::Mod => modules.push(self.parse_mod()?),
                Token::Red | Token::Rew | Token::Search | Token::Load | Token::Select => {
                    commands.push(self.parse_command()?);
                }
                _ => {
                    self.advance()?;
                }
            }
        }
        Ok((modules, commands))
    }

    pub fn parse_command(&mut self) -> Result<Command, String> {
        match self.current {
            Token::Red => {
                self.advance()?;
                let vars = HashMap::new();
                let term = self.parse_term(&vars)?;
                self.expect(Token::Dot)?;
                Ok(Command::Red { term })
            }
            Token::Rew => {
                self.advance()?;
                let vars = HashMap::new();
                let term = self.parse_term(&vars)?;
                self.expect(Token::Dot)?;
                Ok(Command::Rew { term })
            }
            Token::Load => {
                self.advance()?;
                let file = self.parse_ident()?;
                self.expect(Token::Dot)?;
                Ok(Command::Load { file })
            }
            Token::Select => {
                self.advance()?;
                let module = self.parse_ident()?;
                self.expect(Token::Dot)?;
                Ok(Command::Select { module })
            }
            _ => Err(format!("Expected command, got {:?}", self.current)),
        }
    }

    fn parse_fmod(&mut self) -> Result<Module, String> {
        self.expect(Token::Fmod)?;
        let name = self.parse_ident()?;
        self.expect_keyword("is")?;
        let (imports, sorts, subsorts, ops, _vars, eqs, membs) = self.parse_module_body()?;
        self.expect(Token::Endfm)?;
        Ok(Module::Functional {
            name, imports, sorts, subsorts, ops,
            equations: eqs, memberships: membs,
        })
    }

    fn parse_mod(&mut self) -> Result<Module, String> {
        self.expect(Token::Mod)?;
        let name = self.parse_ident()?;
        self.expect_keyword("is")?;
        let (imports, sorts, subsorts, ops, vars, eqs, membs) = self.parse_module_body()?;
        // Parse rules
        let mut rules = Vec::new();
        while matches!(self.current, Token::Rl | Token::Crl) {
            rules.push(self.parse_rule(&vars)?);
        }
        self.expect(Token::Endm)?;
        Ok(Module::System {
            name, imports, sorts, subsorts, ops,
            equations: eqs, memberships: membs, rules,
        })
    }

    fn parse_module_body(&mut self) -> Result<(Vec<Import>, Vec<Sort>, Vec<(Sort, Sort)>, Vec<OpDecl>, HashMap<String, Sort>, Vec<Equation>, Vec<Membership>), String> {
        let mut imports = Vec::new();
        let mut sorts = Vec::new();
        let mut subsorts = Vec::new();
        let mut ops = Vec::new();
        let mut vars: HashMap<String, Sort> = HashMap::new();
        let mut eqs = Vec::new();
        let mut membs = Vec::new();

        loop {
            match self.current {
                Token::Protecting | Token::Extending | Token::Including | Token::Using | Token::Inc => {
                    imports.push(self.parse_import()?);
                }
                Token::Sort | Token::Sorts => {
                    self.advance()?;
                    let sort_names = self.parse_ident_list()?;
                    for s in sort_names { sorts.push(Sort(s)); }
                    self.expect(Token::Dot)?;
                }
                Token::Subsort => {
                    self.advance()?;
                    let s1 = Sort(self.parse_ident()?);
                    self.expect(Token::Lt)?;
                    let s2 = Sort(self.parse_ident()?);
                    subsorts.push((s1, s2));
                    self.expect(Token::Dot)?;
                }
                Token::Op | Token::Ops => {
                    self.advance()?;
                    let op_names = self.parse_ident_list()?;
                    self.expect(Token::Colon)?;
                    let arity = self.parse_sort_list_arrow()?;
                    self.expect(Token::Arrow)?;
                    let coarity = Sort(self.parse_ident()?);
                    let attrs = if matches!(self.current, Token::LBracket) {
                        self.parse_op_attrs()?
                    } else { Vec::new() };
                    self.expect(Token::Dot)?;
                    for op_name in op_names {
                        ops.push(OpDecl { name: op_name, arity: arity.clone(), coarity: coarity.clone(), attrs: attrs.clone() });
                    }
                }
                Token::Var | Token::Vars => {
                    self.advance()?;
                    let names = self.parse_ident_list()?;
                    self.expect(Token::Colon)?;
                    let sort = Sort(self.parse_ident()?);
                    self.expect(Token::Dot)?;
                    for name in names {
                        vars.insert(name, sort.clone());
                    }
                }
                Token::Eq | Token::Ceq => {
                    eqs.push(self.parse_equation(&vars)?);
                }
                Token::Mb => {
                    membs.push(self.parse_membership(&vars)?);
                }
                _ => break,
            }
        }

        Ok((imports, sorts, subsorts, ops, vars, eqs, membs))
    }

    fn parse_import(&mut self) -> Result<Import, String> {
        let mode = match self.current {
            Token::Protecting => ImportMode::Protecting,
            Token::Extending => ImportMode::Extending,
            Token::Including | Token::Inc => ImportMode::Including,
            Token::Using => ImportMode::Using,
            _ => return Err(format!("Expected import mode, got {:?}", self.current)),
        };
        self.advance()?;
        let module_name = self.parse_ident()?;
        // Optional renaming: *(op a to b)
        if self.current == Token::LParen {
            // Skip renaming for now
            self.skip_balanced_parens()?;
        }
        self.expect(Token::Dot)?;
        Ok(Import { mode, module: module_name })
    }

    fn skip_balanced_parens(&mut self) -> Result<(), String> {
        let mut depth = 0;
        loop {
            match self.current {
                Token::LParen => { depth += 1; self.advance()?; }
                Token::RParen => {
                    depth -= 1;
                    self.advance()?;
                    if depth == 0 { break; }
                }
                Token::Eof => return Err("Unexpected EOF while skipping parens".to_string()),
                _ => { self.advance()?; }
            }
        }
        Ok(())
    }

    fn parse_equation(&mut self, vars: &HashMap<String, Sort>) -> Result<Equation, String> {
        let is_ceq = self.current == Token::Ceq;
        self.advance()?;
        let lhs = self.parse_term(vars)?;
        self.expect(Token::EqSign)?;
        let rhs = self.parse_term(vars)?;
        let condition = if is_ceq {
            self.expect(Token::If)?;
            Some(self.parse_conditions(vars)?)
        } else { None };
        self.expect(Token::Dot)?;
        Ok(Equation { label: None, lhs, rhs, condition })
    }

    fn parse_rule(&mut self, vars: &HashMap<String, Sort>) -> Result<Rule, String> {
        let is_crl = self.current == Token::Crl;
        self.advance()?;
        let lhs = self.parse_term(vars)?;
        self.expect(Token::DArrow)?;
        let rhs = self.parse_term(vars)?;
        let condition = if is_crl {
            self.expect(Token::If)?;
            Some(self.parse_conditions(vars)?)
        } else { None };
        self.expect(Token::Dot)?;
        Ok(Rule { label: None, lhs, rhs, condition })
    }

    fn parse_membership(&mut self, vars: &HashMap<String, Sort>) -> Result<Membership, String> {
        self.advance()?; // mb or cmb
        let term = self.parse_term(vars)?;
        self.expect(Token::Colon)?;
        let sort = Sort(self.parse_ident()?);
        let condition = if self.current == Token::If {
            self.advance()?;
            Some(self.parse_conditions(vars)?)
        } else { None };
        self.expect(Token::Dot)?;
        Ok(Membership { term, sort, condition })
    }

    fn parse_conditions(&mut self, vars: &HashMap<String, Sort>) -> Result<Vec<Condition>, String> {
        let mut conds = Vec::new();
        loop {
            let t1 = self.parse_term(vars)?;
            match self.current {
                Token::EqSign => {
                    self.advance()?;
                    let t2 = self.parse_term(vars)?;
                    conds.push(Condition::Eq(t1, t2));
                }
                Token::DArrow => {
                    self.advance()?;
                    let t2 = self.parse_term(vars)?;
                    conds.push(Condition::Rewrite(t1, t2));
                }
                Token::Colon => {
                    // := pattern
                    self.advance()?;
                    if self.current == Token::EqSign {
                        self.advance()?;
                        let t2 = self.parse_term(vars)?;
                        conds.push(Condition::Match(t1, t2));
                    } else {
                        return Err("Expected := in match condition".to_string());
                    }
                }
                _ => return Err(format!("Expected condition operator, got {:?}", self.current)),
            }
            if self.current == Token::Semi {
                self.advance()?;
            } else {
                break;
            }
        }
        Ok(conds)
    }

    fn parse_op_attrs(&mut self) -> Result<Vec<OpAttr>, String> {
        self.expect(Token::LBracket)?;
        let mut attrs = Vec::new();
        while self.current != Token::RBracket {
            let attr_name = self.parse_ident()?;
            match attr_name.as_str() {
                "assoc" => attrs.push(OpAttr::Assoc),
                "comm" => attrs.push(OpAttr::Comm),
                "id" => {
                    self.expect(Token::Colon)?;
                    // Parse a simple term as identity
                    let id_term = self.parse_simple_term()?;
                    attrs.push(OpAttr::Id(id_term));
                }
                "left" => {
                    self.expect(Token::Ident("id".to_string()))?;
                    self.expect(Token::Colon)?;
                    let id_term = self.parse_simple_term()?;
                    attrs.push(OpAttr::LeftId(id_term));
                }
                "right" => {
                    self.expect(Token::Ident("id".to_string()))?;
                    self.expect(Token::Colon)?;
                    let id_term = self.parse_simple_term()?;
                    attrs.push(OpAttr::RightId(id_term));
                }
                "memo" => attrs.push(OpAttr::Memo),
                "ditto" => attrs.push(OpAttr::Ditto),
                "config" => attrs.push(OpAttr::Config),
                "object" => attrs.push(OpAttr::Object),
                "message" => attrs.push(OpAttr::Message),
                "strat" => {
                    self.expect(Token::LParen)?;
                    let mut strat = Vec::new();
                    while self.current != Token::RParen {
                        if let Token::NatLit(n) = self.current {
                            strat.push(n as i32);
                            self.advance()?;
                        } else if let Token::Minus = &self.current {
                            self.advance()?;
                            if let Token::NatLit(n) = self.current {
                                strat.push(-(n as i32));
                                self.advance()?;
                            }
                        }
                        if self.current == Token::Comma { self.advance()?; }
                    }
                    self.expect(Token::RParen)?;
                    attrs.push(OpAttr::Strat(strat));
                }
                "prec" => {
                    self.expect(Token::LParen)?;
                    if let Token::NatLit(n) = self.current {
                        attrs.push(OpAttr::Prec(n as i32));
                        self.advance()?;
                    }
                    self.expect(Token::RParen)?;
                }
                "gather" => {
                    self.expect(Token::LParen)?;
                    let mut gather = Vec::new();
                    while self.current != Token::RParen {
                        gather.push(self.parse_ident()?);
                        if self.current == Token::Comma { self.advance()?; }
                    }
                    self.expect(Token::RParen)?;
                    attrs.push(OpAttr::Gather(gather));
                }
                "format" => {
                    self.expect(Token::LParen)?;
                    let mut fmt = Vec::new();
                    while self.current != Token::RParen {
                        fmt.push(self.parse_ident()?);
                        if self.current == Token::Comma { self.advance()?; }
                    }
                    self.expect(Token::RParen)?;
                    attrs.push(OpAttr::Format(fmt));
                }
                "special" => {
                    self.expect(Token::LParen)?;
                    let special_name = self.parse_ident()?;
                    let mut special_args = HashMap::new();
                    while self.current != Token::RParen {
                        let key = self.parse_ident()?;
                        self.expect(Token::EqSign)?;
                        let val = self.parse_ident()?;
                        special_args.insert(key, val);
                        if self.current == Token::Comma { self.advance()?; }
                    }
                    self.expect(Token::RParen)?;
                    attrs.push(OpAttr::Special(special_name, special_args));
                }
                "poly" => {
                    self.expect(Token::LParen)?;
                    let mut poly = Vec::new();
                    while self.current != Token::RParen {
                        poly.push(Sort(self.parse_ident()?));
                        if self.current == Token::Comma { self.advance()?; }
                    }
                    self.expect(Token::RParen)?;
                    attrs.push(OpAttr::Poly(poly));
                }
                "frozen" => {
                    self.expect(Token::LParen)?;
                    let mut frozen = Vec::new();
                    while self.current != Token::RParen {
                        if let Token::NatLit(n) = self.current {
                            frozen.push(n as i32);
                            self.advance()?;
                        }
                        if self.current == Token::Comma { self.advance()?; }
                    }
                    self.expect(Token::RParen)?;
                    attrs.push(OpAttr::Frozen(frozen));
                }
                _ => {
                    // Unknown attribute, skip until comma or bracket
                    while !matches!(self.current, Token::Comma | Token::RBracket | Token::Eof) {
                        self.advance()?;
                    }
                }
            }
            if self.current == Token::Comma { self.advance()?; }
        }
        self.expect(Token::RBracket)?;
        Ok(attrs)
    }

    fn parse_simple_term(&mut self) -> Result<Term, String> {
        // Parse a simple term without variables for op attrs like id: nil
        match &self.current {
            Token::Ident(name) => {
                let n = name.clone();
                self.advance()?;
                Ok(Term::Constant(n, Sort("unknown".to_string())))
            }
            Token::NatLit(n) => {
                let v = *n;
                self.advance()?;
                Ok(Term::NatLiteral(v))
            }
            Token::StringLit(s) => {
                let v = s.clone();
                self.advance()?;
                Ok(Term::StringLiteral(v))
            }
            _ => Err(format!("Expected simple term, got {:?}", self.current)),
        }
    }

    pub fn parse_term(&mut self, vars: &HashMap<String, Sort>) -> Result<Term, String> {
        self.parse_term_precedence(vars, 0)
    }

    fn parse_term_precedence(&mut self, vars: &HashMap<String, Sort>, min_prec: i32) -> Result<Term, String> {
        let mut left = self.parse_term_atom(vars)?;

        // Handle postfix and infix applications
        loop {
            // Check for postfix operator application (e.g., X !, s_^3(0))
            if let Token::Ident(ref op) = self.current.clone() {
                // Simple infix/postfix parsing
                // For now, treat adjacent terms as application: f(X) or X + Y
                // This is simplified; real Maude parsing is more complex
                if self.is_potential_infix_or_postfix(op) {
                    // Try to parse as infix
                    let op_name = op.clone();
                    self.advance()?;

                    // Handle iteration: s_^3(0)
                    if op_name == "^" {
                        if let Token::NatLit(n) = self.current {
                            self.advance()?;
                            // This is iteration; wrap left in iter application
                            left = Term::Application {
                                op: format!("{}^{}", get_base_op(&left), n),
                                args: vec![left],
                                sort: Sort("unknown".to_string()),
                            };
                            continue;
                        }
                    }

                    let right = self.parse_term_precedence(vars, min_prec)?;
                    left = Term::Application {
                        op: op_name,
                        args: vec![left, right],
                        sort: Sort("unknown".to_string()),
                    };
                    continue;
                }
            }

            // Check for parenthesized arguments: f(X, Y) or s_ (0)
            if self.current == Token::LParen {
                // Could be function application arguments
                self.advance()?;
                let mut args = Vec::new();
                while self.current != Token::RParen {
                    args.push(self.parse_term_precedence(vars, 0)?);
                    if self.current == Token::Comma { self.advance()?; }
                }
                self.expect(Token::RParen)?;

                left = match left {
                    Term::Constant(name, sort) => Term::Application { op: name, args, sort },
                    Term::Variable(name, sort) => {
                        if args.is_empty() {
                            Term::Variable(name, sort)
                        } else {
                            Term::Application { op: name, args, sort }
                        }
                    }
                    Term::Application { op, args: mut existing, sort } => {
                        existing.extend(args);
                        Term::Application { op, args: existing, sort }
                    }
                    other => other,
                };
                continue;
            }

            break;
        }

        Ok(left)
    }

    fn is_potential_infix_or_postfix(&self, op: &str) -> bool {
        // Heuristic: if op starts/ends with underscore or contains operator symbols, it's mixfix
        op.starts_with('_') || op.ends_with('_') ||
        op.chars().any(|c| matches!(c, '+' | '-' | '*' | '/' | '%' | '&' | '|' | '^' | '<' | '>' | '=' | '!' | '~' | '@' | '$'))
    }

    fn parse_term_atom(&mut self, vars: &HashMap<String, Sort>) -> Result<Term, String> {
        match &self.current.clone() {
            Token::Ident(name) => {
                let n = name.clone();
                self.advance()?;

                // Check if it's a variable reference with explicit sort: X:Nat
                if self.current == Token::Colon {
                    self.advance()?;
                    let sort_name = self.parse_ident()?;
                    Ok(Term::Variable(n, Sort(sort_name)))
                } else {
                    // Check if it's a known variable
                    if let Some(sort) = vars.get(&n) {
                        Ok(Term::Variable(n, sort.clone()))
                    } else {
                        Ok(Term::Constant(n, Sort("unknown".to_string())))
                    }
                }
            }
            Token::NatLit(n) => {
                let v = *n;
                self.advance()?;
                Ok(Term::NatLiteral(v))
            }
            Token::StringLit(s) => {
                let v = s.clone();
                self.advance()?;
                Ok(Term::StringLiteral(v))
            }
            Token::Apostrophe => {
                // Quoted identifier: 'foo
                self.advance()?;
                let name = self.parse_ident()?;
                Ok(Term::Qid(name))
            }
            Token::LParen => {
                self.advance()?;
                let term = self.parse_term(vars)?;
                self.expect(Token::RParen)?;
                Ok(term)
            }
            Token::Minus => {
                // Negative number
                self.advance()?;
                if let Token::NatLit(n) = self.current {
                    let v = n;
                    self.advance()?;
                    // Represent as unary minus application
                    Ok(Term::Application {
                        op: "-".to_string(),
                        args: vec![Term::NatLiteral(v)],
                        sort: Sort("unknown".to_string()),
                    })
                } else {
                    Err("Expected number after minus".to_string())
                }
            }
            _ => Err(format!("Unexpected token in term: {:?}", self.current)),
        }
    }

    fn parse_ident(&mut self) -> Result<String, String> {
        match &self.current {
            Token::Ident(s) => {
                let name = s.clone();
                self.advance()?;
                Ok(name)
            }
            _ => Err(format!("Expected identifier, got {:?}", self.current)),
        }
    }

    fn parse_ident_list(&mut self) -> Result<Vec<String>, String> {
        let mut list = Vec::new();
        loop {
            match &self.current {
                Token::Ident(s) => {
                    list.push(s.clone());
                    self.advance()?;
                }
                _ => break,
            }
        }
        Ok(list)
    }

    fn parse_sort_list_arrow(&mut self) -> Result<Vec<Sort>, String> {
        let mut list = Vec::new();
        while !matches!(self.current, Token::Arrow | Token::Eof) {
            let name = self.parse_ident()?;
            list.push(Sort(name));
        }
        Ok(list)
    }
}

fn get_base_op(term: &Term) -> String {
    match term {
        Term::Application { op, .. } => op.clone(),
        Term::Constant(name, _) => name.clone(),
        _ => "op".to_string(),
    }
}

// Missing Token variants that parser references
impl Token {
    pub fn as_ident(&self) -> Option<&str> {
        match self {
            Token::Ident(s) => Some(s),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_fmod() {
        let input = r#"
            fmod NAT_SIMPLE is
                sort Nat .
                op z : -> Nat .
                op s : Nat -> Nat .
                vars M N : Nat .
                eq z = z .
            endfm
        "#;
        let mut parser = Parser::new(input).unwrap();
        let modules = parser.parse().unwrap();
        assert_eq!(modules.len(), 1);
        match &modules[0] {
            Module::Functional { name, sorts, ops, equations, .. } => {
                assert_eq!(name, "NAT_SIMPLE");
                assert_eq!(sorts.len(), 1);
                assert_eq!(ops.len(), 2);
                assert_eq!(equations.len(), 1);
            }
            _ => panic!("Expected functional module"),
        }
    }

    #[test]
    fn test_parse_system_mod() {
        let input = r#"
            mod COUNTER is
                sort Counter .
                op mk : Nat -> Counter .
                var N : Nat .
                rl mk(N) => mk(N) .
            endm
        "#;
        let mut parser = Parser::new(input).unwrap();
        let modules = parser.parse().unwrap();
        assert_eq!(modules.len(), 1);
        match &modules[0] {
            Module::System { name, rules, .. } => {
                assert_eq!(name, "COUNTER");
                assert_eq!(rules.len(), 1);
            }
            _ => panic!("Expected system module"),
        }
    }

    #[test]
    fn test_parse_term_constant() {
        let input = "z";
        let mut parser = Parser::new(input).unwrap();
        let vars = HashMap::new();
        let term = parser.parse_term(&vars).unwrap();
        assert!(matches!(term, Term::Constant(name, _) if name == "z"));
    }

    #[test]
    fn test_parse_term_application() {
        let input = "s(z)";
        let mut parser = Parser::new(input).unwrap();
        let vars = HashMap::new();
        let term = parser.parse_term(&vars).unwrap();
        assert!(matches!(term, Term::Application { args, .. } if args.len() == 1));
    }

    #[test]
    fn test_parse_term_nat_literal() {
        let input = "42";
        let mut parser = Parser::new(input).unwrap();
        let vars = HashMap::new();
        let term = parser.parse_term(&vars).unwrap();
        assert!(matches!(term, Term::NatLiteral(42)));
    }

    #[test]
    fn test_parse_term_string_literal() {
        let input = r#""hello""#;
        let mut parser = Parser::new(input).unwrap();
        let vars = HashMap::new();
        let term = parser.parse_term(&vars).unwrap();
        assert!(matches!(term, Term::StringLiteral(s) if s == "hello"));
    }

    #[test]
    fn test_parse_term_qid() {
        let input = "'foo";
        let mut parser = Parser::new(input).unwrap();
        let vars = HashMap::new();
        let term = parser.parse_term(&vars).unwrap();
        assert!(matches!(term, Term::Qid(q) if q == "foo"));
    }

    #[test]
    fn test_parse_term_variable() {
        let input = "N";
        let mut parser = Parser::new(input).unwrap();
        let mut vars = HashMap::new();
        vars.insert("N".to_string(), Sort("Nat".to_string()));
        let term = parser.parse_term(&vars).unwrap();
        assert!(matches!(term, Term::Variable(name, sort) if name == "N" && sort.0 == "Nat"));
    }

    #[test]
    fn test_parse_red_command() {
        let input = "red not(true) .";
        let mut parser = Parser::new(input).unwrap();
        let cmd = parser.parse_command().unwrap();
        assert!(matches!(cmd, Command::Red { term } if matches!(&term, Term::Application { args, .. } if args.len() == 1)));
    }

    #[test]
    fn test_parse_script_with_modules_and_commands() {
        let input = r#"
            fmod NAT is
                sort Nat .
                op z : -> Nat .
                op s : Nat -> Nat .
            endfm
            red s(z) .
        "#;
        let mut parser = Parser::new(input).unwrap();
        let (modules, commands) = parser.parse_script().unwrap();
        assert_eq!(modules.len(), 1);
        assert_eq!(commands.len(), 1);
        assert!(matches!(commands[0], Command::Red { .. }));
    }
}
