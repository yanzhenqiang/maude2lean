use std::collections::{HashMap, HashSet};

/// A sort name in Maude, e.g., `Nat`, `Bool`, `Qid`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Sort(pub String);

/// A kind (connected component of sorts) in Maude.
/// Terms that are ill-sorted but belong to the same kind are allowed.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Kind(pub Vec<Sort>);

/// An operator attribute, e.g., `assoc`, `comm`, `id: 0`, `prec 33`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OpAttr {
    Assoc,
    Comm,
    Id(Term),
    LeftId(Term),
    RightId(Term),
    Iter(String), // iteration operator name
    Strat(Vec<i32>), // evaluation strategy
    Memo,
    Prec(i32),
    Gather(Vec<String>),
    Format(Vec<String>),
    Special(String, HashMap<String, String>),
    Poly(Vec<Sort>), // polymorphic sorts
    Ditto,
    Config,
    Object,
    Message,
    Frozen(Vec<i32>),
}

/// Operator declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpDecl {
    pub name: String,
    pub arity: Vec<Sort>,
    pub coarity: Sort,
    pub attrs: Vec<OpAttr>,
}

/// A term in Maude.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// A variable, e.g., `X:Nat` or just `X`.
    Variable(String, Sort),
    /// A constant (zero-ary operator application), e.g., `0`, `true`.
    Constant(String, Sort),
    /// An operator application, e.g., `s_ N`, `_+_(M, N)`.
    Application {
        op: String,
        args: Vec<Term>,
        sort: Sort,
    },
    /// A quoted identifier literal, e.g., `'foo`.
    Qid(String),
    /// A string literal.
    StringLiteral(String),
    /// A natural number literal.
    NatLiteral(u64),
    /// A float literal.
    FloatLiteral(String),
}

impl Term {
    pub fn sort(&self) -> Option<&Sort> {
        match self {
            Term::Variable(_, s) => Some(s),
            Term::Constant(_, s) => Some(s),
            Term::Application { sort, .. } => Some(sort),
            Term::Qid(_) => None, // resolved later to Qid sort
            Term::StringLiteral(_) => None,
            Term::NatLiteral(_) => None,
            Term::FloatLiteral(_) => None,
        }
    }

    pub fn set_sort(&mut self, new_sort: Sort) {
        match self {
            Term::Variable(_, s) => *s = new_sort,
            Term::Constant(_, s) => *s = new_sort,
            Term::Application { sort, .. } => *sort = new_sort,
            _ => {}
        }
    }

    /// Collect all variables in the term.
    pub fn variables(&self) -> HashSet<(String, Sort)> {
        let mut vars = HashSet::new();
        self.collect_variables(&mut vars);
        vars
    }

    fn collect_variables(&self, vars: &mut HashSet<(String, Sort)>) {
        match self {
            Term::Variable(name, sort) => {
                vars.insert((name.clone(), sort.clone()));
            }
            Term::Application { args, .. } => {
                for arg in args {
                    arg.collect_variables(vars);
                }
            }
            _ => {}
        }
    }

    /// Apply a substitution to this term.
    pub fn substitute(&self, subst: &HashMap<String, Term>) -> Term {
        match self {
            Term::Variable(name, sort) => {
                if let Some(t) = subst.get(name) {
                    t.clone()
                } else {
                    Term::Variable(name.clone(), sort.clone())
                }
            }
            Term::Application { op, args, sort } => {
                let new_args: Vec<Term> = args.iter().map(|a| a.substitute(subst)).collect();
                Term::Application {
                    op: op.clone(),
                    args: new_args,
                    sort: sort.clone(),
                }
            }
            other => other.clone(),
        }
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Variable(name, sort) => {
                if sort.0 == "unknown" {
                    write!(f, "{}", name)
                } else {
                    write!(f, "{}:{}", name, sort.0)
                }
            }
            Term::Constant(name, sort) => {
                if sort.0 == "unknown" {
                    write!(f, "{}", name)
                } else {
                    write!(f, "{}", name)
                }
            }
            Term::Application { op, args, .. } => {
                if args.is_empty() {
                    write!(f, "{}", op)
                } else {
                    write!(f, "{}(", op)?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", arg)?;
                    }
                    write!(f, ")")
                }
            }
            Term::Qid(q) => write!(f, "'{}", q),
            Term::StringLiteral(s) => write!(f, "\"{}\"", s),
            Term::NatLiteral(n) => write!(f, "{}", n),
            Term::FloatLiteral(s) => write!(f, "{}", s),
        }
    }
}

/// A condition in a conditional equation or rule.
/// Can be a matching condition `lhs := rhs`, a boolean condition `b = true`,
/// or a rewrite condition `lhs => rhs`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Condition {
    /// Matching condition: `term := pattern`
    Match(Term, Term),
    /// Boolean equation condition: `term = true`
    Eq(Term, Term),
    /// Rewrite condition: `term => pattern`
    Rewrite(Term, Term),
}

/// An equation: `eq [label] lhs = rhs .` or `ceq [label] lhs = rhs if cond .`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Equation {
    pub label: Option<String>,
    pub lhs: Term,
    pub rhs: Term,
    pub condition: Option<Vec<Condition>>,
}

/// A rewrite rule: `rl [label] lhs => rhs .` or `crl [label] lhs => rhs if cond .`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    pub label: Option<String>,
    pub lhs: Term,
    pub rhs: Term,
    pub condition: Option<Vec<Condition>>,
}

/// A membership axiom: `mb term : sort .` or `cmb term : sort if cond .`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Membership {
    pub term: Term,
    pub sort: Sort,
    pub condition: Option<Vec<Condition>>,
}

/// Module import directive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportMode {
    Protecting,
    Extending,
    Including,
    Using,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Import {
    pub mode: ImportMode,
    pub module: String,
}

/// A Maude module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Module {
    /// Functional module: `fmod NAME is ... endfm`
    Functional {
        name: String,
        imports: Vec<Import>,
        sorts: Vec<Sort>,
        subsorts: Vec<(Sort, Sort)>,
        ops: Vec<OpDecl>,
        equations: Vec<Equation>,
        memberships: Vec<Membership>,
    },
    /// System module: `mod NAME is ... endm`
    System {
        name: String,
        imports: Vec<Import>,
        sorts: Vec<Sort>,
        subsorts: Vec<(Sort, Sort)>,
        ops: Vec<OpDecl>,
        equations: Vec<Equation>,
        memberships: Vec<Membership>,
        rules: Vec<Rule>,
    },
}

/// A top-level command in a Maude script.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Command {
    /// Reduce a term: `red term .`
    Red { term: Term },
    /// Rewrite a term: `rew term .`
    Rew { term: Term },
    /// Search: `search term =>* pattern .`
    Search { term: Term, pattern: Term },
    /// Load a file: `load file.maude`
    Load { file: String },
    /// Select a module: `select MODULE .`
    Select { module: String },
}

impl Module {
    pub fn name(&self) -> &str {
        match self {
            Module::Functional { name, .. } => name,
            Module::System { name, .. } => name,
        }
    }

    pub fn sorts(&self) -> &Vec<Sort> {
        match self {
            Module::Functional { sorts, .. } => sorts,
            Module::System { sorts, .. } => sorts,
        }
    }

    pub fn subsorts(&self) -> &Vec<(Sort, Sort)> {
        match self {
            Module::Functional { subsorts, .. } => subsorts,
            Module::System { subsorts, .. } => subsorts,
        }
    }

    pub fn ops(&self) -> &Vec<OpDecl> {
        match self {
            Module::Functional { ops, .. } => ops,
            Module::System { ops, .. } => ops,
        }
    }

    pub fn equations(&self) -> &Vec<Equation> {
        match self {
            Module::Functional { equations, .. } => equations,
            Module::System { equations, .. } => equations,
        }
    }

    pub fn rules(&self) -> Option<&Vec<Rule>> {
        match self {
            Module::Functional { .. } => None,
            Module::System { rules, .. } => Some(rules),
        }
    }

    pub fn imports(&self) -> &Vec<Import> {
        match self {
            Module::Functional { imports, .. } => imports,
            Module::System { imports, .. } => imports,
        }
    }
}
