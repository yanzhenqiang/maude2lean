use super::expr::*;

/// Reducibility hints for definitions
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ReducibilityHints {
    Opaque,
    Abbreviation,
    Regular(u32),
}

impl ReducibilityHints {
    pub fn is_opaque(&self) -> bool {
        matches!(self, ReducibilityHints::Opaque)
    }

    pub fn is_abbrev(&self) -> bool {
        matches!(self, ReducibilityHints::Abbreviation)
    }

    pub fn is_regular(&self) -> bool {
        matches!(self, ReducibilityHints::Regular(_))
    }

    pub fn get_height(&self) -> Option<u32> {
        match self {
            ReducibilityHints::Regular(h) => Some(*h),
            _ => None,
        }
    }
}

/// Definition safety level
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefinitionSafety {
    Unsafe,
    Safe,
    Partial,
}

/// Common fields for all declarations
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstantVal {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Expr,
}

/// Axiom declaration value
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AxiomVal {
    pub constant_val: ConstantVal,
    pub is_unsafe: bool,
}

/// Definition declaration value
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefinitionVal {
    pub constant_val: ConstantVal,
    pub value: Expr,
    pub hints: ReducibilityHints,
    pub safety: DefinitionSafety,
}

/// Theorem declaration value
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TheoremVal {
    pub constant_val: ConstantVal,
    pub value: Expr,
}

/// Opaque declaration value
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OpaqueVal {
    pub constant_val: ConstantVal,
    pub value: Expr,
    pub is_unsafe: bool,
}

/// Constructor in an inductive type
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Constructor {
    pub name: Name,
    pub ty: Expr,
}

/// Inductive type declaration
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InductiveType {
    pub name: Name,
    pub ty: Expr,
    pub ctors: Vec<Constructor>,
}

/// Recursor rule
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecursorRule {
    pub ctor: Name,
    pub nfields: u64,
    pub rhs: Expr,
}

/// Recursor declaration value
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecursorVal {
    pub constant_val: ConstantVal,
    pub all: Vec<Name>,       // all inductive types in the mutual block
    pub num_params: u64,
    pub num_indices: u64,
    pub num_motives: u64,
    pub num_minors: u64,
    pub rules: Vec<RecursorRule>,
    pub k: bool,              // supports K-like reduction
    pub is_unsafe: bool,
}

impl RecursorVal {
    pub fn get_major_idx(&self) -> u64 {
        self.num_params + self.num_motives + self.num_minors + self.num_indices
    }
}

/// Inductive type declaration value
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InductiveVal {
    pub constant_val: ConstantVal,
    pub num_params: u64,
    pub num_indices: u64,
    pub all: Vec<Name>,       // all inductive types in the mutual block
    pub ctors: Vec<Name>,     // constructor names
    pub num_nested: u64,
    pub is_rec: bool,
    pub is_unsafe: bool,
    pub is_reflexive: bool,
}

/// Constructor declaration value
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstructorVal {
    pub constant_val: ConstantVal,
    pub induct: Name,         // inductive type this constructor belongs to
    pub cidx: u64,            // constructor index
    pub num_params: u64,
    pub num_fields: u64,
    pub is_unsafe: bool,
}

/// Quotient kind
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum QuotKind {
    Type,
    Mk,
    Lift,
    Ind,
}

/// Quotient declaration value
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QuotVal {
    pub constant_val: ConstantVal,
    pub kind: QuotKind,
}

/// A declaration in the environment
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Declaration {
    Axiom(AxiomVal),
    Definition(DefinitionVal),
    Theorem(TheoremVal),
    Opaque(OpaqueVal),
    Quot,
    MutualDefinition(Vec<DefinitionVal>),
    Inductive {
        level_params: Vec<Name>,
        num_params: u64,
        types: Vec<InductiveType>,
        is_unsafe: bool,
    },
}

impl Declaration {
    pub fn is_definition(&self) -> bool {
        matches!(self, Declaration::Definition(_))
    }

    pub fn is_axiom(&self) -> bool {
        matches!(self, Declaration::Axiom(_))
    }

    pub fn is_theorem(&self) -> bool {
        matches!(self, Declaration::Theorem(_))
    }

    pub fn is_opaque(&self) -> bool {
        matches!(self, Declaration::Opaque(_))
    }

    pub fn is_mutual(&self) -> bool {
        matches!(self, Declaration::MutualDefinition(_))
    }

    pub fn is_inductive(&self) -> bool {
        matches!(self, Declaration::Inductive { .. })
    }

    pub fn is_unsafe(&self) -> bool {
        match self {
            Declaration::Axiom(v) => v.is_unsafe,
            Declaration::Definition(v) => matches!(v.safety, DefinitionSafety::Unsafe),
            Declaration::Theorem(_) => false,
            Declaration::Opaque(v) => v.is_unsafe,
            Declaration::Quot => false,
            Declaration::MutualDefinition(vs) => vs.iter().any(|v| matches!(v.safety, DefinitionSafety::Unsafe)),
            Declaration::Inductive { is_unsafe, .. } => *is_unsafe,
        }
    }

    pub fn has_value(&self) -> bool {
        self.is_definition()
    }

    pub fn to_definition_val(&self) -> Option<&DefinitionVal> {
        match self {
            Declaration::Definition(v) => Some(v),
            _ => None,
        }
    }

    pub fn to_axiom_val(&self) -> Option<&AxiomVal> {
        match self {
            Declaration::Axiom(v) => Some(v),
            _ => None,
        }
    }

    pub fn to_theorem_val(&self) -> Option<&TheoremVal> {
        match self {
            Declaration::Theorem(v) => Some(v),
            _ => None,
        }
    }

    pub fn to_opaque_val(&self) -> Option<&OpaqueVal> {
        match self {
            Declaration::Opaque(v) => Some(v),
            _ => None,
        }
    }

    pub fn to_inductive_val(&self) -> Option<(&Vec<Name>, u64, &Vec<InductiveType>, bool)> {
        match self {
            Declaration::Inductive { level_params, num_params, types, is_unsafe } => {
                Some((level_params, *num_params, types, *is_unsafe))
            }
            _ => None,
        }
    }
}

/// Constant information stored in the environment
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstantInfo {
    AxiomInfo(AxiomVal),
    DefinitionInfo(DefinitionVal),
    TheoremInfo(TheoremVal),
    OpaqueInfo(OpaqueVal),
    QuotInfo(QuotVal),
    InductiveInfo(InductiveVal),
    ConstructorInfo(ConstructorVal),
    RecursorInfo(RecursorVal),
}

impl ConstantInfo {
    pub fn from_declaration(decl: &Declaration) -> Option<Self> {
        match decl {
            Declaration::Axiom(v) => Some(ConstantInfo::AxiomInfo(v.clone())),
            Declaration::Definition(v) => Some(ConstantInfo::DefinitionInfo(v.clone())),
            Declaration::Theorem(v) => Some(ConstantInfo::TheoremInfo(v.clone())),
            Declaration::Opaque(v) => Some(ConstantInfo::OpaqueInfo(v.clone())),
            Declaration::Quot => None,
            Declaration::MutualDefinition(_) => None,
            Declaration::Inductive { .. } => None,
        }
    }

    pub fn name(&self) -> &Name {
        match self {
            ConstantInfo::AxiomInfo(v) => &v.constant_val.name,
            ConstantInfo::DefinitionInfo(v) => &v.constant_val.name,
            ConstantInfo::TheoremInfo(v) => &v.constant_val.name,
            ConstantInfo::OpaqueInfo(v) => &v.constant_val.name,
            ConstantInfo::QuotInfo(v) => &v.constant_val.name,
            ConstantInfo::InductiveInfo(v) => &v.constant_val.name,
            ConstantInfo::ConstructorInfo(v) => &v.constant_val.name,
            ConstantInfo::RecursorInfo(v) => &v.constant_val.name,
        }
    }

    pub fn get_type(&self) -> &Expr {
        match self {
            ConstantInfo::AxiomInfo(v) => &v.constant_val.ty,
            ConstantInfo::DefinitionInfo(v) => &v.constant_val.ty,
            ConstantInfo::TheoremInfo(v) => &v.constant_val.ty,
            ConstantInfo::OpaqueInfo(v) => &v.constant_val.ty,
            ConstantInfo::QuotInfo(v) => &v.constant_val.ty,
            ConstantInfo::InductiveInfo(v) => &v.constant_val.ty,
            ConstantInfo::ConstructorInfo(v) => &v.constant_val.ty,
            ConstantInfo::RecursorInfo(v) => &v.constant_val.ty,
        }
    }

    pub fn get_level_params(&self) -> &Vec<Name> {
        match self {
            ConstantInfo::AxiomInfo(v) => &v.constant_val.level_params,
            ConstantInfo::DefinitionInfo(v) => &v.constant_val.level_params,
            ConstantInfo::TheoremInfo(v) => &v.constant_val.level_params,
            ConstantInfo::OpaqueInfo(v) => &v.constant_val.level_params,
            ConstantInfo::QuotInfo(v) => &v.constant_val.level_params,
            ConstantInfo::InductiveInfo(v) => &v.constant_val.level_params,
            ConstantInfo::ConstructorInfo(v) => &v.constant_val.level_params,
            ConstantInfo::RecursorInfo(v) => &v.constant_val.level_params,
        }
    }

    pub fn is_definition(&self) -> bool {
        matches!(self, ConstantInfo::DefinitionInfo(_))
    }

    pub fn is_axiom(&self) -> bool {
        matches!(self, ConstantInfo::AxiomInfo(_))
    }

    pub fn is_theorem(&self) -> bool {
        matches!(self, ConstantInfo::TheoremInfo(_))
    }

    pub fn is_opaque(&self) -> bool {
        matches!(self, ConstantInfo::OpaqueInfo(_))
    }

    pub fn is_inductive(&self) -> bool {
        matches!(self, ConstantInfo::InductiveInfo(_))
    }

    pub fn is_constructor(&self) -> bool {
        matches!(self, ConstantInfo::ConstructorInfo(_))
    }

    pub fn is_recursor(&self) -> bool {
        matches!(self, ConstantInfo::RecursorInfo(_))
    }

    pub fn is_quot(&self) -> bool {
        matches!(self, ConstantInfo::QuotInfo(_))
    }

    pub fn is_unsafe(&self) -> bool {
        match self {
            ConstantInfo::AxiomInfo(v) => v.is_unsafe,
            ConstantInfo::DefinitionInfo(v) => matches!(v.safety, DefinitionSafety::Unsafe),
            ConstantInfo::TheoremInfo(_) => false,
            ConstantInfo::OpaqueInfo(v) => v.is_unsafe,
            ConstantInfo::QuotInfo(_) => false,
            ConstantInfo::InductiveInfo(v) => v.is_unsafe,
            ConstantInfo::ConstructorInfo(v) => v.is_unsafe,
            ConstantInfo::RecursorInfo(v) => v.is_unsafe,
        }
    }

    pub fn has_value(&self, allow_opaque: bool) -> bool {
        self.is_definition() || self.is_theorem() || (allow_opaque && self.is_opaque())
    }

    pub fn get_value(&self, allow_opaque: bool) -> Option<&Expr> {
        match self {
            ConstantInfo::DefinitionInfo(v) => Some(&v.value),
            ConstantInfo::TheoremInfo(v) => Some(&v.value),
            ConstantInfo::OpaqueInfo(v) if allow_opaque => Some(&v.value),
            _ => None,
        }
    }

    pub fn get_hints(&self) -> Option<&ReducibilityHints> {
        match self {
            ConstantInfo::DefinitionInfo(v) => Some(&v.hints),
            _ => None,
        }
    }

    pub fn to_definition_val(&self) -> Option<&DefinitionVal> {
        match self {
            ConstantInfo::DefinitionInfo(v) => Some(v),
            _ => None,
        }
    }

    pub fn to_inductive_val(&self) -> Option<&InductiveVal> {
        match self {
            ConstantInfo::InductiveInfo(v) => Some(v),
            _ => None,
        }
    }

    pub fn to_constructor_val(&self) -> Option<&ConstructorVal> {
        match self {
            ConstantInfo::ConstructorInfo(v) => Some(v),
            _ => None,
        }
    }

    pub fn to_recursor_val(&self) -> Option<&RecursorVal> {
        match self {
            ConstantInfo::RecursorInfo(v) => Some(v),
            _ => None,
        }
    }

    pub fn to_quot_val(&self) -> Option<&QuotVal> {
        match self {
            ConstantInfo::QuotInfo(v) => Some(v),
            _ => None,
        }
    }
}
