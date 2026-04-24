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

/// Definition safety level
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefinitionSafety {
    Unsafe,
    Safe,
    Partial,
}

/// A declaration in the environment.
/// TTobs core only has Axiom and Definition.
/// Inductive types, quotients, etc. are outer-layer features.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Declaration {
    Axiom(AxiomVal),
    Definition(DefinitionVal),
    MutualDefinition(Vec<DefinitionVal>),
}

impl Declaration {
    pub fn is_definition(&self) -> bool {
        matches!(self, Declaration::Definition(_))
    }

    pub fn is_axiom(&self) -> bool {
        matches!(self, Declaration::Axiom(_))
    }

    pub fn is_unsafe(&self) -> bool {
        match self {
            Declaration::Axiom(v) => v.is_unsafe,
            Declaration::Definition(v) => matches!(v.safety, DefinitionSafety::Unsafe),
            Declaration::MutualDefinition(vs) => vs.iter().any(|v| matches!(v.safety, DefinitionSafety::Unsafe)),
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
}

/// Constant information stored in the environment
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstantInfo {
    AxiomInfo(AxiomVal),
    DefinitionInfo(DefinitionVal),
}

impl ConstantInfo {
    pub fn from_declaration(decl: &Declaration) -> Option<Self> {
        match decl {
            Declaration::Axiom(v) => Some(ConstantInfo::AxiomInfo(v.clone())),
            Declaration::Definition(v) => Some(ConstantInfo::DefinitionInfo(v.clone())),
            Declaration::MutualDefinition(_) => None,
        }
    }

    pub fn name(&self) -> &Name {
        match self {
            ConstantInfo::AxiomInfo(v) => &v.constant_val.name,
            ConstantInfo::DefinitionInfo(v) => &v.constant_val.name,
        }
    }

    pub fn get_type(&self) -> &Expr {
        match self {
            ConstantInfo::AxiomInfo(v) => &v.constant_val.ty,
            ConstantInfo::DefinitionInfo(v) => &v.constant_val.ty,
        }
    }

    pub fn get_level_params(&self) -> &Vec<Name> {
        match self {
            ConstantInfo::AxiomInfo(v) => &v.constant_val.level_params,
            ConstantInfo::DefinitionInfo(v) => &v.constant_val.level_params,
        }
    }

    pub fn is_definition(&self) -> bool {
        matches!(self, ConstantInfo::DefinitionInfo(_))
    }

    pub fn is_axiom(&self) -> bool {
        matches!(self, ConstantInfo::AxiomInfo(_))
    }

    pub fn is_unsafe(&self) -> bool {
        match self {
            ConstantInfo::AxiomInfo(v) => v.is_unsafe,
            ConstantInfo::DefinitionInfo(v) => matches!(v.safety, DefinitionSafety::Unsafe),
        }
    }

    pub fn has_value(&self) -> bool {
        self.is_definition()
    }

    pub fn get_value(&self) -> Option<&Expr> {
        match self {
            ConstantInfo::DefinitionInfo(v) => Some(&v.value),
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
}
