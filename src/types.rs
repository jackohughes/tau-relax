use crate::ast::Region;

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    Int,
    Unit,
    Ref(Box<Ty>),
    Flag,
    Var(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeWithPlace {
    pub ty: Ty,
    pub region: Region,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EffectKind {
    Read,
    Write,
    New,
    Free,
    Wait,
    Flag,
    Fence,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Effect {
    pub kind: EffectKind,
    pub region: Region,
    pub index: usize,
}

pub type EffectList = Vec<Effect>;

pub type EffectBar = Vec<EffectList>;