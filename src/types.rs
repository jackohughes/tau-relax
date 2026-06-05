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

#[derive(Debug, Clone, PartialEq)]
pub enum EffectSeq {
    Empty,
    Single(Effect),
    Seq(Box<EffectSeq>, Box<EffectSeq>),
    Branch(Box<EffectSeq>, Box<EffectSeq>),
}

impl EffectSeq {

    pub fn then(self, other: EffectSeq) -> EffectSeq {
        match (&self, &other) {
            (EffectSeq::Empty, _) => other,
            (_, EffectSeq::Empty) => self,
            _ => EffectSeq::Seq(Box::new(self), Box::new(other)),
        }
    }

    pub fn single(effect: Effect) -> EffectSeq {
        EffectSeq::Single(effect)
    }

    pub fn branch(self, other: EffectSeq) -> EffectSeq {
        EffectSeq::Branch(Box::new(self), Box::new(other))
    }

    // Flatten to a Vec<Effect> by taking the union of all branches.
    pub fn flatten(&self) -> Vec<Effect> {
        match self {
            EffectSeq::Empty => vec![],
            EffectSeq::Single(e) => vec![e.clone()],
            EffectSeq::Seq(e1, e2) => {
                let mut v = e1.flatten();
                v.extend(e2.flatten());
                v
            }
            EffectSeq::Branch(e1, e2) => {
                let mut v = e1.flatten();
                v.extend(e2.flatten());
                v
            }
        }
    }

    pub fn paths(&self) -> Vec<Vec<Effect>> {
        match self {
            EffectSeq::Empty => vec![vec![]],
            EffectSeq::Single(e) => vec![vec![e.clone()]],
            EffectSeq::Seq(e1, e2) => {
                let paths1 = e1.paths();
                let paths2 = e2.paths();
                paths1.iter()
                    .flat_map(|p1| paths2.iter().map(move |p2| {
                        let mut p = p1.clone();
                        p.extend(p2.clone());
                        p
                    }))
                    .collect()
            }
            EffectSeq::Branch(e1, e2) => {
                let mut paths = e1.paths();
                paths.extend(e2.paths());
                paths
            }
        }
    }
}


pub type ThreadEffects = EffectSeq;

pub type EffectBar = Vec<EffectSeq>;
