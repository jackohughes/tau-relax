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
    Check,
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
    pub region: Option<Region>,
    pub index: usize,
}

impl Effect {
    pub fn region_name(&self) -> String {
        match &self.region {
            Some(r) => r.name(),
            None => "-".to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum EffectSeq {
    Empty,
    Single(Effect),
    Seq(Box<EffectSeq>, Box<EffectSeq>),
    Branch {
        guard: Option<Effect>,
        then_: Box<EffectSeq>,
        else_: Box<EffectSeq>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Choice {
    pub guard_index: usize,
    pub took_then: bool,
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

    pub fn branch(self, guard: Option<Effect>, other: EffectSeq) -> EffectSeq {
        EffectSeq::Branch {
            guard,
            then_: Box::new(self),
            else_: Box::new(other),
        }
    }

    pub fn realisations(&self) -> Vec<(Vec<Effect>, Vec<Choice>)> {
        match self {
            EffectSeq::Empty => vec![(vec![], vec![])],
            EffectSeq::Single(e) => vec![(vec![e.clone()], vec![])],
            EffectSeq::Seq(s1, s2) => {
                let rs1 = s1.realisations();
                let rs2 = s2.realisations();
                rs1.iter()
                    .flat_map(|(p1, c1)| {
                        rs2.iter().map(move |(p2, c2)| {
                            let mut p = p1.clone();
                            p.extend(p2.iter().cloned());
                            let mut c = c1.clone();
                            c.extend(c2.iter().cloned());
                            (p, c)
                        })
                    })
                    .collect()
            }
            EffectSeq::Branch {
                guard,
                then_,
                else_,
            } => {
                let mut out = Vec::new();
                for (took_then, arm) in [(true, then_), (false, else_)] {
                    for (path, mut choices) in arm.realisations() {
                        let mut p = Vec::new();
                        if let Some(g) = guard {
                            p.push(g.clone());
                            choices.insert(
                                0,
                                Choice {
                                    guard_index: g.index,
                                    took_then,
                                },
                            );
                        }
                        p.extend(path);
                        out.push((p, choices));
                    }
                }
                out
            }
        }
    }
}

pub type ThreadEffects = EffectSeq;

pub type EffectBar = Vec<EffectSeq>;
