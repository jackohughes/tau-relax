use crate::types::{Ty, TypeWithPlace};
use crate::ast::Region;
use crate::error::TauRelaxError;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Substitution {
    pub map: HashMap<String, Ty>,
    pub regions: HashMap<usize, Region>,
}

impl Substitution {
    pub fn new() -> Self {
        Substitution { map: HashMap::new(), regions: HashMap::new() }
    }

    pub fn lookup(&self, var: &str) -> Option<&Ty> {
        self.map.get(var)
    }

    pub fn bind(&mut self, var: String, ty: Ty) {
        self.map.insert(var, ty);
    }

    pub fn bind_region(&mut self, var: usize, region: Region) {
        self.regions.insert(var, region);
    }

    pub fn apply(&self, ty: &Ty) -> Ty {
        match ty {
            Ty::Var(x) => match self.lookup(x) {
                Some(t) => self.apply(t), // follow the chain
                None => ty.clone(),
            },
            Ty::Ref(inner) => Ty::Ref(Box::new(self.apply(inner))),
            Ty::Int | Ty::Unit | Ty::Flag => ty.clone(),
        }
    }

    pub fn apply_region(&self, r: &Region) -> Region {
        match r {
            Region::Var(n) => match self.regions.get(n) {
                Some(r2) => self.apply_region(r2), // follow the chain
                None => r.clone(),
            },
            Region::Named(_) => r.clone(),
        }
    }

    pub fn apply_twp(&self, twp: &TypeWithPlace) -> TypeWithPlace {
        TypeWithPlace {
            ty: self.apply(&twp.ty),
            region: self.apply_region(&twp.region),
        }
    }
}

pub fn unify(t1: &Ty, t2: &Ty, subst: &mut Substitution) -> Result<(), TauRelaxError> {
    let t1 = subst.apply(t1);
    let t2 = subst.apply(t2);

    match (&t1, &t2) {
        (Ty::Int, Ty::Int) => Ok(()),
        (Ty::Unit, Ty::Unit) => Ok(()),
        (Ty::Flag, Ty::Flag) => Ok(()),

        (Ty::Ref(a), Ty::Ref(b)) => unify(a, b, subst),

        (Ty::Var(x), t) => {
            if occurs(x, t) {
                Err(TauRelaxError::TypeError {
                    message: format!("infinite type: {} occurs in {:?}", x, t),
                })
            } else {
                subst.bind(x.clone(), t.clone());
                Ok(())
            }
        }

        (t, Ty::Var(x)) => {
            if occurs(x, t) {
                Err(TauRelaxError::TypeError {
                    message: format!("infinite type: {} occurs in {:?}", x, t),
                })
            } else {
                subst.bind(x.clone(), t.clone());
                Ok(())
            }
        }

        _ => Err(TauRelaxError::TypeError {
            message: format!("cannot unify {:?} with {:?}", t1, t2),
        }),
    }
}

/// Regions unify structurally: two concrete regions must be the same, and a
/// variable is bound to whatever it meets. There is no occurs check, regions
/// having no internal structure.
pub fn unify_region(
    r1: &Region,
    r2: &Region,
    subst: &mut Substitution,
) -> Result<(), TauRelaxError> {
    let r1 = subst.apply_region(r1);
    let r2 = subst.apply_region(r2);

    match (&r1, &r2) {
        (Region::Named(a), Region::Named(b)) if a == b => Ok(()),
        (Region::Var(n), r) => {
            subst.bind_region(*n, r.clone());
            Ok(())
        }
        (r, Region::Var(n)) => {
            subst.bind_region(*n, r.clone());
            Ok(())
        }
        _ => Err(TauRelaxError::TypeError {
            message: format!(
                "cannot unify region {} with region {}",
                r1.name(),
                r2.name()
            ),
        }),
    }
}

fn occurs(x: &str, ty: &Ty) -> bool {
    match ty {
        Ty::Var(y) => x == y,
        Ty::Ref(inner) => occurs(x, inner),
        Ty::Int | Ty::Unit | Ty::Flag => false,
    }
}