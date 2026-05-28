use crate::types::{Ty, TypeWithPlace};
use crate::error::TauRelaxError;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Substitution {
    pub map: HashMap<String, Ty>,
}

impl Substitution {
    pub fn new() -> Self { 
        Substitution { map: HashMap::new() }
    }

    pub fn lookup(&self, var : &str) -> Option<&Ty> {
        self.map.get(var)
    }

    pub fn bind(&mut self, var: String , ty: Ty){
        self.map.insert(var, ty);
    }

    pub fn apply(&self, ty: &Ty) -> Ty {
        match ty { 
            Ty::Var(x) => {
                match self.lookup(x) {
                    Some(t) => self.apply(t), // follow the chain and keep applying
                    None => ty.clone(),
                }
            }
            Ty::Ref(inner) => Ty::Ref(Box::new(self.apply(inner))), 
            Ty::Int | Ty::Unit | Ty::Flag => ty.clone(),
        }
    }

    pub fn apply_twp(&self, twp: &TypeWithPlace) -> TypeWithPlace {
        TypeWithPlace { 
            ty: self.apply(&twp.ty), 
            region: twp.region.clone(),
        }
    }
}

pub fn unify(
    t1: &Ty, 
    t2: &Ty,
    subst: &mut Substitution,
) -> Result<(), TauRelaxError>{
    let t1 = subst.apply(t1);
    let t2 = subst.apply(t2);

    match (&t1, &t2) {
        (Ty::Int, Ty::Int)   => Ok(()),
        (Ty::Unit, Ty::Unit) => Ok(()),
        (Ty::Flag, Ty::Flag) => Ok(()),

        (Ty::Ref(a), Ty::Ref(b)) => unify(a, b, subst), 

        (Ty::Var(x), t) => {
            if occurs(x, t) {
                Err(TauRelaxError::TypeError {
                    message: format!("infinite type: {} occurs in {:?}", x, t)
                })
            } else {
                subst.bind(x.clone(), t.clone());
                Ok(())
            }
        }

        (t, Ty::Var(x)) => {
            if occurs(x, t) {
                Err(TauRelaxError::TypeError {
                    message: format!("infinite type: {} occurs in {:?}", x, t)
                })
            } else { 
                subst.bind(x.clone(), t.clone());
                Ok(())
            }
        }

        // mismatch
        _ => Err(TauRelaxError::TypeError {
            message: format!("cannot unify {:?} with {:?}", t1, t2)
        })
    }
}

fn occurs(x: &str, ty: &Ty) -> bool {
    match ty { 
        Ty::Var(y) => x == y, 
        Ty::Ref(inner) => occurs(x, inner),
        Ty::Int | Ty::Unit | Ty::Flag => false,
    }
}
