use crate::ast::Region;
use crate::types::{Effect, EffectKind, EffectSeq};
use crate::error::TauRelaxError;
use std::collections::BTreeSet;

pub type AliveSet = BTreeSet<Region>;

/// `A |- a ok => A'` for a single action.
fn step(alive: &AliveSet, eff: &Effect) -> Result<AliveSet, TauRelaxError> {
    // eok-fence: a fence has no region and no lifecycle obligation
    if eff.kind == EffectKind::Fence {
        return Ok(alive.clone());
    }

    let region = eff.region.as_ref().ok_or_else(|| TauRelaxError::TypeError {
        message: format!("effect {:?} has no region", eff.kind),
    })?;

    match eff.kind {
        // eok-new: the region must not already be alive
        EffectKind::New => {
            if alive.contains(region) {
                return Err(TauRelaxError::TypeError {
                    message: format!(
                        "region {} is allocated twice in one thread", region.name()
                    ),
                });
            }
            let mut a = alive.clone();
            a.insert(region.clone());
            Ok(a)
        }
        // eok-free: the region must be alive, and ceases to be
        EffectKind::Free => {
            if !alive.contains(region) {
                return Err(TauRelaxError::TypeError {
                    message: format!(
                        "region {} is freed while not alive (double free, \
                         or freed before allocation)", region.name()
                    ),
                });
            }
            let mut a = alive.clone();
            a.remove(region);
            Ok(a)
        }
        // eok-use: every other action requires the region to be alive
        _ => {
            if !alive.contains(region) {
                return Err(TauRelaxError::TypeError {
                    message: format!(
                        "{:?} on region {} which is not alive (use before \
                         allocation, or use after free)", eff.kind, region.name()
                    ),
                });
            }
            Ok(alive.clone())
        }
    }
}

/// `A |- phi ok => A'` for an effect sequence.
pub fn check(alive: &AliveSet, seq: &EffectSeq) -> Result<AliveSet, TauRelaxError> {
    match seq {
        // eok-empty
        EffectSeq::Empty => Ok(alive.clone()),

        EffectSeq::Single(eff) => step(alive, eff),

        // eok-seq: thread the alive-set through
        EffectSeq::Seq(s1, s2) => {
            let a1 = check(alive, s1)?;
            check(&a1, s2)
        }

        // eok-branch: the guard read runs first (eok-use), then both branches
        // are checked against the *same* incoming alive-set, since either may
        // run, and the results are intersected — a region is assumable-alive
        // afterwards only if alive on both paths.
        EffectSeq::Branch { guard, then_, else_ } => {
            let alive = match guard {
                Some(g) => step(alive, g)?,
                None => alive.clone(),
            };
            let a1 = check(&alive, then_)?;
            let a2 = check(&alive, else_)?;
            Ok(a1.intersection(&a2).cloned().collect())
        }
    }
}

/// `effects_ok(phi)`: check from the initial alive-set.
pub fn effects_ok(initial: &AliveSet, seq: &EffectSeq) -> Result<(), TauRelaxError> {
    check(initial, seq).map(|_| ())
}