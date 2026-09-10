use crate::types::{EffectBar, EffectSeq};
use crate::error::TauRelaxError;

pub fn check_safety_sc(
    _preamble_effects: &EffectSeq,
    _thread_effects: &EffectBar,
    _debug: bool,
) -> Result<(), TauRelaxError> {
    println!("safety check: SKIPPED");
    Ok(())
}