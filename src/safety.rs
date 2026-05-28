use crate::types::{Effect, EffectBar, EffectList};
use crate::ast::Region;
use crate::error::TauRelaxError;

use z3::{Context,Config,Solver};
use z3::ast::{Int, Bool, Ast};


struct Event<'ctxt> {
    id: usize,
    thread: usize,
    effect: Effect,
    timestamp: Int<'ctxt>,
}


// Check safety(M_SC, Φ̄, Σ) 
pub fn check_safety_sc(
    preamble_effects: &EffectList, 
    thread_effects: &EffectBar,
) -> Result<(), TauRelaxError> {
    let cfg = z3::Config::new();
    let ctxt = Context::new(&cfg);
    let solver = Solver::new(&ctxt);


    // flatten effects
    let mut events: Vec<Event> = Vec::new();
    let mut id = 0;
    for (thread, phi) in thread_effects.iter().enumerate() {
        for effect in phi.iter() {
            let timestamp = Int::new_const(
                &ctxt,
                format!("ts_{}", id)
            );
            events.push(Event {
                id,
                thread,
                effect: effect.clone(),
                timestamp,
            });
            id += 1;
        }
    }
    // then assert program order, liveness, reads-from, coherence, acyclicty, and 
    // negation of safe(hb)
    todo!()
}