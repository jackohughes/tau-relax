//! The `safety(M, Phi_bar, H)` premise of t-topLevel, discharged with Z3.
//!
//! The paper states the condition as
//!
//! ```text
//!   safety(M, Phi_bar, H) = forall grf. wf_grf(grf) /\ M(grf) => safe(hb_M)
//!   M(grf)                = exists co. wf_co(co)
//!                                   /\ acyclic(<_M|_L U grf U co U rb)
//!   hb_M                  = (grf U <_M|_L)^+
//!   graph_erroneous(hb_M) = exists e in L|_rho, free^rho in L.
//!                             e /= free^rho /\ (e, free^rho) not in hb_M^?
//! ```
//!
//! which we can rewrite without quantifier alternation:
//!
//! ```text
//!   exists realisation, grf, co.
//!     wf_grf(grf) /\ wf_co(co) /\ acyclic(...) /\ graph_erroneous(hb_M)
//! ```
//!
//! and that is just plain satisfiability query over a finite domain. `Unsat`
//! means the program is safe; `Sat` hands back a counterexample execution.

use crate::error::TauRelaxError;
use crate::types::{Choice, Effect, EffectBar, EffectKind, EffectSeq};

use z3::ast::{Ast, Bool, Int};
use z3::{Config, Context, SatResult, Solver};

/// The memory model, which enters only by choosing which program-order edges
/// it preserves. TSO would add a variant here and a case in `po_m`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Model {
    Sc,
}

impl Model {
    pub const SC: Model = Model::Sc;

    fn name(&self) -> &'static str {
        match self {
            Model::Sc => "SC",
        }
    }
}

/// An event `t : a`: an action tagged with the thread that performs it, and
/// its position in that thread's realised sequence. Thread 0 is the preamble.
struct Ev<'a> {
    tid: usize,
    pos: usize,
    eff: &'a Effect,
}

impl<'a> Ev<'a> {
    fn show(&self) -> String {
        format!(
            "{:?}^{} (thread {}, index {})",
            self.eff.kind,
            self.eff.region_name(),
            self.tid,
            self.eff.index
        )
    }
}

/// Can this kind supply a value to a reader?
fn is_value_supplying(k: &EffectKind) -> bool {
    matches!(k, EffectKind::Write | EffectKind::New | EffectKind::Flag)
}

/// The events `wf_co` totally orders per region.
fn is_co_event(k: &EffectKind) -> bool {
    matches!(
        k,
        EffectKind::Write | EffectKind::New | EffectKind::Flag | EffectKind::Free
    )
}

fn is_reader(k: &EffectKind) -> bool {
    matches!(k, EffectKind::Read | EffectKind::Wait)
}

fn same_region(a: &Effect, b: &Effect) -> bool {
    match (&a.region, &b.region) {
        (Some(x), Some(y)) => x == y,
        _ => false,
    }
}

fn may_read_from(reader: &Effect, writer: &Effect) -> bool {
    if !same_region(reader, writer) {
        return false;
    }
    match reader.kind {
        EffectKind::Wait => writer.kind == EffectKind::Flag,
        EffectKind::Read => is_value_supplying(&writer.kind),
        _ => false,
    }
}

fn po_m(model: Model, a: &Ev, b: &Ev) -> bool {
    let po = (a.tid == b.tid && a.pos < b.pos) || (a.tid == 0 && b.tid != 0);
    match model {
        Model::Sc => po,
    }
}

pub struct ConstraintDebugger {
    pub enabled: bool,
}

impl ConstraintDebugger {
    pub fn new(enabled: bool) -> Self {
        ConstraintDebugger { enabled }
    }

    fn events(&self, events: &[Ev]) {
        if !self.enabled {
            return;
        }
        println!("\n=== Events ===");
        for (i, e) in events.iter().enumerate() {
            println!("  [{:>2}] {}", i, e.show());
        }
    }

    fn po_edges(&self, model: Model, events: &[Ev]) {
        if !self.enabled {
            return;
        }
        println!("\n=== Program Order Edges (<_{}) ===", model.name());
        for i in 0..events.len() {
            for j in 0..events.len() {
                if i != j && po_m(model, &events[i], &events[j]) {
                    println!("  [{i}] -> [{j}]");
                }
            }
        }
    }

    fn grf_candidates(&self, events: &[Ev], cands: &[(usize, Vec<usize>)]) {
        if !self.enabled {
            return;
        }
        println!("\n=== Reads-From Candidates ===");
        for (r, writers) in cands {
            print!("  [{r}] {} can read from: ", events[*r].show());
            if writers.is_empty() {
                println!("(none)");
            } else {
                let s: Vec<String> = writers.iter().map(|w| format!("[{w}]")).collect();
                println!("{}", s.join(", "));
            }
        }
    }

    fn choices(&self, events: &[Ev], choices: &[(usize, bool)]) {
        if !self.enabled {
            return;
        }
        println!("\n=== Branch Commitments (value_constraint) ===");
        if choices.is_empty() {
            println!("  (none)");
        }
        for (g, took_then) in choices {
            println!(
                "  [{g}] {} took {} => source must be {}",
                events[*g].show(),
                if *took_then { "then" } else { "else" },
                if *took_then {
                    "a Flag"
                } else {
                    "a New or Write"
                }
            );
        }
    }
}

pub fn check_safety(
    model: Model,
    preamble_effects: &EffectSeq,
    thread_effects: &EffectBar,
    debug: bool,
) -> Result<(), TauRelaxError> {
    let dbg = ConstraintDebugger::new(debug);
    let preamble_rs = preamble_effects.realisations();
    let thread_rs: Vec<Vec<(Vec<Effect>, Vec<Choice>)>> = thread_effects
        .iter()
        .map(|phi| phi.realisations())
        .collect();

    let combos = cartesian_product(&thread_rs);
    let total = preamble_rs.len() * combos.len();
    if dbg.enabled {
        println!("\nsafety({}, ...): {} realisation(s)", model.name(), total);
    }

    for preamble in &preamble_rs {
        for combo in &combos {
            check_realisation(model, preamble, combo, &dbg)?;
        }
    }
    println!("safety check ok ({})", model.name());
    Ok(())
}

fn cartesian_product<T: Clone>(choices: &[Vec<T>]) -> Vec<Vec<T>> {
    if choices.is_empty() {
        return vec![vec![]];
    }
    let rest = cartesian_product(&choices[1..]);
    choices[0]
        .iter()
        .flat_map(|head| {
            rest.iter().map(move |tail| {
                let mut v = vec![head.clone()];
                v.extend(tail.iter().cloned());
                v
            })
        })
        .collect()
}

fn check_realisation(
    model: Model,
    preamble: &(Vec<Effect>, Vec<Choice>),
    threads: &[(Vec<Effect>, Vec<Choice>)],
    dbg: &ConstraintDebugger,
) -> Result<(), TauRelaxError> {
    // --- events -----------------------------------------------------------
    // The preamble is thread 0; program thread `t` is thread `t + 1`. An
    // event's position in its own realised path is its position in `<`.
    let mut events: Vec<Ev> = Vec::new();
    for (pos, eff) in preamble.0.iter().enumerate() {
        events.push(Ev { tid: 0, pos, eff });
    }
    for (t, (path, _)) in threads.iter().enumerate() {
        for (pos, eff) in path.iter().enumerate() {
            events.push(Ev {
                tid: t + 1,
                pos,
                eff,
            });
        }
    }
    let n = events.len();
    if n == 0 {
        return Ok(());
    }

    // Branch commitments, resolved from (thread, effect index) to event index.
    let mut choices: Vec<(usize, bool)> = Vec::new();
    for (tid, (_, cs)) in std::iter::once(&(Vec::new(), preamble.1.clone()))
        .chain(threads.iter().map(|x| x))
        .enumerate()
    {
        for c in cs {
            if let Some(i) = events
                .iter()
                .position(|e| e.tid == tid && e.eff.index == c.guard_index)
            {
                choices.push((i, c.took_then));
            }
        }
    }

    dbg.events(&events);
    dbg.po_edges(model, &events);

    // --- solver -----------------------------------------------------------
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    let tt = Bool::from_bool(&ctx, true);

    // `ts`: a linear extension of `<_M|_L U grf U co U rb`
    let ts: Vec<Int> = (0..n)
        .map(|i| Int::new_const(&ctx, format!("ts_{i}")))
        .collect();
    let zero = Int::from_i64(&ctx, 0);
    for t in &ts {
        solver.assert(&t.ge(&zero));
    }
    for i in 0..n {
        for j in (i + 1)..n {
            solver.assert(&ts[i]._eq(&ts[j]).not());
        }
    }

    // `grf`: one boolean per (reader, admissible writer) pair.
    let mut grf: Vec<(usize, Vec<(usize, Bool)>)> = Vec::new();
    for r in 0..n {
        if !is_reader(&events[r].eff.kind) {
            continue;
        }
        let cands: Vec<(usize, Bool)> = (0..n)
            .filter(|&w| w != r && may_read_from(events[r].eff, events[w].eff))
            .map(|w| (w, Bool::new_const(&ctx, format!("grf_{r}_{w}"))))
            .collect();
        grf.push((r, cands));
    }
    dbg.grf_candidates(
        &events,
        &grf.iter()
            .map(|(r, c)| (*r, c.iter().map(|(w, _)| *w).collect()))
            .collect::<Vec<_>>(),
    );

    let grf_of = |r: usize| -> &[(usize, Bool)] {
        grf.iter()
            .find(|(x, _)| *x == r)
            .map(|(_, c)| c.as_slice())
            .unwrap_or(&[])
    };

    // grf is a function: at most one source per reader.
    for (_, cands) in &grf {
        for a in 0..cands.len() {
            for b in (a + 1)..cands.len() {
                solver.assert(&Bool::and(&ctx, &[&cands[a].1, &cands[b].1]).not());
            }
        }
    }

    // `resolved`: a wait is resolved when grf gives it a source.
    let resolved: Vec<Bool> = (0..n)
        .map(|i| {
            let cands = grf_of(i);
            if cands.is_empty() {
                Bool::from_bool(&ctx, false)
            } else {
                let refs: Vec<&Bool> = cands.iter().map(|(_, b)| b).collect();
                Bool::or(&ctx, &refs)
            }
        })
        .collect();

    // `L`: an event is live when every wait preceding it in `<` is resolved.
    let live: Vec<Bool> = (0..n)
        .map(|i| {
            let blockers: Vec<&Bool> = (0..n)
                .filter(|&l| {
                    events[l].eff.kind == EffectKind::Wait && po_m(model, &events[l], &events[i])
                })
                .map(|l| &resolved[l])
                .collect();
            if blockers.is_empty() {
                tt.clone()
            } else {
                Bool::and(&ctx, &blockers)
            }
        })
        .collect();

    // wf_grf: grf covers every live reader, and relates live events only.
    for (r, cands) in &grf {
        solver.assert(&live[*r].implies(&resolved[*r]));
        for (w, b) in cands {
            solver.assert(&b.implies(&Bool::and(&ctx, &[&live[*r], &live[*w]])));
            // grf is one of the edges the acyclicity check ranges over.
            solver.assert(&b.implies(&ts[*w].lt(&ts[*r])));
        }
    }

    // `<_M|_L` is likewise one of those edges.
    for i in 0..n {
        for j in 0..n {
            if i != j && po_m(model, &events[i], &events[j]) {
                let both = Bool::and(&ctx, &[&live[i], &live[j]]);
                solver.assert(&both.implies(&ts[i].lt(&ts[j])));
            }
        }
    }

    for (r, cands) in &grf {
        for (w, b) in cands {
            for w2 in 0..n {
                if w2 == *w || w2 == *r {
                    continue;
                }
                if !is_co_event(&events[w2].eff.kind)
                    || !same_region(events[*w].eff, events[w2].eff)
                {
                    continue;
                }
                let ante = Bool::and(&ctx, &[b, &live[w2], &ts[*w].lt(&ts[w2])]);
                solver.assert(&ante.implies(&ts[*r].lt(&ts[w2])));
            }
        }
    }

    // `value_constraint`: a branch may only be taken if the guard read could
    // have observed the value that selects it. A `flag` event sets the
    // location, a `new` or `write` leaves it unset, so the then-branch
    // requires a flag source and the else-branch forbids one.
    dbg.choices(&events, &choices);
    for (g, took_then) in &choices {
        let flags: Vec<&Bool> = grf_of(*g)
            .iter()
            .filter(|(w, _)| events[*w].eff.kind == EffectKind::Flag)
            .map(|(_, b)| b)
            .collect();
        if *took_then {
            let any_flag = if flags.is_empty() {
                Bool::from_bool(&ctx, false)
            } else {
                Bool::or(&ctx, &flags)
            };
            solver.assert(&live[*g].implies(&any_flag));
        } else {
            for b in flags {
                solver.assert(&live[*g].implies(&b.not()));
            }
        }
    }

    // --- graph_erroneous, one query per free event -------------------------
    for f in 0..n {
        if events[f].eff.kind != EffectKind::Free {
            continue;
        }
        let rho = match &events[f].eff.region {
            Some(r) => r.clone(),
            None => continue,
        };
        let others: Vec<usize> = (0..n)
            .filter(|&e| {
                e != f
                    && events[e]
                        .eff
                        .region
                        .as_ref()
                        .map(|r| *r == rho)
                        .unwrap_or(false)
            })
            .collect();
        if others.is_empty() {
            continue;
        }

        solver.push();

        let u: Vec<Bool> = (0..n)
            .map(|i| Bool::new_const(&ctx, format!("u_{i}")))
            .collect();

        solver.assert(&live[f]);
        solver.assert(&u[f].not());

        for i in 0..n {
            for j in 0..n {
                if i != j && po_m(model, &events[i], &events[j]) {
                    let ante = Bool::and(&ctx, &[&live[i], &live[j], &u[i]]);
                    solver.assert(&ante.implies(&u[j]));
                }
            }
        }
        for (r, cands) in &grf {
            for (w, b) in cands {
                solver.assert(&Bool::and(&ctx, &[b, &u[*w]]).implies(&u[*r]));
            }
        }

        let witnesses: Vec<Bool> = others
            .iter()
            .map(|&e| Bool::and(&ctx, &[&live[e], &u[e]]))
            .collect();
        let refs: Vec<&Bool> = witnesses.iter().collect();
        solver.assert(&Bool::or(&ctx, &refs));

        let result = solver.check();
        match result {
            SatResult::Unsat => {
                solver.pop(1);
            }
            SatResult::Sat => {
                let model_z3 = solver.get_model().unwrap();
                let culprit = others.iter().copied().find(|&e| {
                    model_z3
                        .eval(&Bool::and(&ctx, &[&live[e], &u[e]]), true)
                        .and_then(|v| v.as_bool())
                        .unwrap_or(false)
                });
                let mut trace: Vec<(i64, String)> = (0..n)
                    .filter(|&i| {
                        model_z3
                            .eval(&live[i], true)
                            .and_then(|v| v.as_bool())
                            .unwrap_or(true)
                    })
                    .map(|i| {
                        let t = model_z3
                            .eval(&ts[i], true)
                            .and_then(|v| v.as_i64())
                            .unwrap_or(-1);
                        (t, events[i].show())
                    })
                    .collect();
                trace.sort_by_key(|(t, _)| *t);
                let trace = trace
                    .iter()
                    .map(|(t, d)| format!("  t={t}: {d}"))
                    .collect::<Vec<_>>()
                    .join("\n");
                let culprit = culprit
                    .map(|e| events[e].show())
                    .unwrap_or_else(|| "<unknown>".to_string());
                solver.pop(1);
                return Err(TauRelaxError::SafetyError {
                    message: format!(
                        "safety({}) violated: {} is not ordered before {}, \
                         so an execution exists in which region {} is used \
                         after it is freed.\nWitness execution:\n{}",
                        model.name(),
                        culprit,
                        events[f].show(),
                        rho.name(),
                        trace
                    ),
                });
            }
            SatResult::Unknown => {
                solver.pop(1);
                return Err(TauRelaxError::SafetyError {
                    message: format!("Z3 returned unknown while checking {}", events[f].show()),
                });
            }
        }
    }

    Ok(())
}
