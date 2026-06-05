use crate::types::{Effect, EffectBar, EffectSeq, EffectKind};
use crate::ast::Region;
use crate::error::TauRelaxError;

use z3::{Context,Config,Solver,SatResult};
use z3::ast::{Int, Bool, Ast};
use std::collections::HashMap;


pub struct ConstraintDebugger {
    pub enabled: bool,
}

impl ConstraintDebugger {
    pub fn new(enabled: bool) -> Self {
        ConstraintDebugger { enabled }
    }

    pub fn print_events(&self, events: &[(usize, &Effect)]) {
        if !self.enabled { return; }
        println!("\n=== Events ===");
        for (i, (tid, eff)) in events.iter().enumerate() {
            println!("  [{:>2}] thread={} {:?}^{} index={}",
                i, tid, eff.kind, eff.region.0, eff.index);
        }
    }

    pub fn print_po_edges(&self, events: &[(usize, &Effect)]) {
        if !self.enabled { return; }
        println!("\n=== Program Order Edges ===");
        for i in 0..events.len() {
            for j in 0..events.len() {
                if i == j { continue; }
                let (tid_i, eff_i) = events[i];
                let (tid_j, _) = events[j];
                let (_, eff_j) = events[j];
                if tid_i == tid_j && eff_i.index < eff_j.index {
                    println!("  [{i}] -> [{j}]  (po: thread {tid_i})");
                }
                if tid_i == 0 && tid_j != 0 {
                    println!("  [{i}] -> [{j}]  (preamble before thread {tid_j})");
                }
            }
        }
    }

    pub fn print_grf_candidates(
        &self,
        events: &[(usize, &Effect)],
        candidates: &HashMap<usize, Vec<usize>>,
    ) {
        if !self.enabled { return; }
        println!("\n=== Reads-From Candidates ===");
        for (read_i, writers) in candidates {
            let (_, eff_r) = events[*read_i];
            print!("  [{read_i}] {:?}^{} can read from: ", eff_r.kind, eff_r.region.0);
            if writers.is_empty() {
                println!("∅  (no valid writers — safe(hb) will fail)");
            } else {
                let strs: Vec<String> = writers.iter().map(|&w| {
                    let (_, eff_w) = events[w];
                    format!("[{w}] {:?}^{}", eff_w.kind, eff_w.region.0)
                }).collect();
                println!("{{{}}}", strs.join(", "));
            }
        }
    }

    pub fn print_liveness(
        &self,
        events: &[(usize, &Effect)],
        blocking: &HashMap<usize, Vec<usize>>,
    ) {
        if !self.enabled { return; }
        println!("\n=== Liveness ===");
        for i in 0..events.len() {
            let (_, eff) = events[i];
            match blocking.get(&i) {
                None => {
                    println!("  [{i}] {:?}^{}: unconditionally live",
                        eff.kind, eff.region.0);
                }
                Some(b) if b.is_empty() => {
                    println!("  [{i}] {:?}^{}: unconditionally live",
                        eff.kind, eff.region.0);
                }
                Some(blockers) => {
                    let strs: Vec<String> = blockers.iter()
                        .map(|b| format!("[{b}] resolved"))
                        .collect();
                    println!("  [{i}] {:?}^{}: live iff {}",
                        eff.kind, eff.region.0, strs.join(" ∧ "));
                }
            }
        }
    }

    pub fn print_violation_clauses(
        &self,
        events: &[(usize, &Effect)],
        clauses: &[(usize, usize)],
    ) {
        if !self.enabled { return; }
        println!("\n=== Safety Violation Clauses (negation of safe(hb)) ===");
        if clauses.is_empty() {
            println!("  (no free events — trivially safe)");
            return;
        }
        for (free_i, other_i) in clauses {
            let (_, eff_f) = events[*free_i];
            let (_, eff_o) = events[*other_i];
            println!(
                "  live[{free_i}] ∧ live[{other_i}] ∧ ¬(ts[{other_i}] < ts[{free_i}])"
            );
            println!(
                "     (free {:?}^{} not after {:?}^{})",
                eff_f.kind, eff_f.region.0,
                eff_o.kind, eff_o.region.0,
            );
        }
    }

    pub fn print_z3_state(&self, solver: &Solver) {
        if !self.enabled { return; }
        println!("\n=== Z3 Solver Assertions ===");
        println!("{}", solver);
    }

    pub fn print_result(
    &self,
    result: &SatResult,
    _events: &[(usize, &Effect)],
    _timestamps: &[Int<'_>],
    ) {
        if !self.enabled { return; }
        match result {
            SatResult::Unsat => println!("\n=== Result: UNSAT (safe) ==="),
            SatResult::Sat   => println!("\n=== Result: SAT (violation found) ==="),
            SatResult::Unknown => println!("\n=== Result: UNKNOWN ==="),
        }
    }
}


// Check safety(M_SC, Φ̄, Σ): 
// For every well-formed reads-from function grf that is consistent with M_SC, safe(hb) holds
// Try to find a grf under M_SC such that safe(hb) fails - if we can't (Unsat) then the program is safe
pub fn check_safety_sc(
    preamble_effects: &EffectSeq,
    thread_effects: &EffectBar,
    debug: bool,
) -> Result<(), TauRelaxError> {
    let dbg = ConstraintDebugger::new(debug);
    let preamble_paths = preamble_effects.paths();
    let thread_paths: Vec<Vec<Vec<Effect>>> = thread_effects
        .iter()
        .map(|phi| phi.paths())
        .collect();

    // check can create branching paths of effect sequences so we enumerate each path
    for preamble_path in &preamble_paths {
        for thread_combo in cartesian_product(&thread_paths) {
            if dbg.enabled {
                println!("\nChecking path combination");
            }
            check_path_combination(preamble_path, &thread_combo, &dbg)?;
        }
    }
    Ok(())
}

// check safety for every combination of paths across threads. this enumerates the combinations 
fn cartesian_product(paths: &[Vec<Vec<Effect>>]) -> Vec<Vec<Vec<Effect>>> {
    if paths.is_empty() { return vec![vec![]]; }
    let first = &paths[0];
    let rest = cartesian_product(&paths[1..]);
    first.iter().flat_map(|path| {
        rest.iter().map(move |combo| {
            let mut result = vec![path.clone()];
            result.extend(combo.clone());
            result
        })
    }).collect()
}

fn check_path_combination(
    preamble: &[Effect],
    thread_paths: &[Vec<Effect>],
    dbg: &ConstraintDebugger,
) -> Result<(), TauRelaxError> {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    // collect events. preamble effects are thread 0. 
    let mut events: Vec<(usize, &Effect)> = Vec::new();
    for e in preamble { events.push((0, e)); }
    for (tid, path) in thread_paths.iter().enumerate() {
        for e in path { events.push((tid + 1, e)); }
    }
    let n = events.len();
    if n == 0 { return Ok(()); }

    dbg.print_events(&events);

    let timestamps: Vec<Int<'_>> = (0..n)
        .map(|i| Int::new_const(&ctx, format!("ts_{}", i)))
        .collect();

    for ts in &timestamps {
        solver.assert(&ts.ge(&Int::from_i64(&ctx, 0)));
    }
    for i in 0..n {
        for j in (i + 1)..n {
            solver.assert(&timestamps[i]._eq(&timestamps[j]).not());
        }
    }

    // program order
    dbg.print_po_edges(&events);
    for i in 0..n {
        for j in 0..n {
            if i == j { continue; }
            let (tid_i, eff_i) = events[i];
            let (tid_j, eff_j) = events[j];
            if tid_i == tid_j && eff_i.index < eff_j.index {
                solver.assert(&timestamps[i].lt(&timestamps[j]));
            }
            if tid_i == 0 && tid_j != 0 {
                solver.assert(&timestamps[i].lt(&timestamps[j]));
            }
        }
    }

    // grf variables and candidates
    // For each Read or Wait event i, we create a Z3 integer variable grf_i. 
    // This variable represents which event i reads from. its value will be the index of the write event that i observes. 
    // a Read can read from a Write or New on the same region. 
    // a Wait can only read from a Flag on the same region
    let mut grf: HashMap<usize, Int<'_>> = HashMap::new();
    let mut grf_candidates: HashMap<usize, Vec<usize>> = HashMap::new();
    for i in 0..n {
        let (_, eff_i) = events[i];
        if !matches!(eff_i.kind, EffectKind::Read | EffectKind::Wait) { continue; }
        grf.insert(i, Int::new_const(&ctx, format!("grf_{}", i)));
        let candidates: Vec<usize> = (0..n).filter(|&j| {
            let (_, eff_j) = events[j];
            let right_kind = match eff_i.kind {
                EffectKind::Read => matches!(eff_j.kind, EffectKind::Write | EffectKind::New),
                EffectKind::Wait => eff_j.kind == EffectKind::Flag,
                _ => false,
            };
            right_kind && eff_j.region == eff_i.region
        }).collect();
        grf_candidates.insert(i, candidates);
    }
    dbg.print_grf_candidates(&events, &grf_candidates);

    // liveness : an event is live if every wait that precedes it in program order is resolved
 
    let mut resolved: HashMap<usize, Bool<'_>> = HashMap::new();
    for i in 0..n {
        let (_, eff_i) = events[i];
        if eff_i.kind != EffectKind::Wait { continue; }
        let grf_var = &grf[&i];
        let candidates = &grf_candidates[&i];
        let cands_bool: Vec<Bool<'_>> = candidates.iter()
            .map(|&j| grf_var._eq(&Int::from_i64(&ctx, j as i64)))
            .collect();
        let is_resolved = if cands_bool.is_empty() {
            Bool::from_bool(&ctx, false)
        } else {
            Bool::or(&ctx, &cands_bool.iter().collect::<Vec<_>>())
        };
        resolved.insert(i, is_resolved);
    }

    let mut blocking: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut live: HashMap<usize, Bool<'_>> = HashMap::new();
    for i in 0..n {
        let (tid_i, eff_i) = events[i];
        let blockers: Vec<usize> = (0..n).filter(|&j| {
            let (tid_j, eff_j) = events[j];
            tid_j == tid_i
                && eff_j.kind == EffectKind::Wait
                && eff_j.index < eff_i.index
        }).collect();
        let is_live = if blockers.is_empty() {
            Bool::from_bool(&ctx, true)
        } else {
            let conds: Vec<Bool> = blockers.iter()
                .map(|b| resolved[b].clone())
                .collect();
            Bool::and(&ctx, &conds.iter().collect::<Vec<_>>())
        };
        blocking.insert(i, blockers);
        live.insert(i, is_live);
    }
    dbg.print_liveness(&events, &blocking);

    // reads-from constraints
    for i in 0..n {
        let (_, eff_i) = events[i];
        if !matches!(eff_i.kind, EffectKind::Read | EffectKind::Wait) { continue; }
        let grf_var = &grf[&i];
        let candidates = &grf_candidates[&i];
        let valid: Vec<Bool<'_>> = candidates.iter().map(|&j| {
            let points_to:   Bool<'_> = grf_var._eq(&Int::from_i64(&ctx, j as i64));
            let writer_live: Bool<'_> = live[&j].clone();
            let before:      Bool<'_> = timestamps[j].lt(&timestamps[i]);
            Bool::and(&ctx, &[&points_to, &writer_live, &before])
        }).collect();
        let has_writer = if valid.is_empty() {
            Bool::from_bool(&ctx, false)
        } else {
            Bool::or(&ctx, &valid.iter().collect::<Vec<_>>())
        };
        solver.assert(&live[&i].clone().implies(&has_writer));
    }

    // safety violation
    let mut violation_pairs: Vec<(usize, usize)> = Vec::new();
    let mut violation_clauses: Vec<Bool<'_>> = Vec::new();
    for i in 0..n {
        let (_, eff_i) = events[i];
        if eff_i.kind != EffectKind::Free { continue; }
        for j in 0..n {
            if i == j { continue; }
            let (_, eff_j) = events[j];
            if eff_j.region != eff_i.region { continue; }
            violation_pairs.push((i, j));
            let free_live  = live[&i].clone();
            let other_live = live[&j].clone();
            let not_before = timestamps[j].lt(&timestamps[i]).not();
            violation_clauses.push(
                Bool::and(&ctx, &[&free_live, &other_live, &not_before])
            );
        }
    }
    dbg.print_violation_clauses(&events, &violation_pairs);

    if violation_clauses.is_empty() {
        return Ok(());
    }
    solver.assert(&Bool::or(
        &ctx,
        &violation_clauses.iter().collect::<Vec<_>>()
    ));

    dbg.print_z3_state(&solver);

    let result = solver.check();
    dbg.print_result(&result, &events, &timestamps);

    match result {
        SatResult::Unsat => Ok(()),
        SatResult::Sat => {
            let model = solver.get_model().unwrap();
            let mut execution: Vec<(i64, String)> = events.iter().enumerate()
                .map(|(i, (tid, eff))| {
                    let ts = model.eval(&timestamps[i], true)
                        .and_then(|v| v.as_i64())
                        .unwrap_or(-1);
                    (ts, format!("{:?}^{} (thread {}, index {})",
                        eff.kind, eff.region.0, tid, eff.index))
                })
                .collect();
            execution.sort_by_key(|(ts, _)| *ts);
            let trace = execution.iter()
                .map(|(ts, desc)| format!("  t={}: {}", ts, desc))
                .collect::<Vec<_>>()
                .join("\n");
            Err(TauRelaxError::SafetyError {
                message: format!(
                    "safety violation — execution exists where a region is accessed after free:\n{}",
                    trace
                )
            })
        }
        SatResult::Unknown => Err(TauRelaxError::SafetyError {
            message: "Z3 returned unknown".to_string()
        })
    }
}
