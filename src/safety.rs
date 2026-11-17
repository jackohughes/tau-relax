use crate::ast::Region;
use crate::error::TauRelaxError;
use crate::types::{Choice, Effect, EffectBar, EffectKind, EffectSeq};

use z3::ast::{Ast, Bool, Int};
use z3::{Config, Context, SatResult};

use crate::constraints::Constraints;
use crate::pretty::{Names, render_flat, render_query, sub, sup};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Model {
    Sc,
    Tso,
}

impl Model {
    pub const SC: Model = Model::Sc;

    fn name(&self) -> &'static str {
        match self {
            Model::Sc => "SC",
            Model::Tso => "TSO",
        }
    }

    pub fn parse(s: &str) -> Option<Model> {
        match s.to_ascii_lowercase().as_str() {
            "sc" => Some(Model::Sc),
            "tso" => Some(Model::Tso),
            _ => None,
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
    /// `Write\u{02B3}\u{2070}`: the action kind carrying its region as a superscript.
    fn kind_region(&self) -> String {
        format!("{:?}{}", self.eff.kind, sup(&self.eff.region_name()))
    }

    /// For listings, where there is room to name the thread and position.
    fn show(&self) -> String {
        format!(
            "{} (thread {}, index {})",
            self.kind_region(),
            self.tid,
            self.eff.index
        )
    }

    /// Terse form, for use inside a formula rather than in a listing.
    fn short(&self) -> String {
        format!(
            "{} t{}#{}",
            self.kind_region(),
            sub(&self.tid.to_string()),
            sub(&self.eff.index.to_string())
        )
    }
}

/// The kinds that supersede the value a read took, which is what `co` orders
/// among and what `rb` is built from. A `new` writes only the header.
fn is_writing(k: &EffectKind) -> bool {
    matches!(k, EffectKind::Write | EffectKind::Flag)
}

/// The events `wf_co` totally orders per region.
fn is_co_event(k: &EffectKind) -> bool {
    matches!(k, EffectKind::Write | EffectKind::Flag | EffectKind::Free)
}

fn is_reader(k: &EffectKind) -> bool {
    matches!(k, EffectKind::Read | EffectKind::Check | EffectKind::Wait)
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
        EffectKind::Check => is_writing(&writer.kind),
        EffectKind::Read => is_writing(&writer.kind) || writer.kind == EffectKind::New,
        _ => false,
    }
}

fn po(a: &Ev, b: &Ev) -> bool {
    (a.tid == b.tid && a.pos < b.pos) || (a.tid == 0 && b.tid != 0)
}

fn is_buffered(k: &EffectKind) -> bool {
    matches!(k, EffectKind::Write | EffectKind::Flag)
}

fn fence_between(events: &[Ev], a: &Ev, b: &Ev) -> bool {
    events.iter().any(|e| {
        e.tid == a.tid && e.pos > a.pos && e.pos < b.pos && e.eff.kind == EffectKind::Fence
    })
}

/// The targets a buffered write is not ordered before: the rules that act on
/// the store without waiting for the buffer, and a free of another region.
fn relaxed_target(a: &Ev, b: &Ev) -> bool {
    match b.eff.kind {
        EffectKind::Read | EffectKind::Check | EffectKind::Wait | EffectKind::New => true,
        EffectKind::Free => !same_region(a.eff, b.eff),
        _ => false,
    }
}

fn po_m(model: Model, events: &[Ev], i: usize, j: usize) -> bool {
    let (a, b) = (&events[i], &events[j]);
    if !po(a, b) {
        return false;
    }
    match model {
        Model::Sc => true,
        Model::Tso => {
            a.tid != b.tid
                || !is_buffered(&a.eff.kind)
                || !relaxed_target(a, b)
                || fence_between(events, a, b)
        }
    }
}

fn grf_m(model: Model, events: &[Ev], w: usize, r: usize) -> bool {
    match model {
        Model::Sc => true,
        Model::Tso => events[w].tid != events[r].tid,
    }
}

fn on_singular(singular: &std::collections::BTreeSet<Region>, e: &Ev) -> bool {
    match &e.eff.region {
        Some(r) => singular.contains(r),
        None => false,
    }
}

fn po_m_edges(model: Model, events: &[Ev]) -> Vec<(usize, usize)> {
    let n = events.len();
    let mut out = Vec::new();
    for i in 0..n {
        for j in 0..n {
            if i != j && po_m(model, events, i, j) {
                out.push((i, j));
            }
        }
    }
    out
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

    fn po_edges(&self, model: Model, events: &[Ev], preserved: &[(usize, usize)]) {
        if !self.enabled {
            return;
        }
        println!("\n=== Program Order Edges (<_{}) ===", model.name());
        for (i, j) in preserved {
            println!("  [{i}] -> [{j}]");
        }
        if model == Model::Sc {
            return;
        }
        println!(
            "\n=== Relaxed by {} (in < but not <_{}) ===",
            model.name(),
            model.name()
        );
        let mut any = false;
        for i in 0..events.len() {
            for j in 0..events.len() {
                if i != j && po(&events[i], &events[j]) && !preserved.contains(&(i, j)) {
                    any = true;
                    println!(
                        "  [{i}] -> [{j}]\t{} -> {}\t(thread {})",
                        events[i].kind_region(),
                        events[j].kind_region(),
                        events[i].tid
                    );
                }
            }
        }
        if !any {
            println!("  (none)");
        }
    }

    fn grf_m_pairs(&self, events: &[Ev], global: &[(usize, usize)]) {
        if !self.enabled {
            return;
        }
        println!("\n=== Global Reads-From Candidates (grf_M) ===");
        if global.is_empty() {
            println!("  (none)");
        }
        for (w, r) in global {
            println!(
                "  [{w}] {} -> [{r}] {}",
                events[*w].kind_region(),
                events[*r].kind_region()
            );
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
                if *took_then { "a Flag" } else { "a Write" }
            );
        }
    }
}

pub fn check_safety(
    model: Model,
    preamble_effects: &EffectSeq,
    thread_effects: &EffectBar,
    singular: &std::collections::BTreeSet<Region>,
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
            check_realisation(model, preamble, combo, singular, &dbg)?;
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
    singular: &std::collections::BTreeSet<Region>,
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
    let preserved = po_m_edges(model, &events);
    dbg.po_edges(model, &events, &preserved);

    // --- solver -----------------------------------------------------------
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    // Unsat-core tracking costs solving time, so it follows --debug.
    let mut c = Constraints::new(&ctx, dbg.enabled);
    let tt = Bool::from_bool(&ctx, true);

    // Generated constant names, mapped back to the events they stand for so
    // that the rendered formula reads in terms of the program.
    let mut names = Names::new();
    for i in 0..n {
        names.insert(format!("ts_{i}"), format!("ts({})", events[i].short()));
        names.insert(format!("u_{i}"), format!("u({})", events[i].short()));
        names.insert(format!("live_{i}"), format!("live({})", events[i].short()));
        names.insert(
            format!("resolved_{i}"),
            format!("resolved({})", events[i].short()),
        );
    }

    // `ts`: a linear extension of `<_M|_L U grf U co U rb`
    let ts: Vec<Int> = (0..n)
        .map(|i| Int::new_const(&ctx, format!("ts_{i}")))
        .collect();
    let zero = Int::from_i64(&ctx, 0);
    c.group("ts");
    for t in ts.iter() {
        c.add(t.ge(&zero));
    }
    for i in 0..n {
        for j in (i + 1)..n {
            c.add(ts[i]._eq(&ts[j]).not());
        }
    }

    // `grf`: one boolean per (reader, admissible writer) pair.
    let mut grf: Vec<(usize, Vec<(usize, Bool)>)> = Vec::new();
    for r in 0..n {
        if !is_reader(&events[r].eff.kind) {
            continue;
        }
        let cands: Vec<(usize, Bool)> = (0..n)
            .filter(|&w| {
                w != r && may_read_from(events[r].eff, events[w].eff) && !po(&events[r], &events[w])
            })
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

    for (r, cands) in &grf {
        for (w, _) in cands {
            names.insert(
                format!("grf_{r}_{w}"),
                format!("grf({}) = {}", events[*r].short(), events[*w].short()),
            );
        }
    }

    let grf_of = |r: usize| -> &[(usize, Bool)] {
        grf.iter()
            .find(|(x, _)| *x == r)
            .map(|(_, c)| c.as_slice())
            .unwrap_or(&[])
    };

    // grf is a function: at most one source per reader.
    c.group("grf");
    for (_, cands) in &grf {
        for a in 0..cands.len() {
            for b in (a + 1)..cands.len() {
                c.add(Bool::and(&ctx, &[&cands[a].1, &cands[b].1]).not());
            }
        }
    }

    // `resolved` and `L` are named rather than inlined, so that they appear
    // as atoms in the rendered formula and in an unsat core instead of being
    // expanded at every use.
    c.group("definitions");

    // resolved : a wait is resolved when grf gives it a source.
    let resolved: Vec<Bool> = (0..n)
        .map(|i| Bool::new_const(&ctx, format!("resolved_{i}")))
        .collect();
    for i in 0..n {
        // Only a reader can be resolved; the others are never consulted.
        if !is_reader(&events[i].eff.kind) {
            continue;
        }
        let cands = grf_of(i);
        let body = if cands.is_empty() {
            Bool::from_bool(&ctx, false)
        } else {
            let refs: Vec<&Bool> = cands.iter().map(|(_, b)| b).collect();
            Bool::or(&ctx, &refs)
        };
        c.add(resolved[i]._eq(&body));
    }

    // `L`: an event is live when every wait and check strictly before it in
    // `<` is resolved. The clause excludes the event itself, so an unresolved
    // wait or check is live and only what follows it is dead.
    let live: Vec<Bool> = (0..n)
        .map(|i| Bool::new_const(&ctx, format!("live_{i}")))
        .collect();
    for i in 0..n {
        let blockers: Vec<&Bool> = (0..n)
            .filter(|&l| {
                matches!(events[l].eff.kind, EffectKind::Wait | EffectKind::Check)
                    && po(&events[l], &events[i])
            })
            .map(|l| &resolved[l])
            .collect();
        let body = if blockers.is_empty() {
            tt.clone()
        } else {
            Bool::and(&ctx, &blockers)
        };
        c.add(live[i]._eq(&body));
    }

    // wf_grf: grf covers every live reader, and relates live events only.
    c.group("wf_grf");
    for (r, cands) in &grf {
        if events[*r].eff.kind == EffectKind::Read {
            c.add(live[*r].implies(&resolved[*r]));
        }
        for (w, b) in cands {
            c.add(b.implies(&Bool::and(&ctx, &[&live[*r], &live[*w]])));
        }
    }

    // The relation the acyclicity check ranges over is `grf_M U <_M|_L U co U
    // rb`. A reads-from edge the model keeps thread-local is not in `grf_M`,
    // so it is neither ordered here nor carried by `hb_M` below. `rb` is still
    // built from `grf` whole.
    let mut global_rf: Vec<(usize, usize, Bool)> = Vec::new();
    for (r, cands) in &grf {
        for (w, b) in cands {
            if grf_m(model, &events, *w, *r) {
                global_rf.push((*w, *r, b.clone()));
            }
        }
    }
    dbg.grf_m_pairs(
        &events,
        &global_rf
            .iter()
            .map(|(w, r, _)| (*w, *r))
            .collect::<Vec<_>>(),
    );

    c.group("grf\u{2098}");
    for (w, r, b) in &global_rf {
        c.add(b.implies(&ts[*w].lt(&ts[*r])));
    }

    c.group("<\u{2098}|\u{2097}");
    for (i, j) in &preserved {
        let both = Bool::and(&ctx, &[&live[*i], &live[*j]]);
        c.add(both.implies(&ts[*i].lt(&ts[*j])));
    }

    // `rb = grf^-1 ; co`, with co read off ts.
    c.group("rb");
    for (r, cands) in &grf {
        for (w, b) in cands {
            if !is_co_event(&events[*w].eff.kind) || !on_singular(singular, &events[*w]) {
                continue;
            }
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
                c.add(ante.implies(&ts[*r].lt(&ts[w2])));
            }
        }
    }

    c.group("sc_per_loc'");
    for (r, cands) in &grf {
        for (w, b) in cands {
            if !on_singular(singular, &events[*w]) {
                continue;
            }
            for a in 0..n {
                if a == *w || a == *r {
                    continue;
                }
                if !is_writing(&events[a].eff.kind)
                    || !same_region(events[a].eff, events[*w].eff)
                    || events[a].tid != events[*r].tid
                    || !po(&events[a], &events[*r])
                {
                    continue;
                }
                let ante = Bool::and(&ctx, &[b, &live[a]]);
                c.add(ante.implies(&ts[a].lt(&ts[*w])));
            }
        }
    }

    // `value_constraint`: a branch may only be taken if the guard read could
    // have observed the value that selects it. A `flag` event sets the
    // location, a `new` or `write` leaves it unset, so the then-branch
    // requires a flag source and the else-branch forbids one.
    dbg.choices(&events, &choices);
    c.group("value_constraint");
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
            c.add(live[*g].implies(&any_flag));
        } else {
            for b in flags {
                c.add(live[*g].implies(&b.not()));
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

        c.push();
        c.group("graph_erroneous");

        let u: Vec<Bool> = (0..n)
            .map(|i| Bool::new_const(&ctx, format!("u_{i}")))
            .collect();

        c.add(live[f].clone());
        c.add(u[f].not());

        for (i, j) in &preserved {
            let ante = Bool::and(&ctx, &[&live[*i], &live[*j], &u[*i]]);
            c.add(ante.implies(&u[*j]));
        }
        for (w, r, b) in &global_rf {
            c.add(Bool::and(&ctx, &[b, &u[*w]]).implies(&u[*r]));
        }

        let witnesses: Vec<Bool> = others
            .iter()
            .map(|&e| Bool::and(&ctx, &[&live[e], &u[e]]))
            .collect();
        let refs: Vec<&Bool> = witnesses.iter().collect();
        c.add(Bool::or(&ctx, &refs));

        if dbg.enabled {
            println!(
                "\n=== Is there a counterexample execution? ===\n\
                 \x20 \u{2203} grf, ts, u.  wf_grf(grf) \u{2227} M(grf) \u{2227} graph_erroneous(hb)\n\
                 \x20 free under test: {}\n\
                 \x20 u collects events the free is unreachable from. Anything an\n\
                 \x20 event in u reaches is in u too, and the free is not in u, so\n\
                 \x20 nothing in u is ordered before it. A counterexample is a live\n\
                 \x20 event on region {} sitting in u.\n\
                 \x20 Unsat means no such execution, so this free is safe.\n{}",
                events[f].show(),
                rho.name(),
                render_query(&c.labelled(), &names, 72)
            );
        }

        let result = c.check();
        match result {
            SatResult::Unsat => {
                if dbg.enabled {
                    let core = c.unsat_core_terms();
                    if !core.is_empty() {
                        println!("\n=== Unsat core ({} assertions) ===", core.len());
                        for (g, t) in &core {
                            println!("  [{}] {}", g, render_flat(t, &names));
                        }
                    }
                }
                c.pop();
            }
            SatResult::Sat => {
                let model_z3 = c.solver().get_model().unwrap();
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
                c.pop();
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
                c.pop();
                return Err(TauRelaxError::SafetyError {
                    message: format!("Z3 returned unknown while checking {}", events[f].show()),
                });
            }
        }
    }

    Ok(())
}
