use crate::ast::{global_region, Expr, LocName, Region, SiteId, Value};
use crate::checker::{site_loc, site_region, GLOB_LOC};
use crate::types::EffectKind;
use crate::error::TauRelaxError;
use std::collections::HashMap;

/// A runtime action: `a ::= m^rho | r^rho | fence`.
#[derive(Debug, Clone, PartialEq)]
pub struct Action {
    pub kind: EffectKind,
    pub region: Option<Region>,
}

impl Action {
    fn mem(kind: EffectKind, region: Region) -> Self {
        Action { kind, region: Some(region) }
    }
    fn fence() -> Self {
        Action { kind: EffectKind::Fence, region: None }
    }
}

/// What a thread-local step discharges: `alpha ::= a | (+)_j | .`
#[derive(Debug, Clone, PartialEq)]
pub enum Annot {
    /// consumes an action
    Act(Action),
    /// commits to branch j of a choice node
    Branch(usize),
    /// discharges nothing
    Silent,
}

/// A memory label. The label and the annotation are independent: `set`
/// emits `WRITE` while discharging `flag^rho`, the busy-wait emits `READ`
/// while discharging `wait^rho` on exit and nothing on a failed poll, and
/// `ref v at e` emits `ALLOC` while discharging `write^rho`.
#[derive(Debug, Clone, PartialEq)]
pub enum Label {
    Epsilon,
    New(String, Value),
    Alloc(String, Value),
    Write(String, Value),
    Read(String, Value),
    Free(Region),
    Fence,
}

// ------------------------------------------------------------ memory state

pub type Store = HashMap<String, Value>;

/// The machine's memory. Under TSO this gains one write buffer per thread;
/// it gains nothing else.
#[derive(Debug, Clone)]
pub struct Mem {
    pub store: Store,
}

impl Mem {
    /// `S_0` binds the global location and nothing else.
    pub fn initial() -> Self {
        let mut store = Store::new();
        store.insert(GLOB_LOC.to_string(), Value::Unit);
        Mem { store }
    }

    /// The bound locations of a region. A region is present exactly when this
    /// is non-empty; deallocation removes its members.
    pub fn locs(&self, rho: &Region) -> Vec<String> {
        self.store
            .keys()
            .filter(|l| region_of(l).ok().as_ref() == Some(rho))
            .cloned()
            .collect()
    }

    /// The global region is present in every configuration.
    pub fn present(&self, rho: &Region) -> bool {
        *rho == global_region() || !self.locs(rho).is_empty()
    }
}

// ------------------------------------------------------- memory subsystem

/// `M ==(t:I)==> M', v`. Every side condition is a condition on the store:
/// that a region has bindings, that it has none, or that a location is bound.
fn mem_step(mem: &mut Mem, label: &Label) -> Result<Value, TauRelaxError> {
    let err = |m: String| TauRelaxError::RuntimeError { message: m };

    match label {
        Label::Epsilon | Label::Fence => Ok(Value::Unit),

        // SC-new: the region must have no bindings
        Label::New(loc, v) => {
            let rho = region_of(loc)?;
            if !mem.locs(&rho).is_empty() {
                return Err(err(format!("region {} is already present", rho.name())));
            }
            mem.store.insert(loc.clone(), v.clone());
            Ok(Value::Unit)
        }

        // SC-alloc: a fresh location in a region that is present. Allocation
        // writes through under TSO too: a buffered allocation would leave the
        // location unbound until the buffer drained.
        Label::Alloc(loc, v) => {
            let rho = region_of(loc)?;
            if !mem.present(&rho) {
                return Err(err(format!("allocation in absent region {}", rho.name())));
            }
            if mem.store.contains_key(loc) {
                return Err(err(format!("location {} is already bound", loc)));
            }
            mem.store.insert(loc.clone(), v.clone());
            Ok(Value::Unit)
        }

        // SC-write: the location must be bound
        Label::Write(loc, v) => {
            if !mem.store.contains_key(loc) {
                return Err(err(format!("write to unbound location {}", loc)));
            }
            mem.store.insert(loc.clone(), v.clone());
            Ok(Value::Unit)
        }

        // SC-read: the value is the binding, so no separate guard is needed
        Label::Read(loc, _) => mem
            .store
            .get(loc)
            .cloned()
            .ok_or_else(|| err(format!("read from unbound location {}", loc))),

        // SC-free: the region's bindings are removed. This is what makes a
        // use-after-free stuck: the binding is gone, rather than a predicate
        // recording that the region has died.
        Label::Free(rho) => {
            let locs = mem.locs(rho);
            if locs.is_empty() {
                return Err(err(format!("free of absent region {}", rho.name())));
            }
            for l in locs {
                mem.store.remove(&l);
            }
            Ok(Value::Unit)
        }
    }
}

// ------------------------------------------------------- thread-local step

pub type Env = HashMap<String, Value>;

pub struct StepOut {
    pub expr: Expr,
    pub env: Env,
    pub label: Label,
    pub annot: Annot,
}

pub fn is_value(e: &Expr) -> bool {
    matches!(e, Expr::Val(_))
}

fn as_value(e: &Expr) -> Option<&Value> {
    match e {
        Expr::Val(v) => Some(v),
        _ => None,
    }
}

/// The location a name denotes, resolved through the environment.
fn resolve_loc(name: &str, env: &Env) -> Result<String, TauRelaxError> {
    match env.get(name) {
        Some(Value::Loc(l)) => Ok(l.name.clone()),
        Some(v) => Err(TauRelaxError::RuntimeError {
            message: format!("{} is bound to {:?}, not a location", name, v),
        }),
        // a location named directly in the source denotes itself
        None => Ok(name.to_string()),
    }
}

/// The region a location belongs to. Locations are named by their allocation
/// site, so the region is recoverable from the name.
fn region_of(loc: &str) -> Result<Region, TauRelaxError> {
    if loc == GLOB_LOC {
        return Ok(global_region());
    }
    loc.strip_prefix("l_site")
        .and_then(|s| s.parse::<SiteId>().ok())
        .map(site_region)
        .ok_or_else(|| TauRelaxError::RuntimeError {
            message: format!("cannot determine the region of {}", loc),
        })
}

/// One thread-local step, or `None` if the expression is a value.
pub fn step(
    e: &Expr,
    env: &Env,
    mem: &Mem,
) -> Result<Option<StepOut>, TauRelaxError> {
    let keep = |expr: Expr, label: Label, annot: Annot| {
        Ok(Some(StepOut { expr, env: env.clone(), label, annot }))
    };
    let glob = || Expr::Val(Value::Loc(crate::ast::Location {
        name: GLOB_LOC.to_string(),
        region: global_region(),
    }));

    match e {
        Expr::Val(_) => Ok(None),

        // a variable resolves to the value bound for it
        Expr::Var(x) => match env.get(x) {
            Some(v) => keep(Expr::Val(v.clone()), Label::Epsilon, Annot::Silent),
            None => Err(TauRelaxError::RuntimeError {
                message: format!("unbound variable {}", x),
            }),
        },

        // e-newrgn: allocates the region and its header location
        Expr::NewRgn(site) => {
            let loc = site_loc(*site);
            let rho = site_region(*site);
            keep(
                Expr::Val(Value::Loc(crate::ast::Location {
                    name: loc.clone(),
                    region: rho.clone(),
                })),
                Label::New(loc, Value::Unit),
                Annot::Act(Action::mem(EffectKind::New, rho)),
            )
        }

        // e-ref / e-refL
        Expr::RefAt(site, v, inner) => {
            if let Some(Value::Loc(l)) = as_value(inner) {
                let loc = site_loc(*site);
                keep(
                    Expr::Val(Value::Loc(crate::ast::Location {
                        name: loc.clone(),
                        region: l.region.clone(),
                    })),
                    Label::Alloc(loc, v.clone()),
                    Annot::Act(Action::mem(EffectKind::Write, l.region.clone())),
                )
            } else {
                congruence(inner, env, mem, |i| Expr::RefAt(*site, v.clone(), Box::new(i)))
            }
        }

        // e-freergn / e-freergnL
        Expr::FreeRgn(inner) => {
            if let Some(Value::Loc(l)) = as_value(inner) {
                keep(
                    glob(),
                    Label::Free(l.region.clone()),
                    Annot::Act(Action::mem(EffectKind::Free, l.region.clone())),
                )
            } else {
                congruence(inner, env, mem, |i| Expr::FreeRgn(Box::new(i)))
            }
        }

        // e-deref / e-derefL
        Expr::Deref(inner) => {
            if let Some(Value::Loc(l)) = as_value(inner) {
                let v = peek(mem, &l.name)?;
                keep(
                    Expr::Val(v.clone()),
                    Label::Read(l.name.clone(), v),
                    Annot::Act(Action::mem(EffectKind::Read, l.region.clone())),
                )
            } else {
                congruence(inner, env, mem, |i| Expr::Deref(Box::new(i)))
            }
        }

        // e-assign / e-assignL
        Expr::Assign(LocName(name), inner) => {
            if let Some(v) = as_value(inner) {
                let loc = resolve_loc(name, env)?;
                let rho = region_of(&loc)?;
                keep(
                    glob(),
                    Label::Write(loc, v.clone()),
                    Annot::Act(Action::mem(EffectKind::Write, rho)),
                )
            } else {
                let n = name.clone();
                congruence(inner, env, mem, move |i| {
                    Expr::Assign(LocName(n.clone()), Box::new(i))
                })
            }
        }

        // e-set
        Expr::Set(LocName(name)) => {
            let loc = resolve_loc(name, env)?;
            let rho = region_of(&loc)?;
            keep(
                glob(),
                Label::Write(loc, Value::Flag(true)),
                Annot::Act(Action::mem(EffectKind::Flag, rho)),
            )
        }

        // e-whileSpin / e-whileExit: the same label, different annotations.
        // A failed poll discharges nothing, so the single static wait action
        // survives until the loop exits.
        Expr::While(LocName(name)) => {
            let loc = resolve_loc(name, env)?;
            let rho = region_of(&loc)?;
            let v = peek(mem, &loc)?;
            let unset = matches!(v, Value::Flag(false));
            if unset {
                keep(
                    e.clone(),
                    Label::Read(loc, v),
                    Annot::Silent,
                )
            } else {
                keep(
                    glob(),
                    Label::Read(loc, v),
                    Annot::Act(Action::mem(EffectKind::Wait, rho)),
                )
            }
        }

        // e-check: emits the read and steps to the residue
        Expr::Check(LocName(name), e1, e2) => {
            let loc = resolve_loc(name, env)?;
            let rho = region_of(&loc)?;
            let v = peek(mem, &loc)?;
            keep(
                Expr::CheckResidue(LocName(name.clone()), v.clone(), e1.clone(), e2.clone()),
                Label::Read(loc, v),
                Annot::Act(Action::mem(EffectKind::Read, rho)),
            )
        }

        // e-checkSet / e-checkUnset: silent commits
        Expr::CheckResidue(_, v, e1, e2) => {
            let taken = !matches!(v, Value::Flag(false));
            let (branch, j) = if taken { (e1, 0) } else { (e2, 1) };
            keep((**branch).clone(), Label::Epsilon, Annot::Branch(j))
        }

        // e-fence
        Expr::Fence(inner) => keep(
            (**inner).clone(),
            Label::Fence,
            Annot::Act(Action::fence()),
        ),

        // e-seq / e-seqNext
        Expr::Seq(e1, e2) => {
            if is_value(e1) {
                keep((**e2).clone(), Label::Epsilon, Annot::Silent)
            } else {
                let tail = e2.clone();
                congruence(e1, env, mem, move |i| {
                    Expr::Seq(Box::new(i), tail.clone())
                })
            }
        }

        // e-let / e-letL
        Expr::Let(x, e1, e2) => {
            if let Some(v) = as_value(e1) {
                let mut env2 = env.clone();
                env2.insert(x.clone(), v.clone());
                Ok(Some(StepOut {
                    expr: (**e2).clone(),
                    env: env2,
                    label: Label::Epsilon,
                    annot: Annot::Silent,
                }))
            } else {
                let x2 = x.clone();
                let body = e2.clone();
                congruence(e1, env, mem, move |i| {
                    Expr::Let(x2.clone(), Box::new(i), body.clone())
                })
            }
        }
    }
}

/// Read a value without recording anything — used to decide which rule
/// applies before the subsystem step is taken.
fn peek(mem: &Mem, loc: &str) -> Result<Value, TauRelaxError> {
    mem.store.get(loc).cloned().ok_or_else(|| TauRelaxError::RuntimeError {
        message: format!("unbound location {}", loc),
    })
}

/// A congruence step: reduce the subexpression and rebuild the context,
/// propagating both annotations unchanged.
fn congruence<F>(
    inner: &Expr,
    env: &Env,
    mem: &Mem,
    rebuild: F,
) -> Result<Option<StepOut>, TauRelaxError>
where
    F: FnOnce(Expr) -> Expr,
{
    match step(inner, env, mem)? {
        None => Err(TauRelaxError::RuntimeError {
            message: "stuck: subexpression is a value of the wrong shape".to_string(),
        }),
        Some(out) => Ok(Some(StepOut {
            expr: rebuild(out.expr),
            env: out.env,
            label: out.label,
            annot: out.annot,
        })),
    }
}

// ------------------------------------------------------------ global steps

pub struct Thread {
    pub expr: Expr,
    pub env: Env,
}

/// One entry of the trace: which thread stepped, and what it discharged.
#[derive(Debug, Clone)]
pub struct TraceEntry {
    pub thread: usize,
    pub annot: Annot,
}

pub struct Config {
    pub threads: Vec<Thread>,
    pub mem: Mem,
    /// The trace so far. The history `H` of the metatheory is recovered from
    /// this by `history()`; no rule of the semantics consults it.
    pub trace: Vec<TraceEntry>,
}

impl Config {
    pub fn new(threads: Vec<Expr>, env: Env) -> Self {
        Config {
            threads: threads
                .into_iter()
                .map(|expr| Thread { expr, env: env.clone() })
                .collect(),
            mem: Mem::initial(),
            trace: Vec::new(),
        }
    }

    pub fn done(&self) -> bool {
        self.threads.iter().all(|t| is_value(&t.expr))
    }

    /// `H_0 = { t |-> eps }`, `H_{k+1} = shift(t_k, alpha_k, H_k)`.
    /// A derived object: the machine does not carry it.
    pub fn history(&self) -> HashMap<usize, Vec<Action>> {
        let mut h: HashMap<usize, Vec<Action>> = HashMap::new();
        for t in 0..self.threads.len() {
            h.insert(t, Vec::new());
        }
        for entry in &self.trace {
            if let Annot::Act(a) = &entry.annot {
                h.entry(entry.thread).or_default().push(a.clone());
            }
        }
        h
    }

    /// One global step by thread `tid`, if it can take one.
    pub fn step_thread(&mut self, tid: usize) -> Result<bool, TauRelaxError> {
        let out = {
            let t = &self.threads[tid];
            step(&t.expr, &t.env, &self.mem)?
        };
        let out = match out {
            None => return Ok(false),
            Some(o) => o,
        };
        // global-non-silent routes the label through the subsystem;
        // global-silent does not. Neither touches a history.
        if out.label != Label::Epsilon {
            mem_step(&mut self.mem, &out.label)?;
        }
        self.trace.push(TraceEntry { thread: tid, annot: out.annot });
        self.threads[tid].expr = out.expr;
        self.threads[tid].env = out.env;
        Ok(true)
    }
}

/// Run under a round-robin schedule until every thread is a value. A thread
/// spinning on a flag no other thread sets will not terminate: Progress
/// guarantees a step is always available, not that one makes headway.
pub fn run_sc(threads: Vec<Expr>, env: Env, fuel: usize) -> Result<Config, TauRelaxError> {
    let mut cfg = Config::new(threads, env);
    let mut steps = 0;
    while !cfg.done() {
        if steps >= fuel {
            return Err(TauRelaxError::RuntimeError {
                message: format!("out of fuel after {} steps", fuel),
            });
        }
        let mut progressed = false;
        for tid in 0..cfg.threads.len() {
            if cfg.step_thread(tid)? {
                progressed = true;
                steps += 1;
            }
        }
        if !progressed {
            break;
        }
    }
    Ok(cfg)
}