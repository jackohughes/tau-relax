use crate::ast::{global_region, Expr, LocName, Region, SiteId, Value};
use crate::checker::{site_loc, site_region, GLOB_LOC};
use crate::types::EffectKind;
use crate::error::TauRelaxError;
use std::collections::HashMap;

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

#[derive(Debug, Clone, PartialEq)]
pub enum Annot {
    /// consumes an action
    Act(Action),
    /// commits to branch j of a choice node
    Branch(usize),
    /// discharges nothing
    Silent,
}

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

pub type Store = HashMap<String, Value>;
pub type Log = Vec<Action>;

#[derive(Debug, Clone)]
pub struct Mem {
    pub store: Store,
    pub history: HashMap<usize, Log>,
}

impl Mem {
    /// `S_0` binds the global location; `H_0` gives every thread an empty log.
    pub fn initial(threads: usize) -> Self {
        let mut store = Store::new();
        store.insert(GLOB_LOC.to_string(), Value::Unit);
        let mut history = HashMap::new();
        for t in 0..threads {
            history.insert(t, Log::new());
        }
        Mem { store, history }
    }

    fn actions(&self) -> impl Iterator<Item = &Action> {
        self.history.values().flat_map(|log| log.iter())
    }

    pub fn allocated(&self, rho: &Region) -> bool {
        self.actions().any(|a| {
            a.kind == EffectKind::New && a.region.as_ref() == Some(rho)
        })
    }

    pub fn freed(&self, rho: &Region) -> bool {
        self.actions().any(|a| {
            a.kind == EffectKind::Free && a.region.as_ref() == Some(rho)
        })
    }

    /// The global region is live in every history; every other region is
    /// live once allocated and until freed.
    pub fn live(&self, rho: &Region) -> bool {
        *rho == global_region() || (self.allocated(rho) && !self.freed(rho))
    }

    /// `shift(t, alpha, M)`: extend the log only when an action was consumed.
    fn shift(&mut self, tid: usize, annot: &Annot) {
        if let Annot::Act(a) = annot {
            self.history.entry(tid).or_default().push(a.clone());
        }
    }
}

fn mem_step(mem: &mut Mem, label: &Label) -> Result<Value, TauRelaxError> {
    let err = |m: String| TauRelaxError::RuntimeError { message: m };

    match label {
        Label::Epsilon | Label::Fence => Ok(Value::Unit),

        Label::New(loc, v) => {
            let rho = region_of(loc)?;
            if mem.allocated(&rho) {
                return Err(err(format!("region {} allocated twice", rho.name())));
            }
            mem.store.insert(loc.clone(), v.clone());
            Ok(Value::Unit)
        }

        Label::Alloc(loc, v) => {
            let rho = region_of(loc)?;
            if !mem.live(&rho) {
                return Err(err(format!("allocation in dead region {}", rho.name())));
            }
            if mem.store.contains_key(loc) {
                return Err(err(format!("location {} allocated twice", loc)));
            }
            mem.store.insert(loc.clone(), v.clone());
            Ok(Value::Unit)
        }

        Label::Write(loc, v) => {
            let rho = region_of(loc)?;
            if !mem.live(&rho) {
                return Err(err(format!("write to dead region {}", rho.name())));
            }
            if !mem.store.contains_key(loc) {
                return Err(err(format!("write to unbound location {}", loc)));
            }
            mem.store.insert(loc.clone(), v.clone());
            Ok(Value::Unit)
        }

        Label::Read(loc, _) => {
            let rho = region_of(loc)?;
            if !mem.live(&rho) {
                return Err(err(format!("read from dead region {}", rho.name())));
            }
            mem.store
                .get(loc)
                .cloned()
                .ok_or_else(|| err(format!("read from unbound location {}", loc)))
        }

        Label::Free(rho) => {
            if !mem.live(rho) {
                return Err(err(format!("free of dead region {}", rho.name())));
            }
            // the store is untouched: deallocation is recorded in the history
            Ok(Value::Unit)
        }
    }
}

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

pub struct Thread {
    pub expr: Expr,
    pub env: Env,
}

pub struct Config {
    pub threads: Vec<Thread>,
    pub mem: Mem,
}

impl Config {
    pub fn new(threads: Vec<Expr>, env: Env) -> Self {
        let mem = Mem::initial(threads.len());
        Config {
            threads: threads
                .into_iter()
                .map(|expr| Thread { expr, env: env.clone() })
                .collect(),
            mem,
        }
    }

    pub fn done(&self) -> bool {
        self.threads.iter().all(|t| is_value(&t.expr))
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
        // global-silent does not. Both then apply shift.
        if out.label != Label::Epsilon {
            mem_step(&mut self.mem, &out.label)?;
        }
        self.mem.shift(tid, &out.annot);
        self.threads[tid].expr = out.expr;
        self.threads[tid].env = out.env;
        Ok(true)
    }
}

pub fn run_sc(
    threads: Vec<Expr>,
    env: Env,
    fuel: usize,
) -> Result<Config, TauRelaxError> {
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