use crate::ast::{Expr, LocName, Location, Program, Region, SiteId, Value, global_region, sites};
use crate::effects::{AliveSet, effects_ok};
use crate::error::TauRelaxError;
use crate::options::Options;
use crate::safety::check_safety;
use crate::substitution::{Substitution, unify, unify_region};
use crate::types::{Effect, EffectBar, EffectKind, EffectSeq, Ty, TypeWithPlace};

pub type TypeEnv = std::collections::HashMap<String, TypeWithPlace>;

pub type StoreTyping = std::collections::HashMap<String, TypeWithPlace>;

pub const GLOB_LOC: &str = "l_glob";

pub fn glob_loc_ty() -> TypeWithPlace {
    TypeWithPlace {
        ty: Ty::Ref(Box::new(Ty::Unit)),
        region: global_region(),
    }
}

pub fn site_loc(s: SiteId) -> String {
    format!("l_site{}", s)
}

pub fn site_region(s: SiteId) -> Region {
    Region::Named(format!("r{}", s))
}

pub struct TypeCheckCtxt {
    pub gamma: TypeEnv,
    pub sigma: StoreTyping,
    pub subst: Substitution,
    pub effect_counter: usize,
    pub thread_id: usize,
    pub type_var_counter: usize,
    pub region_var_counter: usize,
}

impl TypeCheckCtxt {
    pub fn new() -> Self {
        let mut sigma = StoreTyping::new();
        // Sigma carries the global location from the outset. Its contents
        // are the unit value, so its own type is `Ref Unit`.
        sigma.insert(
            GLOB_LOC.to_string(),
            TypeWithPlace {
                ty: Ty::Unit,
                region: global_region(),
            },
        );
        TypeCheckCtxt {
            gamma: TypeEnv::new(),
            sigma,
            subst: Substitution::new(),
            effect_counter: 0,
            thread_id: 0,
            type_var_counter: 0,
            region_var_counter: 0,
        }
    }

    /// The contents type recorded for a location.
    pub fn lookup_loc(&self, name: &str) -> Result<TypeWithPlace, TauRelaxError> {
        self.sigma
            .get(name)
            .cloned()
            .map(|twp| self.subst.apply_twp(&twp))
            .ok_or_else(|| TauRelaxError::TypeError {
                message: format!("unbound location: {}", name),
            })
    }

    pub fn fresh_type_var(&mut self) -> Ty {
        let n = self.type_var_counter;
        self.type_var_counter += 1;
        Ty::Var(format!("a{}", n))
    }

    pub fn fresh_region_var(&mut self) -> Region {
        let n = self.region_var_counter;
        self.region_var_counter += 1;
        Region::Var(n)
    }

    pub fn fresh_effect_index(&mut self) -> usize {
        let n = self.effect_counter;
        self.effect_counter += 1;
        n
    }

    pub fn make_effect(&mut self, kind: EffectKind, region: Region) -> Effect {
        Effect {
            kind,
            region: Some(region),
            index: self.fresh_effect_index(),
        }
    }

    /// A fence carries no target region.
    pub fn make_fence(&mut self) -> Effect {
        Effect {
            kind: EffectKind::Fence,
            region: None,
            index: self.fresh_effect_index(),
        }
    }

    pub fn zonk(&self, ty: &Ty) -> Ty {
        self.subst.apply(ty)
    }

    pub fn zonk_twp(&self, twp: &TypeWithPlace) -> TypeWithPlace {
        self.subst.apply_twp(twp)
    }
}

/// Populate Sigma before checking, with one entry per allocation site.
///
/// A `newrgn` site is given a concrete region and a header location. A
/// `ref v at e` site is given a location whose region is a *variable*: the
/// region comes from `e`, which is not known until the expression is
/// checked, and unification resolves it there.
///
/// Numbering sites in a single pass makes them distinct by construction, so
/// the hygiene condition — that distinct threads allocate at distinct sites
/// — holds automatically. This function rejects a duplicate site outright,
/// since that would mean the numbering pass had not been run.
pub fn prepopulate(program: &Program, ctxt: &mut TypeCheckCtxt) -> Result<(), TauRelaxError> {
    let mut all: Vec<(SiteId, bool)> = Vec::new();
    for (_, e) in &program.preamble {
        sites(e, &mut all);
    }
    for e in &program.threads {
        sites(e, &mut all);
    }

    let mut seen: std::collections::HashSet<SiteId> = std::collections::HashSet::new();
    for (s, is_region_site) in all {
        if !seen.insert(s) {
            return Err(TauRelaxError::TypeError {
                message: format!(
                    "allocation site {} occurs twice; sites must be numbered \
                     before checking",
                    s
                ),
            });
        }
        let loc = site_loc(s);
        let (ty, region) = if is_region_site {
            // the header location of a fresh region; its contents are unit
            (Ty::Unit, site_region(s))
        } else {
            // a `ref` site: contents type and region both to be resolved
            (ctxt.fresh_type_var(), ctxt.fresh_region_var())
        };
        ctxt.sigma.insert(loc, TypeWithPlace { ty, region });
    }
    Ok(())
}

/// The regions Sigma gives exactly one location besides the header its
/// allocation creates. On such a region "same region" and "same location"
/// coincide, which is what lets `rb` and `sc_per_thread` be asserted there.
///
/// Sigma holds each location twice, under its preamble binder and under its
/// site name, so only the site names are counted. A header is the location a
/// `newrgn` site binds, so `l_site<s>` is one exactly when its region is the
/// one that site names; `l_glob` is the global region's header.
fn is_header(name: &str, region: &Region) -> bool {
    if name == GLOB_LOC {
        return true;
    }
    match name
        .strip_prefix("l_site")
        .and_then(|s| s.parse::<SiteId>().ok())
    {
        Some(s) => *region == site_region(s),
        None => false,
    }
}

pub fn singular_regions(ctxt: &TypeCheckCtxt) -> std::collections::BTreeSet<Region> {
    let mut counts: std::collections::BTreeMap<Region, usize> = std::collections::BTreeMap::new();
    for (name, twp) in &ctxt.sigma {
        if !(name.starts_with("l_site") || name == GLOB_LOC) {
            continue;
        }
        if is_header(name, &ctxt.subst.apply_region(&twp.region)) {
            continue;
        }
        *counts
            .entry(ctxt.subst.apply_region(&twp.region))
            .or_insert(0) += 1;
    }
    counts
        .into_iter()
        .filter(|(_, n)| *n == 1)
        .map(|(r, _)| r)
        .collect()
}

/// Resolve every region and type recorded in an effect sequence, so that the
/// safety checker sees concrete regions only.
fn zonk_effects(seq: &EffectSeq, subst: &Substitution) -> EffectSeq {
    match seq {
        EffectSeq::Empty => EffectSeq::Empty,
        EffectSeq::Single(e) => EffectSeq::Single(Effect {
            kind: e.kind.clone(),
            region: e.region.as_ref().map(|r| subst.apply_region(r)),
            index: e.index,
        }),
        EffectSeq::Seq(a, b) => EffectSeq::Seq(
            Box::new(zonk_effects(a, subst)),
            Box::new(zonk_effects(b, subst)),
        ),
        EffectSeq::Branch {
            guard,
            then_,
            else_,
        } => EffectSeq::Branch {
            guard: guard.as_ref().map(|g| Effect {
                kind: g.kind.clone(),
                region: g.region.as_ref().map(|r| subst.apply_region(r)),
                index: g.index,
            }),
            then_: Box::new(zonk_effects(then_, subst)),
            else_: Box::new(zonk_effects(else_, subst)),
        },
    }
}

pub fn check_program(
    program: &Program,
    ctxt: &mut TypeCheckCtxt,
    opts: &Options,
) -> Result<(), TauRelaxError> {
    prepopulate(program, ctxt)?;

    let mut preamble_effects = EffectSeq::Empty;
    for (name, expr) in &program.preamble {
        let (twp, effects) = synth_expr(expr, ctxt)?;
        preamble_effects = preamble_effects.then(effects);
        if name.starts_with('l') {
            ctxt.sigma.insert(name.clone(), twp);
        } else {
            ctxt.gamma.insert(name.clone(), twp);
        }
    }

    // A0 = {rho_glob} U regions(preamble)
    let mut initial_alive: AliveSet = AliveSet::new();
    initial_alive.insert(global_region());
    let preamble_zonked = zonk_effects(&preamble_effects, &ctxt.subst);
    let preamble_alive = crate::effects::check(&initial_alive, &preamble_zonked).map_err(|e| {
        TauRelaxError::TypeError {
            message: format!("preamble is not well-formed: {:?}", e),
        }
    })?;

    let mut effects_per_thread = EffectBar::new();
    for (tid, thread_expr) in program.threads.iter().enumerate() {
        let mut thread_ctxt = TypeCheckCtxt {
            gamma: ctxt.gamma.clone(),
            sigma: ctxt.sigma.clone(),
            subst: ctxt.subst.clone(),
            effect_counter: 0,
            thread_id: tid,
            type_var_counter: ctxt.type_var_counter,
            region_var_counter: ctxt.region_var_counter,
        };
        let (_, phi) = synth_expr(thread_expr, &mut thread_ctxt)?;
        ctxt.subst = thread_ctxt.subst;
        ctxt.type_var_counter = thread_ctxt.type_var_counter;
        ctxt.region_var_counter = thread_ctxt.region_var_counter;
        effects_per_thread.push(phi);
    }

    let preamble_final = zonk_effects(&preamble_effects, &ctxt.subst);
    let threads_final: EffectBar = effects_per_thread
        .iter()
        .map(|phi| zonk_effects(phi, &ctxt.subst))
        .collect();

    for (tid, phi) in threads_final.iter().enumerate() {
        effects_ok(&preamble_alive, phi).map_err(|e| TauRelaxError::TypeError {
            message: format!("thread {}: {:?}", tid, e),
        })?;
    }

    // The driver reports the verdict, so this only distinguishes a type
    // failure from a safety failure, which is worth seeing when debugging.
    if opts.debug {
        println!("type check ok");
    }
    let singular = singular_regions(ctxt);
    if opts.debug {
        let names: Vec<String> = singular.iter().map(|r| r.name()).collect();
        println!("singular regions: {}", names.join(", "));
    }
    check_safety(
        opts.model,
        &preamble_final,
        &threads_final,
        &singular,
        opts.debug,
    )
}

pub fn check_expr(
    expr: &Expr,
    expected: &TypeWithPlace,
    ctxt: &mut TypeCheckCtxt,
) -> Result<EffectSeq, TauRelaxError> {
    let (ty, phi) = synth_expr(expr, ctxt)?;
    unify(&ty.ty, &expected.ty, &mut ctxt.subst)?;
    Ok(phi)
}

pub fn synth_expr(
    expr: &Expr,
    ctxt: &mut TypeCheckCtxt,
) -> Result<(TypeWithPlace, EffectSeq), TauRelaxError> {
    match expr {
        // t-newrgn: one `new` action; the result is the region's header location
        Expr::NewRgn(site) => {
            let region = site_region(*site);
            let new = ctxt.make_effect(EffectKind::New, region.clone());
            Ok((
                TypeWithPlace {
                    ty: Ty::Ref(Box::new(Ty::Unit)),
                    region,
                },
                EffectSeq::single(new),
            ))
        }

        // t-ref: the region comes from the subexpression, the type from the value
        Expr::RefAt(site, v, e) => {
            let (TypeWithPlace { ty: rgn_ty, region }, phi) = synth_expr(e, ctxt)?;
            let any = ctxt.fresh_type_var();
            unify(&rgn_ty, &Ty::Ref(Box::new(any)), &mut ctxt.subst)?;
            let v_ty = synth_value(v, ctxt)?;
            if matches!(v_ty, Ty::Flag) && !matches!(v, Value::Flag(false)) {
                return Err(TauRelaxError::TypeError {
                    message: "a flag location must be created unset".to_string(),
                });
            }

            // reconcile the site's pre-declared entry with what we found
            let declared = ctxt.lookup_loc(&site_loc(*site))?;
            unify(&declared.ty, &v_ty, &mut ctxt.subst)?;
            unify_region(&declared.region, &region, &mut ctxt.subst)?;

            let write = ctxt.make_effect(EffectKind::Write, region.clone());
            Ok((
                TypeWithPlace {
                    ty: Ty::Ref(Box::new(v_ty)),
                    region,
                },
                phi.then(EffectSeq::single(write)),
            ))
        }

        Expr::FreeRgn(e) => {
            let (TypeWithPlace { ty: rgn_ty, region }, phi) = synth_expr(e, ctxt)?;
            let any = ctxt.fresh_type_var();
            unify(&rgn_ty, &Ty::Ref(Box::new(any)), &mut ctxt.subst)?;
            if region == global_region() {
                return Err(TauRelaxError::TypeError {
                    message: "the global region cannot be freed".to_string(),
                });
            }
            let free = ctxt.make_effect(EffectKind::Free, region);
            Ok((glob_loc_ty(), phi.then(EffectSeq::single(free))))
        }

        Expr::Deref(e) => {
            let (TypeWithPlace { ty, region }, phi) = synth_expr(e, ctxt)?;
            let inner = ctxt.fresh_type_var();
            unify(&ty, &Ty::Ref(Box::new(inner.clone())), &mut ctxt.subst)?;
            let read = EffectSeq::single(ctxt.make_effect(EffectKind::Read, region.clone()));
            Ok((
                TypeWithPlace {
                    ty: ctxt.subst.apply(&inner),
                    region,
                },
                phi.then(read),
            ))
        }

        Expr::Assign(LocName(name), e) => {
            let twp = ctxt.lookup_loc(name)?;
            let region = twp.region.clone();
            let contents = ctxt.fresh_type_var();
            unify(
                &twp.ty,
                &Ty::Ref(Box::new(contents.clone())),
                &mut ctxt.subst,
            )?;
            let contents = ctxt.subst.apply(&contents);
            if matches!(contents, Ty::Flag | Ty::Unit) {
                return Err(TauRelaxError::TypeError {
                    message: format!(
                        "cannot assign to a location of contents type {:?}",
                        contents
                    ),
                });
            }
            let rhs_phi = check_expr(
                e,
                &TypeWithPlace {
                    ty: contents,
                    region: region.clone(),
                },
                ctxt,
            )?;
            let write = ctxt.make_effect(EffectKind::Write, region);
            Ok((glob_loc_ty(), rhs_phi.then(EffectSeq::single(write))))
        }

        Expr::Seq(e1, e2) => {
            let (_, phi1) = synth_expr(e1, ctxt)?;
            let (ty, phi2) = synth_expr(e2, ctxt)?;
            Ok((ty, phi1.then(phi2)))
        }

        // t-fence: `fence, phi` — the fence fires first and has no region
        Expr::Fence(e) => {
            let fence = EffectSeq::single(ctxt.make_fence());
            let (twp, phi) = synth_expr(e, ctxt)?;
            Ok((twp, fence.then(phi)))
        }

        Expr::While(LocName(name)) => {
            let twp = ctxt.lookup_loc(name)?;
            unify(&twp.ty, &Ty::Ref(Box::new(Ty::Flag)), &mut ctxt.subst)?;
            let wait = EffectSeq::single(ctxt.make_effect(EffectKind::Wait, twp.region));
            Ok((glob_loc_ty(), wait))
        }

        Expr::Set(LocName(name)) => {
            let twp = ctxt.lookup_loc(name)?;
            unify(&twp.ty, &Ty::Ref(Box::new(Ty::Flag)), &mut ctxt.subst)?;
            let flag = EffectSeq::single(ctxt.make_effect(EffectKind::Flag, twp.region));
            Ok((glob_loc_ty(), flag))
        }

        Expr::Check(LocName(name), e1, e2) => {
            let twp = ctxt.lookup_loc(name)?;
            unify(&twp.ty, &Ty::Ref(Box::new(Ty::Flag)), &mut ctxt.subst)?;
            let check = ctxt.make_effect(EffectKind::Check, twp.region);
            let (ty1, phi1) = synth_expr(e1, ctxt)?;
            let (ty2, phi2) = synth_expr(e2, ctxt)?;
            unify(&ty1.ty, &ty2.ty, &mut ctxt.subst)?;
            unify_region(&ty1.region, &ty2.region, &mut ctxt.subst)?;
            Ok((ty1, phi1.branch(Some(check), phi2)))
        }

        // internal form: the read has already fired
        Expr::CheckResidue(_, _, e1, e2) => {
            let (ty1, phi1) = synth_expr(e1, ctxt)?;
            let (ty2, phi2) = synth_expr(e2, ctxt)?;
            unify(&ty1.ty, &ty2.ty, &mut ctxt.subst)?;
            unify_region(&ty1.region, &ty2.region, &mut ctxt.subst)?;
            Ok((ty1, phi1.branch(None, phi2)))
        }

        Expr::Let(name, e1, e2) => {
            let (twp, phi1) = synth_expr(e1, ctxt)?;
            if name.starts_with('l') {
                ctxt.sigma.insert(name.clone(), twp);
            } else {
                ctxt.gamma.insert(name.clone(), twp);
            }
            let (ty2, phi2) = synth_expr(e2, ctxt)?;
            Ok((ty2, phi1.then(phi2)))
        }

        Expr::Var(name) => {
            let twp = ctxt
                .gamma
                .get(name)
                .or_else(|| ctxt.sigma.get(name))
                .cloned()
                .map(|twp| ctxt.subst.apply_twp(&twp))
                .ok_or_else(|| TauRelaxError::TypeError {
                    message: format!("unbound variable: {}", name),
                })?;
            Ok((twp, EffectSeq::Empty))
        }

        // t-val: a runtime form, its region unconstrained
        Expr::Val(v) => {
            let ty = synth_value(v, ctxt)?;
            let region = match v {
                Value::Loc(loc) => loc.region.clone(),
                _ => ctxt.fresh_region_var(),
            };
            Ok((TypeWithPlace { ty, region }, EffectSeq::Empty))
        }
    }
}

pub fn synth_value(value: &Value, ctxt: &mut TypeCheckCtxt) -> Result<Ty, TauRelaxError> {
    match value {
        Value::Int(_) => Ok(Ty::Int),
        Value::Unit => Ok(Ty::Unit),
        Value::Flag(_) => Ok(Ty::Flag),
        // a location value has type `Ref tau` for the contents type tau
        Value::Loc(Location { name, .. }) => {
            let twp = ctxt.lookup_loc(name)?;
            Ok(Ty::Ref(Box::new(twp.ty)))
        }
    }
}
