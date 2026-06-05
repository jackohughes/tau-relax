use crate::ast::{Value, Expr, Program, Region, LocName, global_region};
use crate::types::{Ty, TypeWithPlace, Effect, EffectBar, EffectKind, EffectSeq};
use crate::safety::{check_safety_sc};
use crate::substitution::{Substitution, unify};
use crate::error::TauRelaxError;


pub type TypeEnv = std::collections::HashMap<String, TypeWithPlace>;

pub type StoreTyping = std::collections::HashMap<String, TypeWithPlace>;

pub struct TypeCheckCtxt { 
    pub gamma: TypeEnv, 
    pub sigma: StoreTyping, 
    pub subst: Substitution,
    pub region_counter: usize,
    pub effect_counter: usize, 
    pub thread_id: usize, 
    pub type_var_counter: usize,
}

impl TypeCheckCtxt { 
    pub fn new() -> Self {
        TypeCheckCtxt { 
            gamma: TypeEnv::new(),
            sigma: StoreTyping::new(), 
            subst: Substitution::new(),
            region_counter: 0,
            effect_counter: 0,
            thread_id: 0,
            type_var_counter: 0,
        }
    }

    pub fn lookup_loc(&self, name: &str) -> Result<TypeWithPlace, TauRelaxError> {
        self.sigma.get(name)
            .cloned()
            .map(|twp| self.subst.apply_twp(&twp))
            .ok_or_else(|| TauRelaxError::TypeError {
                message: format!("unbound location: {}", name)
            })
    }


    pub fn fresh_region(&mut self) -> Region {
        let n = self.region_counter;
        self.region_counter += 1;
        Region(format!("r{}", n))
    }

    pub fn fresh_type_var(&mut self) -> Ty { 
        let n = self.type_var_counter;
        self.type_var_counter += 1; 
        Ty::Var(format!("a{}", n))
    }

    pub fn fresh_effect_index(&mut self) -> usize {
        let n = self.effect_counter; 
        self.effect_counter += 1; 
        n
    }

    pub fn make_effect(
        &mut self, 
        kind : EffectKind,
        region: Region
    ) -> Effect {
        Effect {
            kind, 
            region,
            index : self.fresh_effect_index(),
        }
    }

    pub fn zonk(&self, ty: &Ty) -> Ty { 
        self.subst.apply(ty)
    }

    pub fn zonk_twp(&self, twp: &TypeWithPlace) -> TypeWithPlace {
        self.subst.apply_twp(twp)
    }
}

pub fn check_program(
    program: &Program,
    ctxt: &mut TypeCheckCtxt
) -> Result<(), TauRelaxError> {

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

    let mut effects_per_thread = EffectBar::new();

    for (tid, thread_expr) in program.threads.iter().enumerate(){
        let mut thread_ctxt = TypeCheckCtxt { 
            gamma: ctxt.gamma.clone(),
            sigma: ctxt.sigma.clone(),
            subst: ctxt.subst.clone(),
            region_counter: ctxt.region_counter, 
            effect_counter: 0, 
            thread_id: tid,
            type_var_counter: 0,
        }; 
        let (_, phi) = synth_expr(thread_expr, &mut  thread_ctxt)?; 
        ctxt.subst = thread_ctxt.subst;
        effects_per_thread.push(phi); 
    }

    println!("type check ok");
    check_safety_sc(&preamble_effects, &effects_per_thread, true)
}

pub fn check_expr(
    expr: &Expr,
    expected: &TypeWithPlace,
    ctxt: &mut TypeCheckCtxt
) -> Result<EffectSeq, TauRelaxError> {
    match expr {
        Expr::Assign(LocName(name), e) => {
            let twp = ctxt.lookup_loc(name)?;
            let inner_ty = ctxt.fresh_type_var();
            unify(&twp.ty, &Ty::Ref(Box::new(inner_ty.clone())), &mut ctxt.subst)?;
            let region = twp.region.clone();
            let rhs_phi = check_expr(
                e,
                &TypeWithPlace {
                    ty: ctxt.subst.apply(&inner_ty),
                    region: region.clone(),
                },
                ctxt,
            )?;
            let write = ctxt.make_effect(EffectKind::Write, region);
            Ok(rhs_phi.then(EffectSeq::single(write)))
        }
        _ => {
            let (ty, phi) = synth_expr(expr, ctxt)?;
            unify(&ty.ty, &expected.ty, &mut ctxt.subst)?;
            Ok(phi)
        } 
    }
}

pub fn synth_expr(
    expr: &Expr,
    ctxt: &mut TypeCheckCtxt
) -> Result<(TypeWithPlace, EffectSeq), TauRelaxError> {
    match expr { 
        Expr::Skip => {
            Ok((TypeWithPlace { ty : Ty::Unit, region : global_region() }, EffectSeq::Empty))
        }
        Expr::NewRgn => {
            let fresh_reg = ctxt.fresh_region(); 
            let effect1 = ctxt.make_effect(EffectKind::New, fresh_reg.clone());
            let effect2 = ctxt.make_effect(EffectKind::Write, fresh_reg.clone());
            let phi = EffectSeq::single(effect1).then(EffectSeq::single(effect2));
            Ok((TypeWithPlace { ty: Ty::Unit, region : fresh_reg.clone() }, phi))
        }
        Expr::FreeRgn(e) => {
            let (TypeWithPlace { region, .. }, mut phi) = synth_expr(e, ctxt)?; 
            let free = ctxt.make_effect(EffectKind::Free, region.clone());
            Ok((TypeWithPlace { ty : Ty::Unit, region : global_region()}, phi.then(EffectSeq::Single(free))))
        }
        Expr::Ref(e) => {
            let (TypeWithPlace { ty, region }, mut phi) = synth_expr(e, ctxt)?;
            let loc_name = format!("loc_{}", ctxt.fresh_effect_index());
            let result_ty = TypeWithPlace {
                ty: Ty::Ref(Box::new(ty)),
                region: region.clone()
            };
            // add the new location to sigma
            ctxt.sigma.insert(loc_name.clone(), result_ty.clone());
            let effect = ctxt.make_effect(EffectKind::Write, region);
            let (TypeWithPlace { ty, region }, phi) = synth_expr(e, ctxt)?;
            let write = ctxt.make_effect(EffectKind::Write, region.clone());
            Ok((result_ty, phi.then(EffectSeq::single(write))))
        }
        Expr::Deref(e) => {
            let (TypeWithPlace { ty, region }, mut phi) = synth_expr(e, ctxt)?;
            let inner_ty = ctxt.fresh_type_var();
            unify(&ty, &Ty::Ref(Box::new(inner_ty.clone())), &mut ctxt.subst)?;
            let read = EffectSeq::single(ctxt.make_effect(EffectKind::Read, region.clone()));
            Ok((TypeWithPlace { ty: ctxt.subst.apply(&inner_ty), region }, phi.then(read)))
        }
        Expr::Seq(e1, e2) => {
            let phi1 = check_expr(e1, &TypeWithPlace { ty : Ty::Unit, region: global_region() }, ctxt)?;
            let (ty, phi2) = synth_expr(e2, ctxt)?; 
            Ok((ty, phi1.then(phi2)))
        }
        Expr::WriteAt(e1, e2) => {
            let (TypeWithPlace { ty, .. }, mut phi1) = synth_expr(e1, ctxt)?;
            let (TypeWithPlace { region, .. }, phi2) = synth_expr(e2, ctxt)?;
            let phi = phi1.then(phi2).then(EffectSeq::single(
                ctxt.make_effect(EffectKind::Write, region.clone())));
            Ok((TypeWithPlace { ty, region }, phi))
        }
        Expr::Fence(e) => {
            let (twp, phi) = synth_expr(e, ctxt)?;
            let fence = EffectSeq::single(ctxt.make_effect(EffectKind::Fence, twp.region.clone()));
            Ok((twp, phi.then(fence)))
        }
        Expr::While(LocName(name)) => {
            let twp = ctxt.lookup_loc(name)?;
            unify(&twp.ty, &Ty::Ref(Box::new(Ty::Flag)), &mut ctxt.subst)?;
            let wait = EffectSeq::single(ctxt.make_effect(EffectKind::Wait, twp.region));
            Ok((TypeWithPlace { ty: Ty::Unit, region: global_region() }, wait))
        }
        Expr::Set(LocName(name)) => {
            let twp = ctxt.lookup_loc(name)?;
            unify(&twp.ty, &Ty::Ref(Box::new(Ty::Flag)), &mut ctxt.subst)?;
            let flag = EffectSeq::single(ctxt.make_effect(EffectKind::Flag, twp.region));
            Ok((TypeWithPlace { ty: Ty::Unit, region: global_region() }, flag))
        }
        Expr::Val(val) => {
            let ty = synth_value(val, ctxt)?;
            let region = match val {
                Value::Loc(loc) => loc.region.clone(),
                _ => global_region(),
            };
            Ok((TypeWithPlace { ty, region}, EffectSeq::Empty))
        }
        Expr::WhilePrime(_, _) => {
            Err(TauRelaxError::TypeError {
                message: "WhilePrime is an internal form and should not appear in source programs".to_string()
            })
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
            let twp = ctxt.gamma.get(name)
                .or_else(|| ctxt.sigma.get(name))
                .cloned()
                .map(|twp| ctxt.subst.apply_twp(&twp))
                .ok_or_else(|| TauRelaxError::TypeError {
                    message: format!("unbound variable: {}", name)
                })?;
            Ok((twp, EffectSeq::Empty))
        }
        Expr::Check(LocName(name), e1, e2) => {
            let twp = ctxt.lookup_loc(name)?;
            unify(&twp.ty, &Ty::Ref(Box::new(Ty::Flag)), &mut ctxt.subst)?;
            let (ty1, phi1) = synth_expr(e1, ctxt)?;
            let (ty2, phi2) = synth_expr(e2, ctxt)?;
            unify(&ty1.ty, &ty2.ty, &mut ctxt.subst)?;
            let read = EffectSeq::single(ctxt.make_effect(EffectKind::Read, twp.region));
            Ok((ty1, read.then(phi1.branch(phi2))))
        }
        _ => {
            todo!()  
        }
    }
}

pub fn synth_value(
    value: &Value, 
    ctxt: &mut TypeCheckCtxt
) -> Result<Ty, TauRelaxError> {
    match value { 
        Value::Int(_) => Ok(Ty::Int),
        Value::Unit => Ok(Ty::Unit),
        Value::Zero => Ok(Ty::Flag),
        Value::Loc(loc) => {
            match ctxt.sigma.get(&loc.name) {
                Some(twp) => Ok(ctxt.subst.apply(&twp.ty)),
                None => {
                    let fresh = ctxt.fresh_type_var();
                    ctxt.sigma.insert(
                    loc.name.clone(),
                    TypeWithPlace {
                        ty: fresh.clone(),
                        region: loc.region.clone(),
                    },
                );
                Ok(fresh)
                }
            }
        }
    }
}