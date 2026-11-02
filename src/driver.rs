//! The analysis pipeline, shared by the file path and the test path so that
//! both go through exactly the same stages in the same order.

use crate::ast::{Expr, Program};
use crate::checker::{check_program, TypeCheckCtxt};
use crate::error::TauRelaxError;
use crate::interpreter::{run_sc, Config, Env};
use crate::options::Options;
use crate::parser::parse;

/// Interpreter step budget. A program that blocks forever on a flag will
/// exhaust it, which is not a failure, so this only has to be large enough
/// that a terminating program finishes.
const FUEL: usize = 10_000;

/// What the checker decided about a program.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Verdict {
    Accepted,
    Rejected,
}

pub fn describe(e: &TauRelaxError) -> String {
    use TauRelaxError::*;
    match e {
        TypeError { message } | SafetyError { message } | RuntimeError { message } => {
            message.clone()
        }
    }
}

/// Parse. Errors come back as a list because the parser reports several.
pub fn compile(source: &str) -> Result<Program, Vec<String>> {
    parse(source)
}

/// Type-check, check the per-thread lifecycle, and discharge the safety
/// condition. `Ok` is the accepting verdict.
pub fn check(program: &Program, opts: &Options) -> Result<(), TauRelaxError> {
    let mut ctxt = TypeCheckCtxt::new();
    check_program(program, &mut ctxt, opts)
}

/// Interpret an accepted program.
///
/// The preamble is run as a prefix of every thread so that its bindings are in
/// scope. That means `newrgn` fires once per thread and every thread after the
/// first is rejected by the subsystem, which is a known wart of the harness
/// rather than a property of the program: a proper implementation would run
/// the preamble once and share the resulting environment.
pub fn interpret(program: &Program, _opts: &Options) -> Result<Config, TauRelaxError> {
    let mut threads = Vec::new();
    for t in &program.threads {
        let mut e = t.clone();
        for (name, bound) in program.preamble.iter().rev() {
            e = Expr::Let(name.clone(), Box::new(bound.clone()), Box::new(e));
        }
        threads.push(e);
    }
    run_sc(threads, Env::new(), FUEL)
}

/// Print the surviving store and each thread's residual expression.
pub fn report_run(cfg: &Config) {
    for (i, th) in cfg.threads.iter().enumerate() {
        println!("  thread {} -> {:?}", i, th.expr);
    }
    let mut keys: Vec<_> = cfg.mem.store.keys().collect();
    keys.sort();
    if keys.is_empty() {
        println!("  (store empty: every region was freed)");
    }
    for k in keys {
        println!("  {} = {:?}", k, cfg.mem.store[k]);
    }
}

/// The whole pipeline for one named source. Returns the verdict, having
/// printed whatever the options call for.
pub fn analyse(name: &str, source: &str, opts: &Options) -> Result<Verdict, String> {
    let program = match compile(source) {
        Ok(p) => p,
        Err(errs) => {
            let mut msg = format!("{}: parse failed", name);
            for e in errs {
                msg.push_str(&format!("\n  {}", e));
            }
            return Err(msg);
        }
    };

    match check(&program, opts) {
        Err(e) => {
            println!("{}: rejected", name);
            println!("  {}", describe(&e));
            Ok(Verdict::Rejected)
        }
        Ok(()) => {
            println!("{}: accepted", name);
            if opts.run {
                match interpret(&program, opts) {
                    Ok(cfg) => {
                        println!("{}: ran to completion", name);
                        report_run(&cfg);
                    }
                    Err(e) => println!("  (interpreter: {})", describe(&e)),
                }
            }
            Ok(Verdict::Accepted)
        }
    }
}