use crate::checker::{check_program, TypeCheckCtxt};
use crate::interpreter::{run_sc, Env};
use crate::parser::parse;

/// Unsynchronised: one thread writes while the other frees. Unsafe.
const EXAMPLE_1: &str = "
    let r = newrgn in
    let lx = ref 0 at r in
    begin
      lx := 42
      ||
      freergn r
    end
";

/// Message passing: the free waits on a flag the writer sets. Safe.
const EXAMPLE_2: &str = "
    let r = newrgn in
    let lx = ref 0 at r in
    let lflag = ref unset at r in
    begin
      lx := 42; set(lflag)
      ||
      while (!lflag = unset) then skip; freergn r
    end
";

/// Dekker-shaped: each thread announces intent, then checks the other's
/// flag; only the thread that sees the other unset proceeds to free.
/// Safe under SC, unsafe under TSO.
const EXAMPLE_3: &str = "
    let r = newrgn in
    let l1 = ref unset at r in
    let l2 = ref unset at r in
    begin
      set(l1); check l2 then l1 := unset else freergn r
      ||
      set(l2); check l1 then l2 := unset else freergn r
    end
";

fn run(name: &str, source: &str) {
    println!("\n======== {} ========", name);
    let program = match parse(source) {
        Ok(p) => p,
        Err(errs) => {
            eprintln!("parse failed:");
            for e in errs {
                eprintln!("  {}", e);
            }
            return;
        }
    };
    let mut ctxt = TypeCheckCtxt::new();
    match check_program(&program, &mut ctxt) {
        Ok(_) => println!("{}: accepted", name),
        Err(e) => {
            println!("{}: rejected — {:?}", name, e);
            return;
        }
    }

    // the preamble is run as a prefix of every thread, so that its
    // bindings are in scope; a proper implementation would run it once
    // and share the resulting environment.
    let mut threads = Vec::new();
    for t in &program.threads {
        let mut e = t.clone();
        for (name, bound) in program.preamble.iter().rev() {
            e = crate::ast::Expr::Let(name.clone(), Box::new(bound.clone()), Box::new(e));
        }
        threads.push(e);
    }

    match run_sc(threads, Env::new(), 10_000) {
        Ok(cfg) => {
            println!("{}: ran to completion", name);
            for (i, th) in cfg.threads.iter().enumerate() {
                println!("  thread {} -> {:?}", i, th.expr);
            }
            // the surviving store: freed regions have no bindings left
            let mut keys: Vec<_> = cfg.mem.store.keys().collect();
            keys.sort();
            for k in keys {
                println!("  {} = {:?}", k, cfg.mem.store[k]);
            }
        }
        Err(e) => println!("{}: runtime error — {:?}", name, e),
    }
}

pub fn test_example() {
    run("example 1 (unsynchronised)", EXAMPLE_1);
    run("example 2 (message passing)", EXAMPLE_2);
    run("example 3 (Dekker)", EXAMPLE_3);
}