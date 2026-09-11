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

/// The same shape as EXAMPLE_3, but with each entry flag in its own region,
/// which is how `fig:dekker` in the paper writes it. Effects are
/// region-granular, so when both flags live in `r` the `rb` cycle that rules
/// out the double free is already closed inside a single thread; here it is a
/// genuinely cross-thread cycle
/// `flag_1 < read_1 < flag_2 < read_2 < flag_1`, so this is the example that
/// exercises coherence and reads-before. Safe under SC.
const EXAMPLE_4: &str = "
    let r = newrgn in
    let r1 = newrgn in
    let r2 = newrgn in
    let l1 = ref unset at r1 in
    let l2 = ref unset at r2 in
    begin
      set(l1); check l2 then l1 := unset else freergn r
      ||
      set(l2); check l1 then l2 := unset else freergn r
    end
";

/// EXAMPLE_4 with thread 1's announcement removed. Thread 2's check can now
/// never observe a flag on r1, so it always takes the else branch, and nothing
/// stops thread 1 taking its else branch too: a double free. Unsafe.
const EXAMPLE_5: &str = "
    let r = newrgn in
    let r1 = newrgn in
    let r2 = newrgn in
    let l1 = ref unset at r1 in
    let l2 = ref unset at r2 in
    begin
      check l2 then l1 := unset else freergn r
      ||
      set(l2); check l1 then l2 := unset else freergn r
    end
";

#[derive(Debug, PartialEq, Clone, Copy)]
enum Verdict {
    Accepted,
    Rejected,
}
use Verdict::*;

fn run(name: &str, source: &str, expected: Verdict) -> bool {
    println!("\n======== {} ========", name);
    let program = match parse(source) {
        Ok(p) => p,
        Err(errs) => {
            eprintln!("parse failed:");
            for e in errs {
                eprintln!("  {}", e);
            }
            println!("{}: FAIL (expected {:?}, did not parse)", name, expected);
            return false;
        }
    };
    let mut ctxt = TypeCheckCtxt::new();
    let verdict = match check_program(&program, &mut ctxt) {
        Ok(_) => {
            println!("{}: accepted", name);
            Accepted
        }
        Err(e) => {
            println!("{}: rejected — {}", name, describe(&e));
            Rejected
        }
    };
    let ok = verdict == expected;
    println!(
        "{}: {} (expected {:?}, got {:?})",
        name,
        if ok { "PASS" } else { "FAIL" },
        expected,
        verdict
    );
    if verdict == Rejected {
        return ok;
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
        // The preamble is re-run per thread (see above), so `newrgn` fires
        // once per thread and the second one is rejected. Pre-existing, and
        // unrelated to the verdict above.
        Err(e) => println!("  (interpreter: {})", describe(&e)),
    }
    ok
}

fn describe(e: &crate::error::TauRelaxError) -> String {
    use crate::error::TauRelaxError::*;
    match e {
        TypeError { message } | SafetyError { message } | RuntimeError { message } => {
            message.clone()
        }
    }
}

pub fn test_example() {
    let results = vec![
        run("example 1 (unsynchronised)", EXAMPLE_1, Rejected),
        run("example 2 (message passing)", EXAMPLE_2, Accepted),
        run("example 3 (Dekker, one region)", EXAMPLE_3, Accepted),
        run(
            "example 4 (Dekker, split flag regions)",
            EXAMPLE_4,
            Accepted,
        ),
        run("example 5 (Dekker, one flag missing)", EXAMPLE_5, Rejected),
    ];
    let passed = results.iter().filter(|r| **r).count();
    println!("\n======== {}/{} passed ========", passed, results.len());
}
