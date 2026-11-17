//! The suite is a directory of `.trx` files, one case per file.
//!
//! Each file carries its expectation in a header of `--` comments. The lexer
//! skips those, so a case file is also a program `tau-relax` will run on its
//! own, and the expectation travels with the program rather than sitting in a
//! table somewhere else.
//!
//! ```text
//! -- name:   a flag set through := is still a set
//! -- expect: reject
//! -- known:  EffectKind::Write reads as leaving the flag clear, so ...
//! ```
//!
//! `expect` is required. `name` defaults to the file stem, which is also the
//! id `--test <name>` matches on. `known` records a deviation the checker is
//! known to have: a case carrying one is reported but does not fail the run.
//! `model` pins the case to one memory model, for a case whose point is a
//! relaxed execution; without one the case follows `--model`.

use std::path::Path;

use crate::driver::{self, Verdict};
use crate::options::Options;
use crate::safety::Model;

use Verdict::*;

pub struct Case {
    /// The file stem, and the handle for `--test <id>`.
    pub id: String,
    pub name: String,
    pub source: String,
    pub expected: Verdict,
    pub known: Option<String>,
    /// The model this case is pinned to, if any.
    pub model: Option<Model>,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Outcome {
    /// Agreed with the expectation, as it should.
    Pass,
    /// Disagreed, and the disagreement is recorded.
    KnownFail,
    /// Agreed despite a recorded deviation: drop the `known` line.
    Fixed,
    /// Disagreed with nothing to explain it.
    Fail,
}
use Outcome::*;

// ------------------------------------------------------------- loading

/// Read the leading `--` comment block for directives. Scanning stops at the
/// first line that is neither blank nor a comment, so a `-- expect:` further
/// down in the body is left alone.
type Header = (String, Verdict, Option<String>, Option<Model>);

fn parse_header(id: &str, source: &str) -> Result<Header, String> {
    let mut name: Option<String> = None;
    let mut expect: Option<Verdict> = None;
    let mut known: Vec<String> = Vec::new();
    let mut model: Option<Model> = None;

    for line in source.lines() {
        let t = line.trim();
        if t.is_empty() {
            continue;
        }
        let Some(rest) = t.strip_prefix("--") else {
            break;
        };
        let rest = rest.trim();
        let Some((key, value)) = rest.split_once(':') else {
            continue;
        };
        let value = value.trim().to_string();
        match key.trim() {
            "name" => name = Some(value),
            "known" => known.push(value),
            "model" => {
                model =
                    Some(Model::parse(&value).ok_or_else(|| {
                        format!("{}: `-- model: {}` should be sc or tso", id, value)
                    })?)
            }
            "expect" => {
                expect = Some(match value.to_ascii_lowercase().as_str() {
                    "accept" | "accepted" => Accepted,
                    "reject" | "rejected" => Rejected,
                    other => {
                        return Err(format!(
                            "{}: `-- expect: {}` should be accept or reject",
                            id, other
                        ));
                    }
                })
            }
            _ => {}
        }
    }

    let expected = expect.ok_or_else(|| {
        format!(
            "{}: no `-- expect: accept` or `-- expect: reject` header",
            id
        )
    })?;

    Ok((
        name.unwrap_or_else(|| id.to_string()),
        expected,
        if known.is_empty() {
            None
        } else {
            Some(known.join(" "))
        },
        model,
    ))
}

/// The `-- model:` pin of a source file, for a file run directly rather than
/// as part of the suite.
pub fn pinned_model(source: &str) -> Option<Model> {
    for line in source.lines() {
        let t = line.trim();
        if t.is_empty() {
            continue;
        }
        let rest = t.strip_prefix("--")?;
        if let Some((key, value)) = rest.trim().split_once(':') {
            if key.trim() == "model" {
                return Model::parse(value.trim());
            }
        }
    }
    None
}

/// Every `.trx` file in `dir`, in file-name order.
pub fn load_cases(dir: &Path) -> Result<Vec<Case>, String> {
    let entries =
        std::fs::read_dir(dir).map_err(|e| format!("cannot read {}: {}", dir.display(), e))?;

    let mut paths: Vec<_> = entries
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "trx"))
        .collect();
    paths.sort();

    if paths.is_empty() {
        return Err(format!("no .trx files in {}", dir.display()));
    }

    let mut cases = Vec::new();
    for path in paths {
        let id = path
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_else(|| path.display().to_string());
        let source = std::fs::read_to_string(&path)
            .map_err(|e| format!("cannot read {}: {}", path.display(), e))?;
        let (name, expected, known, model) = parse_header(&id, &source)?;
        cases.push(Case {
            id,
            name,
            source,
            expected,
            known,
            model,
        });
    }
    Ok(cases)
}

// -------------------------------------------------------------- running

pub fn run_case(case: &Case, opts: &Options) -> Outcome {
    println!("\n======== {} ({}) ========", case.name, case.id);

    let opts = match case.model {
        Some(model) => Options {
            model,
            ..opts.clone()
        },
        None => opts.clone(),
    };

    let verdict = match driver::analyse(&case.id, &case.source, &opts) {
        Ok(v) => v,
        Err(msg) => {
            eprintln!("{}", msg);
            println!(
                "{}: FAIL (expected {:?}, did not parse)",
                case.id, case.expected
            );
            return Fail;
        }
    };

    let outcome = match (verdict == case.expected, &case.known) {
        (true, None) => Pass,
        (true, Some(_)) => Fixed,
        (false, Some(_)) => KnownFail,
        (false, None) => Fail,
    };

    match outcome {
        Pass => println!("{}: PASS ({:?})", case.id, verdict),
        Fail => println!(
            "{}: FAIL (expected {:?}, got {:?})",
            case.id, case.expected, verdict
        ),
        KnownFail => println!(
            "{}: XFAIL (expected {:?}, got {:?})\n  {}",
            case.id,
            case.expected,
            verdict,
            case.known.as_deref().unwrap_or("")
        ),
        Fixed => println!(
            "{}: XPASS (expected {:?} and got it; the recorded deviation is gone, \
             so remove the `-- known:` line)",
            case.id, case.expected
        ),
    }

    outcome
}

fn matches(case: &Case, filter: &str) -> bool {
    let f = filter.to_ascii_lowercase();
    case.id.to_ascii_lowercase().contains(&f) || case.name.to_ascii_lowercase().contains(&f)
}

/// Run the suite, or the cases matching `filter`. True when nothing failed
/// unexpectedly.
pub fn run_suite(filter: Option<&str>, opts: &Options) -> bool {
    let all = match load_cases(&opts.tests_dir) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("tau-relax: {}", e);
            eprintln!("Use --tests <DIR> to point at the case directory.");
            return false;
        }
    };

    let selected: Vec<&Case> = match filter {
        None => all.iter().collect(),
        Some(f) => all.iter().filter(|c| matches(c, f)).collect(),
    };

    if selected.is_empty() {
        eprintln!(
            "tau-relax: no case in {} matches {:?}. Known cases:",
            opts.tests_dir.display(),
            filter.unwrap_or("")
        );
        for c in &all {
            eprintln!("    {:<22} {}", c.id, c.name);
        }
        return false;
    }

    let outcomes: Vec<Outcome> = selected.iter().map(|c| run_case(c, opts)).collect();
    let count = |o: Outcome| outcomes.iter().filter(|x| **x == o).count();
    let (pass, xfail, fixed, fail) = (count(Pass), count(KnownFail), count(Fixed), count(Fail));

    println!(
        "\n======== {} passed, {} known deviations ========",
        pass, xfail
    );
    if fixed > 0 {
        println!(
            "{} case(s) no longer deviate; remove their `-- known:` lines",
            fixed
        );
    }
    if fail > 0 {
        println!("{} unexplained failure(s)", fail);
    }

    fail == 0
}
