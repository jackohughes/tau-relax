use std::path::PathBuf;

use crate::options::Options;
use crate::safety::Model;

#[derive(Debug)]
pub enum Command {
    /// Check a source file and, unless `--no-run`, interpret it.
    Run {
        path: PathBuf,
    },
    /// Run the built-in suite, optionally narrowed to cases matching a name.
    Test {
        filter: Option<String>,
    },
    Help,
    Version,
}

#[derive(Debug)]
pub struct Invocation {
    pub command: Command,
    pub options: Options,
    /// Whether `--model` was given, so that a file carrying a `-- model:`
    /// header can be overridden from the command line but not silently.
    pub model_given: bool,
}

pub const USAGE: &str = "\
tau-relax - a type-and-effect checker for race-type-safety

USAGE
    tau-relax <FILE.trx>          check a program, then interpret it
    tau-relax --test [NAME]       run every case in the tests directory, or
                                  those whose name or id contains NAME
    tau-relax --help
    tau-relax --version

OPTIONS
    -d, --debug        print the events, the reads-from candidates and the
                       constraint handed to the solver
        --no-run       check only; do not interpret an accepted program
        --tests <DIR>  where --test looks for .trx cases (default: tests)
        --model <M>    sc (default) or tso

A CASE FILE
    A .trx file under the tests directory, carrying its expectation in a
    header of -- comments, which the lexer skips:

        -- name:   Dekker, split flag regions
        -- expect: accept
        -- model:  tso
        -- known:  <why the checker currently disagrees, if it does>

    `expect` is required; `name` defaults to the file stem, which is the id
    --test matches on. A case with a `known` line is reported but does not
    fail the run. `model` pins the case to one model, so that a case about a
    relaxed execution is checked under that model whatever --model says; a
    case without one follows --model.

EXAMPLES
    tau-relax tests/example_4.trx
    tau-relax --test
    tau-relax --test example_1
    tau-relax --test dead_wait --debug
";

pub fn parse<I: IntoIterator<Item = String>>(args: I) -> Result<Invocation, String> {
    let mut options = Options::default();
    let mut command: Option<Command> = None;
    let mut positional: Option<PathBuf> = None;
    let mut model_given = false;

    let mut it = args.into_iter().peekable();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "-h" | "--help" => return ok(Command::Help, options, model_given),
            "-V" | "--version" => return ok(Command::Version, options, model_given),

            // `-test` is accepted alongside `--test`; it is a common slip and
            // there is no short flag it could be confused with.
            "-t" | "--test" | "-test" => {
                // A following bare word is the filter; a following flag is not.
                let filter = match it.peek() {
                    Some(next) if !next.starts_with('-') => it.next(),
                    _ => None,
                };
                command = Some(Command::Test { filter });
            }

            "-d" | "--debug" => options.debug = true,
            "--no-run" => options.run = false,

            "--tests" => {
                let d = it.next().ok_or("--tests needs a directory")?;
                options.tests_dir = PathBuf::from(d);
            }

            "--model" => {
                let m = it.next().ok_or("--model needs a name")?;
                match Model::parse(&m) {
                    Some(model) => {
                        options.model = model;
                        model_given = true;
                    }
                    None => return Err(format!("--model: unknown model {}", m)),
                }
            }

            other if other.starts_with('-') => return Err(format!("unknown option {}", other)),

            path => {
                if positional.is_some() {
                    return Err("only one file may be given".to_string());
                }
                positional = Some(PathBuf::from(path));
            }
        }
    }

    match (command, positional) {
        (Some(Command::Test { .. }), Some(p)) => Err(format!(
            "--test takes a case name, not a file; did you mean `tau-relax {}`?",
            p.display()
        )),
        (Some(c), None) => ok(c, options, model_given),
        (None, Some(path)) => ok(Command::Run { path }, options, model_given),
        (None, None) => ok(Command::Help, options, model_given),
        (Some(c), Some(_)) => ok(c, options, model_given),
    }
}

fn ok(command: Command, options: Options, model_given: bool) -> Result<Invocation, String> {
    Ok(Invocation {
        command,
        options,
        model_given,
    })
}
