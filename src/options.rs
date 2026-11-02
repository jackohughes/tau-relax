//! Run-time options, threaded explicitly rather than read from the
//! environment, so that a test case and a file on the command line are
//! analysed under exactly the same settings.

use std::path::PathBuf;

use crate::safety::Model;

#[derive(Debug, Clone)]
pub struct Options {
    /// Print the events, the candidate sets and the generated constraint.
    pub debug: bool,
    /// Run the interpreter after a program is accepted.
    pub run: bool,
    /// The memory model the safety condition is evaluated against.
    pub model: Model,
    /// Where `--test` looks for `.trx` cases.
    pub tests_dir: PathBuf,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            debug: false,
            run: true,
            model: Model::SC,
            tests_dir: PathBuf::from("tests"),
        }
    }
}