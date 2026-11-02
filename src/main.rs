mod ast;
mod checker;
mod cli;
mod constraints;
mod driver;
mod effects;
mod error;
mod interpreter;
mod lexer;
mod options;
mod parser;
mod pretty;
mod safety;
mod substitution;
mod tests;
mod types;

use std::process::ExitCode;

use cli::{Command, USAGE};
use driver::Verdict;

fn main() -> ExitCode {
    let invocation = match cli::parse(std::env::args().skip(1)) {
        Ok(i) => i,
        Err(msg) => {
            eprintln!("tau-relax: {}", msg);
            eprintln!("\nTry `tau-relax --help`.");
            return ExitCode::from(2);
        }
    };

    let opts = invocation.options;

    match invocation.command {
        Command::Help => {
            print!("{}", USAGE);
            ExitCode::SUCCESS
        }

        Command::Version => {
            println!("tau-relax {}", env!("CARGO_PKG_VERSION"));
            ExitCode::SUCCESS
        }

        Command::Run { path } => {
            let source = match std::fs::read_to_string(&path) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("tau-relax: cannot read {}: {}", path.display(), e);
                    return ExitCode::from(2);
                }
            };
            let name = path
                .file_name()
                .map(|s| s.to_string_lossy().into_owned())
                .unwrap_or_else(|| path.display().to_string());

            match driver::analyse(&name, &source, &opts) {
                Err(msg) => {
                    eprintln!("{}", msg);
                    ExitCode::from(2)
                }
                Ok(Verdict::Accepted) => ExitCode::SUCCESS,
                Ok(Verdict::Rejected) => ExitCode::FAILURE,
            }
        }

        Command::Test { filter } => {
            if tests::run_suite(filter.as_deref(), &opts) {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            }
        }
    }
}