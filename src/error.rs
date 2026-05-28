use miette::Diagnostic;
use thiserror::Error;

#[derive(Debug, Error, Diagnostic)]
pub enum TauRelaxError {
    #[error("type error: {message}")]
    TypeError { message: String },

    #[error("safety violation: {message}")]
    SafetyError { message: String },

    #[error("runtime error: {message}")]
    RuntimeError { message: String },
}