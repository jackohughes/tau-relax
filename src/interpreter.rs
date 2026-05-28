use crate::ast::Expr;
use crate::error::TauRelaxError;

pub type Store = std::collections::HashMap<String, crate::ast::Value>;

/// Run a well-typed program under SC semantics
pub fn run_sc(
    expr: &Expr,
    store: &mut Store,
) -> Result<crate::ast::Value, TauRelaxError> {
    todo!()
}