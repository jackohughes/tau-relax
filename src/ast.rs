pub type SiteId = usize;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Region {
    Named(String),
    Var(usize),
}

impl Region {
    pub fn name(&self) -> String {
        match self {
            Region::Named(s) => s.clone(),
            Region::Var(n) => format!("?r{}", n),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct LocName(pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Location {
    pub name: String,
    pub region: Region,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Loc(Location),
    Int(i64),
    /// `unset` is `Flag(false)`, `set` is `Flag(true)`.
    Flag(bool),
    Unit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Var(String),
    /// Values are runtime forms: a source program writes them only as the
    /// contents of a `ref`, but they arise as the result of a dereference.
    Val(Value),

    NewRgn(SiteId),
    FreeRgn(Box<Expr>),
    /// `ref v at e` — the single allocation form. The region comes from `e`.
    RefAt(SiteId, Value, Box<Expr>),

    Deref(Box<Expr>),
    Assign(LocName, Box<Expr>),
    Seq(Box<Expr>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
    Fence(Box<Expr>),

    While(LocName),
    Set(LocName),
    Check(LocName, Box<Expr>, Box<Expr>),
    /// Internal form: the residue of a `check` after its read has fired.
    CheckResidue(LocName, Value, Box<Expr>, Box<Expr>),
}

pub struct Program {
    pub preamble: Vec<(String, Expr)>,
    pub threads: Vec<Expr>,
}

pub fn global_region() -> Region {
    Region::Named("glob".to_string())
}

pub fn number_sites(program: &mut Program) {
    let mut next: SiteId = 0;
    for (_, e) in program.preamble.iter_mut() {
        number_expr(e, &mut next);
    }
    for e in program.threads.iter_mut() {
        number_expr(e, &mut next);
    }
}

fn number_expr(e: &mut Expr, next: &mut SiteId) {
    match e {
        Expr::NewRgn(id) => {
            *id = *next;
            *next += 1;
        }
        Expr::RefAt(id, _, inner) => {
            *id = *next;
            *next += 1;
            number_expr(inner, next);
        }
        Expr::FreeRgn(inner)
        | Expr::Deref(inner)
        | Expr::Fence(inner)
        | Expr::Assign(_, inner) => number_expr(inner, next),
        Expr::Seq(a, b) | Expr::Let(_, a, b) => {
            number_expr(a, next);
            number_expr(b, next);
        }
        Expr::Check(_, a, b) | Expr::CheckResidue(_, _, a, b) => {
            number_expr(a, next);
            number_expr(b, next);
        }
        Expr::Var(_) | Expr::Val(_) | Expr::While(_) | Expr::Set(_) => {}
    }
}

/// Collect the allocation sites of an expression, in order.
pub fn sites(e: &Expr, out: &mut Vec<(SiteId, bool)>) {
    match e {
        // (id, is_region_site)
        Expr::NewRgn(id) => out.push((*id, true)),
        Expr::RefAt(id, _, inner) => {
            out.push((*id, false));
            sites(inner, out);
        }
        Expr::FreeRgn(inner)
        | Expr::Deref(inner)
        | Expr::Fence(inner)
        | Expr::Assign(_, inner) => sites(inner, out),
        Expr::Seq(a, b) | Expr::Let(_, a, b) => {
            sites(a, out);
            sites(b, out);
        }
        Expr::Check(_, a, b) | Expr::CheckResidue(_, _, a, b) => {
            sites(a, out);
            sites(b, out);
        }
        Expr::Var(_) | Expr::Val(_) | Expr::While(_) | Expr::Set(_) => {}
    }
}