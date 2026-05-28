#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Region(pub String);

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
    Unit,
    Zero,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Val(Value),
    Var(String), 
    NewRgn,
    FreeRgn(Box<Expr>),
    Ref(Box<Expr>),
    Deref(Box<Expr>),
    Assign(LocName, Box<Expr>),
    Seq(Box<Expr>, Box<Expr>),
    WriteAt(Box<Expr>, Box<Expr>), 
    Let(String, Box<Expr>, Box<Expr>),
    Fence(Box<Expr>),
    While(LocName),
    WhilePrime(LocName, i64),
    Set(LocName),
    Skip,
}

pub struct Program {
    pub preamble: Vec<(String, Expr)>,
    pub threads: Vec<Expr>,
}

pub fn global_region() -> Region {
    Region("glob".to_string())
} 