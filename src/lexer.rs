use logos::Logos;

#[derive(Logos, Debug, PartialEq, Eq, Clone, Hash)]
#[logos(skip r"--[^\n]*")]        // skip -- line comments
#[logos(skip r"[ \t\n\f\r]+")]    // skip whitespace
pub enum Token {
    // ---- Keywords ----
    #[token("let")]     Let,
    #[token("in")]      In,
    #[token("newrgn")]  NewRgn,
    #[token("freergn")] FreeRgn,
    #[token("ref")]     Ref,
    #[token("while")]   While,
    #[token("then")]    Then,
    #[token("skip")]    Skip,
    #[token("set")]     Set,
    #[token("at")]      At,
    #[token("begin")]   Begin,
    #[token("end")]     End,
    #[token("fence")]   Fence,
    #[token("unset")] Unset,
    #[token("isset")] IsSet,
    #[token("check")] Check,
    #[token("else")]  Else,


    // ---- Operators ----
    #[token(":=")] ColonEq,
    #[token("!")]  Bang,
    #[token(";")]  Semicolon,
    #[token("||")] Par,
    #[token("=")]  Equals,
    #[token("(")]  LParen,
    #[token(")")]  RParen,

    #[token("()")] Unit,
    #[regex("[0-9]+", |lex| lex.slice().parse::<i64>().ok())]
    Int(i64),

    #[regex("l[a-zA-Z0-9_]+", |lex| lex.slice().to_string())]
    LocIdent(String),

    #[regex("[a-zA-Z][a-zA-Z0-9_]*", |lex| lex.slice().to_string())]
    Ident(String),
}

pub fn lex(source: &str) -> Result<Vec<Token>, String> {
    Token::lexer(source)
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| "lexer error: unrecognised token".to_string())
}