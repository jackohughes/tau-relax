use chumsky::prelude::*;
use crate::lexer::Token;
use crate::ast::*;

fn ident_parser() -> impl Parser<Token, String, Error = Simple<Token>> {
    select! { Token::Ident(s) => s }
}

fn loc_ident_parser() -> impl Parser<Token, String, Error = Simple<Token>> {
    select! { Token::LocIdent(s) => s }
}

fn any_ident_parser() -> impl Parser<Token, String, Error = Simple<Token>> {
    select! {
        Token::Ident(s) => s,
        Token::LocIdent(s) => s,
    }
}

/// Values: the contents a `ref` may be initialised with.
fn value_parser() -> impl Parser<Token, Value, Error = Simple<Token>> + Clone {
    just(Token::Unit).map(|_| Value::Unit)
        .or(just(Token::Unset).map(|_| Value::Flag(false)))
        .or(just(Token::IsSet).map(|_| Value::Flag(true)))
        .or(select! { Token::Int(n) => Value::Int(n) })
        .boxed()
}

fn atom_parser() -> impl Parser<Token, Expr, Error = Simple<Token>> + Clone {
    // site ids are placeholders here; `number_sites` assigns them after parsing
    just(Token::NewRgn).map(|_| Expr::NewRgn(0))
        .or(value_parser().map(Expr::Val))
        .or(just(Token::While)
            .ignore_then(just(Token::LParen))
            .ignore_then(just(Token::Bang))
            .ignore_then(loc_ident_parser())
            .then_ignore(just(Token::Equals))
            .then_ignore(just(Token::Unset))
            .then_ignore(just(Token::RParen))
            .then_ignore(just(Token::Then))
            .then_ignore(just(Token::Skip))
            .map(|loc| Expr::While(LocName(loc))))
        .or(just(Token::Set)
            .ignore_then(just(Token::LParen))
            .ignore_then(loc_ident_parser())
            .then_ignore(just(Token::RParen))
            .map(|loc| Expr::Set(LocName(loc))))
        .or(loc_ident_parser().map(Expr::Var))
        .or(ident_parser().map(Expr::Var))
        .boxed()
}

pub fn expr_parser() -> impl Parser<Token, Expr, Error = Simple<Token>> {
    recursive(|expr| {
        let atom = atom_parser();

        let paren = expr.clone()
            .delimited_by(just(Token::LParen), just(Token::RParen));

        let let_expr = just(Token::Let)
            .ignore_then(any_ident_parser())
            .then_ignore(just(Token::Equals))
            .then(expr.clone())
            .then_ignore(just(Token::In))
            .then(expr.clone())
            .map(|((name, e1), e2)| Expr::Let(name, Box::new(e1), Box::new(e2)));

        let check_expr = just(Token::Check)
            .ignore_then(loc_ident_parser())
            .then_ignore(just(Token::Then))
            .then(expr.clone())
            .then_ignore(just(Token::Else))
            .then(expr.clone())
            .map(|((loc, e1), e2)| {
                Expr::Check(LocName(loc), Box::new(e1), Box::new(e2))
            });

        // `ref v at e` is one production: the single allocation form
        let ref_expr = just(Token::Ref)
            .ignore_then(value_parser())
            .then_ignore(just(Token::At))
            .then(atom.clone())
            .map(|(v, e)| Expr::RefAt(0, v, Box::new(e)));

        let freergn_expr = just(Token::FreeRgn)
            .ignore_then(atom.clone())
            .map(|e| Expr::FreeRgn(Box::new(e)));

        let deref_expr = just(Token::Bang)
            .ignore_then(atom.clone())
            .map(|e| Expr::Deref(Box::new(e)));

        let fence_expr = just(Token::Fence)
            .ignore_then(atom.clone())
            .map(|e| Expr::Fence(Box::new(e)));

        // Everything except top-level `;` sequencing and assignment. This is
        // what the right-hand side of an assignment may be, so that
        // `lx := 42; set(lflag)` parses as `(lx := 42); set(lflag)` and not as
        // `lx := (42; set(lflag))`, which would emit the two effects in the
        // wrong order.
        let operand = ref_expr
            .or(freergn_expr)
            .or(deref_expr)
            .or(fence_expr)
            .or(let_expr)
            .or(paren)
            .or(check_expr)
            .or(atom.clone())
            .boxed();

        // `atom` matches a bare location name, so the assignment production
        // has to be tried first or `lx := e` would parse as just `lx`.
        let assign = loc_ident_parser()
            .then_ignore(just(Token::ColonEq))
            .then(operand.clone())
            .map(|(name, e)| Expr::Assign(LocName(name), Box::new(e)));

        let unary = assign.or(operand);

        unary
            .then(just(Token::Semicolon).ignore_then(expr.clone()).or_not())
            .map(|(e1, e2)| match e2 {
                Some(e2) => Expr::Seq(Box::new(e1), Box::new(e2)),
                None => e1,
            })
    })
}

fn preamble_parser() -> impl Parser<Token, Vec<(String, Expr)>, Error = Simple<Token>> {
    just(Token::Let)
        .ignore_then(any_ident_parser())
        .then_ignore(just(Token::Equals))
        .then(expr_parser())
        .then_ignore(just(Token::In))
        .repeated()
}

fn thread_parser() -> impl Parser<Token, Vec<Expr>, Error = Simple<Token>> {
    expr_parser().separated_by(just(Token::Par)).at_least(1)
}

pub fn parser() -> impl Parser<Token, Program, Error = Simple<Token>> {
    preamble_parser()
        .then_ignore(just(Token::Begin))
        .then(thread_parser())
        .then_ignore(just(Token::End))
        .map(|(preamble, threads)| Program { preamble, threads })
}

pub fn parse(source: &str) -> Result<Program, Vec<String>> {
    use crate::lexer::lex;

    let tokens = lex(source).map_err(|e| vec![e])?;
    let mut program = match parser().parse(tokens) {
        Ok(p) => p,
        Err(errs) => {
            return Err(errs.iter().map(|e| format!("{:?}", e)).collect());
        }
    };
    // assign a distinct identifier to every allocation site
    number_sites(&mut program);
    Ok(program)
}