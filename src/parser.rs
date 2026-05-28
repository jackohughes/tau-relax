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

fn atom_parser() -> impl Parser<Token, Expr, Error = Simple<Token>> + Clone {
    just(Token::NewRgn).map(|_| Expr::NewRgn)
        .or(just(Token::Skip).map(|_| Expr::Skip))
        .or(just(Token::Unit).map(|_| Expr::Val(Value::Unit)))
        .or(just(Token::Unset).map(|_| Expr::Val(Value::Zero)))
        .or(select! { Token::Int(n) => Expr::Val(Value::Int(n)) })
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
        .or(loc_ident_parser()
            .map(|name| Expr::Var(name)))
        .or(ident_parser()
            .map(|name| Expr::Var(name))).boxed()
}


pub fn expr_parser() -> impl Parser<Token, Expr, Error = Simple<Token>> {
    recursive(|expr| {
        let atom = atom_parser();

        let let_expr = just(Token::Let)
            .ignore_then(any_ident_parser())
            .then_ignore(just(Token::Equals))
            .then(expr.clone())
            .then_ignore(just(Token::In))
            .then(expr.clone())
            .map(|((name, e1), e2)| {
                Expr::Let(name, Box::new(e1), Box::new(e2))
            });

        let paren = expr.clone()
            .delimited_by(just(Token::LParen), just(Token::RParen));

        // the assignment/loc-ref case also needs expr
        let loc_expr = loc_ident_parser()
            .then(
                just(Token::ColonEq)
                    .ignore_then(expr.clone())
                    .or_not()
            )
            .map(|(name, rhs)| match rhs {
                Some(e) => Expr::Assign(LocName(name), Box::new(e)),
                None    => Expr::Var(name),
            });

        let primary = atom.clone()
            .or(let_expr)
            .or(paren)
            .or(loc_expr);

        // ref, freergn, deref, fence take atom — no clone of primary needed
        let ref_expr = just(Token::Ref)
            .ignore_then(atom.clone())
            .map(|e| Expr::Ref(Box::new(e)));

        let freergn_expr = just(Token::FreeRgn)
            .ignore_then(atom.clone())
            .map(|e| Expr::FreeRgn(Box::new(e)));

        let deref_expr = just(Token::Bang)
            .ignore_then(atom.clone())
            .map(|e| Expr::Deref(Box::new(e)));

        let fence_expr = just(Token::Fence)
            .ignore_then(atom.clone())
            .map(|e| Expr::Fence(Box::new(e)));

        // primary consumed once here — no clone
        let unary = ref_expr
            .or(freergn_expr)
            .or(deref_expr)
            .or(fence_expr)
            .or(primary);

        let cloned_unary = unary.boxed().clone();

        let write_form = cloned_unary.clone()
            .then(
                just(Token::At)
                    .ignore_then(cloned_unary.clone())
                    .or_not()
            )
            .map(|(e1, e2)| match e2 {
                Some(e2) => Expr::WriteAt(Box::new(e1), Box::new(e2)),
                None     => e1,
            });

        write_form
            .then(
                just(Token::Semicolon)
                    .ignore_then(expr.clone())
                    .or_not()
            )
            .map(|(e1, e2)| match e2 {
                Some(e2) => Expr::Seq(Box::new(e1), Box::new(e2)),
                None     => e1,
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
    expr_parser()
        .separated_by(just(Token::Par))
        .at_least(1)
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
    parser()
        .parse(tokens)
        .map_err(|errs| errs.iter().map(|e| format!("{:?}", e)).collect())
}