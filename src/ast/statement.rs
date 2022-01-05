use nom::{
    branch::alt,
    bytes::complete::tag,
    combinator::{cut, map, opt},
    sequence::{preceded, terminated, tuple},
    IResult,
};
use nom::{character::complete::char, multi::many0};

use super::{
    comment::comment_whitespace0,
    expression::{expression, Expression},
    identifier::{consume_keyword, identifier},
    parse::{include_pos, GrammarError, LocatedAst, Span},
};

#[derive(Debug, PartialEq)]
pub enum DeclOrStmt<'a> {
    Decl(LocatedAst<VarDecl<'a>>),
    Stmt(Statement<'a>),
}

pub fn decl_or_stmt(input: Span) -> IResult<Span, DeclOrStmt, GrammarError<Span>> {
    alt((
        map(include_pos(var_decl), |d| DeclOrStmt::Decl(d)),
        map(statement, |s| DeclOrStmt::Stmt(s)),
    ))(input)
}

// declaration    → varDecl | statement ;
#[derive(Debug, PartialEq)]
pub struct VarDecl<'a> {
    pub name: &'a str,
    pub init_expr: Option<LocatedAst<Expression<'a>>>,
}

pub fn var_decl(input: Span) -> IResult<Span, VarDecl, GrammarError<Span>> {
    let (input, _) = consume_keyword("var")(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, name) = cut(identifier)(input)?;
    let (input, init_expr) = opt(preceded(
        tuple((comment_whitespace0, tag("="), comment_whitespace0)),
        cut(expression),
    ))(input)?;
    let (input, _) = tag(";")(input)?;
    let (input, _) = comment_whitespace0(input)?;
    Ok((
        input,
        VarDecl {
            name: name.fragment(),
            init_expr,
        },
    ))
}

#[derive(Debug, PartialEq)]
pub enum Statement<'a> {
    Expr(LocatedAst<Expression<'a>>),
    For(LocatedAst<ForStmt<'a>>),
    If(LocatedAst<IfStmt<'a>>),
    Print(LocatedAst<Expression<'a>>),
    While(LocatedAst<WhileStmt<'a>>),
    Block(LocatedAst<Vec<DeclOrStmt<'a>>>),
}

pub fn statement(input: Span) -> IResult<Span, Statement, GrammarError<Span>> {
    let (input, stmt) = alt((
        map(expr_statement, |expr| Statement::Expr(expr)),
        map(include_pos(for_stmt), |stmt| Statement::For(stmt)),
        map(include_pos(if_stmt), |stmt| Statement::If(stmt)),
        map(print_statement, |expr| Statement::Print(expr)),
        map(include_pos(while_stmt), |stmt| Statement::While(stmt)),
        map(include_pos(block), |block| Statement::Block(block)),
    ))(input)?;
    Ok((input, stmt))
}

#[derive(Debug, PartialEq)]
pub struct IfStmt<'a> {
    pub cond: LocatedAst<Expression<'a>>,
    pub then_branch: Box<Statement<'a>>,
    pub else_branch: Option<Box<Statement<'a>>>,
}

// ifStmt         → "if" "(" expression ")" statement ( "else" statement )? ;
fn if_stmt(input: Span) -> IResult<Span, IfStmt, GrammarError<Span>> {
    let (input, _) = consume_keyword("if")(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, cond) = cut(expression)(input)?;
    let (input, _) = tag(")")(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, then_branch) = cut(statement)(input)?;
    let (input, else_branch) = opt(preceded(
        tuple((consume_keyword("else"), comment_whitespace0)),
        cut(statement),
    ))(input)?;
    Ok((
        input,
        IfStmt {
            cond,
            then_branch: Box::new(then_branch),
            else_branch: else_branch.map(|b| Box::new(b)),
        },
    ))
}

// exprStmt       → expression ";" ;
fn expr_statement(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    terminated(expression, tuple((char(';'), comment_whitespace0)))(input)
}
#[derive(Debug, PartialEq)]
pub struct ForStmt<'a> {
    pub init: Option<Box<DeclOrStmt<'a>>>,
    pub cond: Option<Box<LocatedAst<Expression<'a>>>>,
    pub post: Option<Box<LocatedAst<Expression<'a>>>>,
    pub body: Box<Statement<'a>>,
}
// forStmt        → "for" "(" ( varDecl | exprStmt | ";" ) expression? ";" expression? ")" statement ;
fn for_stmt(input: Span) -> IResult<Span, ForStmt, GrammarError<Span>> {
    let (input, _) = consume_keyword("for")(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, _) = cut(tag("("))(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, init) = alt((
        map(include_pos(var_decl), |d| Some(DeclOrStmt::Decl(d))),
        map(expr_statement, |e| {
            Some(DeclOrStmt::Stmt(Statement::Expr(e)))
        }),
        map(tag(";"), |_| None),
    ))(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, cond) = opt(expression)(input)?;
    let (input, _) = cut(tag(";"))(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, post) = opt(expression)(input)?;
    let (input, _) = cut(tag(")"))(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, body) = cut(statement)(input)?;

    Ok((
        input,
        ForStmt {
            init: init.map(|d| Box::new(d)),
            cond: cond.map(|e| Box::new(e)),
            post: post.map(|e| Box::new(e)),
            body: body.into(),
        },
    ))
}

// printStmt      → "print" expression ";" ;
fn print_statement(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    let (input, _) = consume_keyword("print")(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, expression) = cut(expression)(input)?;
    let (input, _) = cut(tag(";"))(input)?;
    let (input, _) = comment_whitespace0(input)?;
    Ok((input, expression))
}

#[derive(Debug, PartialEq)]
pub struct WhileStmt<'a> {
    pub cond: Box<LocatedAst<Expression<'a>>>,
    pub body: Box<Statement<'a>>,
}

// whileStmt      → "while" "(" expression ")" statement ;
fn while_stmt(input: Span) -> IResult<Span, WhileStmt, GrammarError<Span>> {
    let (input, _) = consume_keyword("while")(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, cond) = cut(expression)(input)?;
    let (input, _) = tag(")")(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, body) = cut(statement)(input)?;
    Ok((
        input,
        WhileStmt {
            cond: Box::new(cond),
            body: Box::new(body),
        },
    ))
}

// block          → "{" declaration* "}" ;
fn block(input: Span) -> IResult<Span, Vec<DeclOrStmt>, GrammarError<Span>> {
    let (input, _) = tag("{")(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, decls) = many0(decl_or_stmt)(input)?;
    let (input, _) = tag("}")(input)?;
    let (input, _) = comment_whitespace0(input)?;
    Ok((input, decls))
}

#[cfg(test)]
mod test {
    use std::error::Error;

    use super::*;
    use crate::ast::{expression::Expression, primary::Literal};

    #[test]
    fn test_var_decl() {
        let (_, token) = var_decl(Span::new("var x = 1;")).unwrap();
        assert_eq!(token.name, "x");
        let LocatedAst { ast: init_expr, .. } = token.init_expr.unwrap();
        assert_eq!(init_expr, Expression::Literal(Literal::Number(1.0)));
    }

    #[test]
    fn test_print_statement() {
        let (_, res) = print_statement("print\"Hello, world!\"; // Hello, world!".into()).unwrap();
        assert_eq!(
            res.ast,
            Expression::Literal(Literal::String("Hello, world!".to_string()))
        );
        print_statement("print1".into()).unwrap_err();
    }

    #[test]
    fn test_expr_statement() -> Result<(), Box<dyn Error>> {
        let (_, res) = expr_statement("1;".into())?;
        assert_eq!(res.ast, Expression::Literal(Literal::Number(1.0)));
        Ok(())
    }
}
