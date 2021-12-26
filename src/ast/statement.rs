use nom::{
    branch::alt,
    bytes::complete::tag,
    combinator::{cut, map, opt},
    sequence::{preceded, terminated, tuple},
    IResult,
};
use nom::{character::complete::char, multi::many0};

use nom_locate::position;

use super::{
    comment::comment_whitespace0,
    expression::{expression, Expression},
    identifier::{consume_keyword, identifier},
    parse::{GrammarError, LocatedAst, Span},
};

#[derive(Debug, PartialEq)]
pub enum DeclOrStmt<'a> {
    Decl(VarDecl<'a>),
    Stmt(Statement<'a>),
}

pub fn decl_or_stmt(input: Span) -> IResult<Span, LocatedAst<DeclOrStmt>, GrammarError<Span>> {
    alt((
        map(var_decl, |l| l.map(|d| DeclOrStmt::Decl(d))),
        map(statement, |l| l.map(|s| DeclOrStmt::Stmt(s))),
    ))(input)
}

// declaration    → varDecl | statement ;
#[derive(Debug, PartialEq)]
pub struct VarDecl<'a> {
    pub name: &'a str,
    pub init_expr: Option<LocatedAst<Expression<'a>>>,
}

pub fn var_decl(input: Span) -> IResult<Span, LocatedAst<VarDecl>, GrammarError<Span>> {
    let (input, pos) = position(input)?;
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
        LocatedAst::new(
            pos,
            VarDecl {
                name: name.fragment(),
                init_expr,
            },
        ),
    ))
}

#[derive(Debug, PartialEq)]
pub enum Statement<'a> {
    Expr(LocatedAst<Expression<'a>>),
    If(IfStmt<'a>),
    Print(LocatedAst<Expression<'a>>),
    Block(Vec<LocatedAst<DeclOrStmt<'a>>>),
}

// statement      → exprStmt | ifStmt | printStmt | block ;
pub fn statement(input: Span) -> IResult<Span, LocatedAst<Statement>, GrammarError<Span>> {
    let (input, pos) = position(input)?;
    let (input, stmt) = alt((
        map(expr_statement, |expr| Statement::Expr(expr)),
        map(if_stmt, |stmt| Statement::If(stmt)),
        map(print_statement, |expr| Statement::Print(expr)),
        map(block, |block| Statement::Block(block)),
    ))(input)?;
    Ok((input, LocatedAst::new(pos, stmt)))
}

#[derive(Debug, PartialEq)]
pub struct IfStmt<'a> {
    pub cond: LocatedAst<Expression<'a>>,
    pub then_branch: Box<LocatedAst<Statement<'a>>>,
    pub else_branch: Option<Box<LocatedAst<Statement<'a>>>>,
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

// printStmt      → "print" expression ";" ;
fn print_statement(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    let (input, _) = consume_keyword("print")(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, expression) = cut(expression)(input)?;
    let (input, _) = cut(tag(";"))(input)?;
    let (input, _) = comment_whitespace0(input)?;
    Ok((input, expression))
}

// block          → "{" declaration* "}" ;
fn block(input: Span) -> IResult<Span, Vec<LocatedAst<DeclOrStmt>>, GrammarError<Span>> {
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
        let (_, LocatedAst { ast: token, .. }) = var_decl(Span::new("var x = 1;")).unwrap();
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
