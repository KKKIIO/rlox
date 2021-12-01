use nom::character::complete::char;
use nom::{
    branch::alt,
    bytes::complete::tag,
    combinator::{cut, map},
    error::{ContextError, ParseError},
    sequence::{terminated, tuple},
    IResult,
};

use nom_locate::position;

use crate::ast::expression::Literal;

use super::{
    comment::comment_whitespace0,
    expression::{expression, ExprBranch, Expression},
    parse::Span,
};

#[derive(Debug, PartialEq)]
pub struct Statement<'a> {
    pub pos: Span<'a>,
    pub branch: StmtBranch<'a>,
}

#[derive(Debug, PartialEq)]
pub enum StmtBranch<'a> {
    Expression(Expression<'a>),
    Print(Expression<'a>),
}

// statement      → exprStmt | printStmt ;
pub fn statement<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, Statement, E> {
    let (input, pos) = position(input)?;
    let (input, branch) = alt((
        map(expr_statement, |expression| {
            StmtBranch::Expression(expression)
        }),
        map(print_statement, |print_statement| {
            StmtBranch::Print(print_statement)
        }),
    ))(input)?;
    Ok((input, Statement { pos, branch }))
}

// exprStmt       → expression ";" ;
fn expr_statement<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, Expression, E> {
    terminated(expression, tuple((char(';'), comment_whitespace0)))(input)
}

// printStmt      → "print" expression ";" ;
fn print_statement<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, Expression, E> {
    let (input, _) = tag("print")(input)?;
    let (input, ws) = comment_whitespace0(input)?;
    if ws.is_empty() {
        return Err(nom::Err::Error(E::from_error_kind(
            input,
            nom::error::ErrorKind::MultiSpace,
        )));
    }
    let (input, expression) = cut(expression)(input)?;
    let (input, _) = cut(tag(";"))(input)?;
    let (input, _) = comment_whitespace0(input)?;
    Ok((input, expression))
}

#[cfg(test)]
mod test {
    use std::error::Error;

    use nom::error::ErrorKind;

    use super::*;
    #[test]
    fn test_print_statement() {
        let (_, res) = print_statement::<nom::error::Error<Span>>(
            "print \"Hello, world!\"; // Hello, world!".into(),
        )
        .unwrap();
        let expected = ExprBranch::Literal(Literal::String("Hello, world!".to_string()));
        assert_eq!(res.branch, expected);
        print_statement::<nom::error::Error<Span>>("print1".into()).unwrap_err();
    }

    #[test]
    fn test_expr_statement() -> Result<(), Box<dyn Error>> {
        let (_, res) = expr_statement::<(Span, ErrorKind)>("1;".into())?;
        assert_eq!(res.branch, ExprBranch::Literal(Literal::Number(1.0)));
        Ok(())
    }
}
