use nom::{
    branch::alt,
    bytes::complete::tag,
    combinator::{cut, map, opt, value},
    error::{context, ContextError, ParseError},
    number::complete::double,
    sequence::terminated,
    IResult,
};
use nom::{
    bytes::complete::{escaped_transform, is_not},
    character::complete::char,
    sequence::preceded,
};
use nom_locate::position;

use super::{comment::comment_whitespace0, parse::Span};

#[derive(Debug, PartialEq)]
pub struct Expression<'a> {
    pub pos: Span<'a>,
    pub branch: ExprBranch<'a>,
}

#[derive(Debug, PartialEq)]
pub enum ExprBranch<'a> {
    Literal(Literal),
    Unary(Unary<'a>),
    Binary(Binary<'a>),
    Grouping(Box<Expression<'a>>),
}

/// going from lowest to highest.
///
/// Name|	Operators|	Associates
/// ---|---|---
/// Equality|	== !=	|Left
/// Comparison|	> >= < <=	|Left
/// Term|	- +	|Left
/// Factor|	/ *	|Left
/// Unary|	! -	|Right
pub fn expression<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, Expression, E> {
    include_equality(input)
}

#[derive(Debug, PartialEq)]
pub struct Binary<'a> {
    pub left: Box<Expression<'a>>,
    pub op: Operator,
    pub right: Box<Expression<'a>>,
}

fn include_equality<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, Expression, E> {
    let (input, pos) = position(input)?;
    let (input, left) = include_comparison(input)?;
    let (input, op) = opt(alt((
        map(tag("=="), |_| -> Operator { Operator::Equal }),
        map(tag("!="), |_| -> Operator { Operator::NotEqual }),
    )))(input)?;
    if let Some(op) = op {
        let (input, _) = comment_whitespace0(input)?;
        let (input, right) = cut(include_equality)(input)?;
        let branch = ExprBranch::Binary(Binary {
            left: Box::new(left),
            op,
            right: Box::new(right),
        });
        Ok((input, Expression { pos, branch }))
    } else {
        Ok((input, left))
    }
}

fn include_comparison<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, Expression, E> {
    let (input, pos) = position(input)?;
    let (input, left) = include_term(input)?;
    let (input, op) = opt(alt((
        map(char('<'), |_| -> Operator { Operator::Less }),
        map(tag("<="), |_| -> Operator { Operator::LessEqual }),
        map(char('>'), |_| -> Operator { Operator::Greater }),
        map(tag(">="), |_| -> Operator { Operator::GreaterEqual }),
    )))(input)?;
    if let Some(op) = op {
        let (input, _) = comment_whitespace0(input)?;
        let (input, right) = cut(include_comparison)(input)?;
        let branch = ExprBranch::Binary(Binary {
            left: Box::new(left),
            op,
            right: Box::new(right),
        });
        Ok((input, Expression { pos, branch }))
    } else {
        Ok((input, left))
    }
}

fn include_term<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, Expression, E> {
    let (input, pos) = position(input)?;
    let (input, left) = include_factor(input)?;
    let (input, op) = opt(alt((
        map(char('+'), |_| -> Operator { Operator::Add }),
        map(char('-'), |_| -> Operator { Operator::Subtract }),
    )))(input)?;
    if let Some(op) = op {
        let (input, _) = comment_whitespace0(input)?;
        let (input, right) = cut(include_term)(input)?;
        let branch = ExprBranch::Binary(Binary {
            left: Box::new(left),
            op,
            right: Box::new(right),
        });
        Ok((input, Expression { pos, branch }))
    } else {
        Ok((input, left))
    }
}
fn include_factor<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, Expression, E> {
    let (input, pos) = position(input)?;
    let (input, left) = include_unary(input)?;
    let (input, op) = opt(alt((
        map(char('*'), |_| -> Operator { Operator::Multiply }),
        map(char('/'), |_| -> Operator { Operator::Divide }),
    )))(input)?;
    if let Some(op) = op {
        let (input, _) = comment_whitespace0(input)?;
        let (input, right) = cut(include_factor)(input)?;
        let branch = ExprBranch::Binary(Binary {
            left: Box::new(left),
            op,
            right: Box::new(right),
        });
        Ok((input, Expression { pos, branch }))
    } else {
        Ok((input, left))
    }
}

fn include_unary<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, Expression, E> {
    let (input, pos) = position(input)?;
    let (input, branch) = alt((
        map(unary, |u| ExprBranch::Unary(u)),
        map(grouping, |g| ExprBranch::Grouping(g)),
        map(literal, |l| ExprBranch::Literal(l)),
    ))(input)?;
    Ok((input, Expression { pos, branch }))
}

// literal        → NUMBER | STRING | "true" | "false" | "nil" ;
#[derive(Debug, PartialEq)]
pub enum Literal {
    Number(f64),
    String(String),
    True,
    False,
    Nil,
}

fn literal<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, Literal, E> {
    terminated(
        alt((
            map(double, |n| -> Literal { Literal::Number(n) }),
            map(string, |s| -> Literal { Literal::String(s) }),
            map(tag("true"), |_| -> Literal { Literal::True }),
            map(tag("false"), |_| -> Literal { Literal::False }),
            map(tag("nil"), |_| -> Literal { Literal::Nil }),
        )),
        comment_whitespace0,
    )(input)
}

fn string<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, String, E> {
    let (input, _) = char('"')(input)?;
    let (input, s) = opt(escaped_transform(
        is_not("\\\"\n"),
        '\\',
        alt((
            value("\\", tag("\\")),
            value("\"", tag("\"")),
            value("\n", tag("n")),
        )),
    ))(input)?;
    let (input, _) = char('"')(input)?;
    return Ok((input, s.unwrap_or("".to_string())));
}

type Number = f64;

// unary          → ( "-" | "!" ) expression ;
#[derive(Debug, PartialEq)]
pub enum Unary<'a> {
    Negative(Box<Expression<'a>>),
    Not(Box<Expression<'a>>),
}

fn unary<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, Unary, E> {
    context(
        "unary",
        alt((
            map(preceded(tag("-"), cut(expression)), |e| -> Unary {
                Unary::Negative(Box::new(e))
            }),
            map(preceded(tag("!"), cut(expression)), |e| -> Unary {
                Unary::Not(Box::new(e))
            }),
        )),
    )(input)
}

// grouping       → "(" expression ")" ;
fn grouping<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, Box<Expression>, E> {
    let (input, _) = char('(')(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, e) = context("group expression", cut(expression))(input)?;
    let (input, _) = char(')')(input)?;
    let (input, _) = comment_whitespace0(input)?;
    Ok((input, Box::new(e)))
}

// operator       → "==" | "!=" | "<" | "<=" | ">" | ">=" | "+"  | "-"  | "*" | "/" ;
#[derive(Debug, PartialEq)]
pub enum Operator {
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Add,
    Subtract,
    Multiply,
    Divide,
}

#[cfg(test)]
mod test {
    use std::error::Error;

    use nom::error::ErrorKind;

    use super::*;
    #[test]
    fn test_string() -> Result<(), Box<dyn Error>> {
        let (_, res) = string::<(Span, ErrorKind)>("\"hello\"".into())?;
        assert_eq!(res, "hello".to_string());
        let (_, res) = string::<(Span, ErrorKind)>(r#""""#.into())?;
        assert_eq!(res, "".to_string());
        let (_, res) = string::<(Span, ErrorKind)>("\"\"\"".into())?;
        assert_eq!(res, "".to_string());
        Ok(())
    }

    #[test]
    fn test_literal() -> Result<(), Box<dyn Error>> {
        let (_, res) = literal::<(Span, ErrorKind)>("1".into())?;
        assert_eq!(res, Literal::Number(1.0));
        let (_, res) = literal::<(Span, ErrorKind)>("\"hello\"".into())?;
        assert_eq!(res, Literal::String("hello".to_string()));
        let (_, res) = literal::<(Span, ErrorKind)>("true".into())?;
        assert_eq!(res, Literal::True);
        let (_, res) = literal::<(Span, ErrorKind)>("false".into())?;
        assert_eq!(res, Literal::False);
        let (_, res) = literal::<(Span, ErrorKind)>("nil".into())?;
        assert_eq!(res, Literal::Nil);
        Ok(())
    }

    #[test]
    fn test_grouping() -> Result<(), Box<dyn Error>> {
        let (_, res) = grouping::<(Span, ErrorKind)>("(1 + 2)".into())?;
        if let ExprBranch::Binary(bin) = res.branch {
            assert_eq!(bin.left.branch, ExprBranch::Literal(Literal::Number(1.0)));
            assert_eq!(bin.right.branch, ExprBranch::Literal(Literal::Number(2.0)));
            assert_eq!(bin.op, Operator::Add);
            Ok(())
        } else {
            Err("not binary".into())
        }
    }

    #[test]
    fn test_expression() {
        // let (_, res) = expression("(5 - (3 - 1)) + -1 ".into())?;
        // let bin = match res.branch {
        //     ExprBranch::Binary(bin) => bin,
        //     _ => panic!("not binary"),
        // };
        // let one = match bin.right.branch {
        //     ExprBranch::Unary(Unary::Negative(Expression { pos, branch:ExprBranch::Literal(l) })) => u,

        // }
        // assert_eq!(
        //     bin.right.branch,
        //     ExprBranch::Unary(Unary::Negative(Literal::Number(1.0)))
        // );
        // assert_eq!(
        //     ,
        //     Ok((
        //         "",
        //         ExprBranch::Binary(Binary {
        //             left: Box::new(ExprBranch::Grouping(Box::new(ExprBranch::Binary(Binary {
        //                 left: Box::new(ExprBranch::Literal(Literal::Number(5.0))),
        //                 op: Operator::Subtract,
        //                 right: Box::new(ExprBranch::Grouping(Box::new(ExprBranch::Binary(
        //                     Binary {
        //                         left: Box::new(ExprBranch::Literal(Literal::Number(3.0))),
        //                         op: Operator::Subtract,
        //                         right: Box::new(ExprBranch::Literal(Literal::Number(1.0)))
        //                     }
        //                 ))))
        //             })))),
        //             op: Operator::Add,
        //             right: Box::new(ExprBranch::Unary(Unary::Negative(Box::new(
        //                 ExprBranch::Literal(Literal::Number(1.0))
        //             ))))
        //         })
        //     ))
        // );
    }
}
