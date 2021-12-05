use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::digit1,
    combinator::{cut, map, opt, recognize, value},
    error::context,
    sequence::{terminated, tuple},
    IResult,
};
use nom::{
    bytes::complete::{escaped_transform, is_not},
    character::complete::char,
    sequence::preceded,
};
use nom_locate::position;

use super::{
    comment::comment_whitespace0,
    identifier::identifier,
    parse::{GrammarError, GrammarErrorKind, LocatedAst, Span},
};

#[derive(Debug, PartialEq)]
pub enum Expression<'a> {
    Literal(Literal),
    Unary(Unary<'a>),
    Binary(Binary<'a>),
    Grouping(Box<LocatedAst<Expression<'a>>>),
    Variable(&'a str),
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
pub fn expression(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    include_equality(input)
}

#[derive(Debug, PartialEq)]
pub struct Binary<'a> {
    pub left: Box<LocatedAst<Expression<'a>>>,
    pub op: Operator,
    pub right: Box<LocatedAst<Expression<'a>>>,
}

fn include_equality(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    let (input, pos) = position(input)?;
    let (input, left) = include_comparison(input)?;
    let (input, op) = opt(alt((
        map(tag("=="), |_| -> Operator { Operator::Equal }),
        map(tag("!="), |_| -> Operator { Operator::NotEqual }),
    )))(input)?;
    if let Some(op) = op {
        let (input, _) = comment_whitespace0(input)?;
        let (input, right) = cut(include_equality)(input)?;
        let expr = Expression::Binary(Binary {
            left: Box::new(left),
            op,
            right: Box::new(right),
        });
        Ok((input, LocatedAst::new(pos, expr)))
    } else {
        Ok((input, left))
    }
}

fn include_comparison(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
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
        let branch = Expression::Binary(Binary {
            left: Box::new(left),
            op,
            right: Box::new(right),
        });
        Ok((input, LocatedAst::new(pos, branch)))
    } else {
        Ok((input, left))
    }
}

fn include_term(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    let (input, pos) = position(input)?;
    let (input, left) = include_factor(input)?;
    let (input, op) = opt(alt((
        map(char('+'), |_| -> Operator { Operator::Add }),
        map(char('-'), |_| -> Operator { Operator::Subtract }),
    )))(input)?;
    if let Some(op) = op {
        let (input, _) = comment_whitespace0(input)?;
        let (input, right) = cut(include_term)(input)?;
        let branch = Expression::Binary(Binary {
            left: Box::new(left),
            op,
            right: Box::new(right),
        });
        Ok((input, LocatedAst::new(pos, branch)))
    } else {
        Ok((input, left))
    }
}
fn include_factor(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    let (input, pos) = position(input)?;
    let (input, left) = include_unary(input)?;
    let (input, op) = opt(alt((
        map(char('*'), |_| -> Operator { Operator::Multiply }),
        map(char('/'), |_| -> Operator { Operator::Divide }),
    )))(input)?;
    if let Some(op) = op {
        let (input, _) = comment_whitespace0(input)?;
        let (input, right) = cut(include_factor)(input)?;
        let branch = Expression::Binary(Binary {
            left: Box::new(left),
            op,
            right: Box::new(right),
        });
        Ok((input, LocatedAst::new(pos, branch)))
    } else {
        Ok((input, left))
    }
}

fn include_unary(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    let (input, pos) = position(input)?;
    match map(unary, |u| Expression::Unary(u))(input) {
        Ok((input, unary)) => Ok((input, LocatedAst::new(pos, unary))),
        Err(_) => include_primary(input),
    }
}

fn include_primary(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    let (input, pos) = position(input)?;
    let (input, expr) = alt((
        map(grouping, |g| Expression::Grouping(g)),
        map(literal, |l| Expression::Literal(l)),
        map(identifier, |v| Expression::Variable(v.fragment())),
    ))(input)?;
    Ok((input, LocatedAst::new(pos, expr)))
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

fn literal(input: Span) -> IResult<Span, Literal, GrammarError<Span>> {
    terminated(
        alt((
            map(number, |n| -> Literal { Literal::Number(n) }),
            map(string, |s| -> Literal { Literal::String(s) }),
            map(tag("true"), |_| -> Literal { Literal::True }),
            map(tag("false"), |_| -> Literal { Literal::False }),
            map(tag("nil"), |_| -> Literal { Literal::Nil }),
        )),
        comment_whitespace0,
    )(input)
}

fn number(input: Span) -> IResult<Span, f64, GrammarError<Span>> {
    map(
        recognize(tuple((digit1, opt(tuple((char('.'), digit1)))))),
        |s: Span| s.fragment().parse::<f64>().unwrap(),
    )(input)
}

fn string(input: Span) -> IResult<Span, String, GrammarError<Span>> {
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
    let (input, _) = char::<Span, nom::error::Error<Span>>('"')(input).map_err(|e| {
        nom::Err::Failure(GrammarError {
            input: match e {
                nom::Err::Error(e) => e.input,
                nom::Err::Failure(e) => e.input,
                nom::Err::Incomplete(_) => unreachable!(),
            },
            error_kind: GrammarErrorKind::Grammar("Unterminated string."),
        })
    })?;
    Ok((input, s.unwrap_or("".to_string())))
}

// unary          → ( "-" | "!" ) expression ;
#[derive(Debug, PartialEq)]
pub enum Unary<'a> {
    Negative(Box<LocatedAst<Expression<'a>>>),
    Not(Box<LocatedAst<Expression<'a>>>),
}

fn unary(input: Span) -> IResult<Span, Unary, GrammarError<Span>> {
    context(
        "unary",
        alt((
            map(preceded(tag("-"), cut(expression)), |e| {
                Unary::Negative(Box::new(e))
            }),
            map(preceded(tag("!"), cut(expression)), |e| {
                Unary::Not(Box::new(e))
            }),
        )),
    )(input)
}

// grouping       → "(" expression ")" ;
fn grouping(input: Span) -> IResult<Span, Box<LocatedAst<Expression>>, GrammarError<Span>> {
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

    use super::*;
    #[test]
    fn test_string() {
        let (_, res) = string("\"hello\"".into()).unwrap();
        assert_eq!(res, "hello");
        let (_, res) = string("\"\"".into()).unwrap();
        assert_eq!(res, "");
        let (_, res) = string("\"\\\\\"".into()).unwrap();
        assert_eq!(res, "\\");
        let err = match string("\"this string has no close quote".into()).unwrap_err() {
            nom::Err::Failure(e) => e,
            _ => panic!("Expected failure"),
        };
        assert_eq!(
            err.error_kind,
            GrammarErrorKind::Grammar("Unterminated string."),
        );
    }

    #[test]
    fn test_literal() -> Result<(), Box<dyn Error>> {
        let (_, res) = literal("1".into())?;
        assert_eq!(res, Literal::Number(1.0));
        let (_, res) = literal("\"hello\"".into())?;
        assert_eq!(res, Literal::String("hello".to_string()));
        let (_, res) = literal("true".into())?;
        assert_eq!(res, Literal::True);
        let (_, res) = literal("false".into())?;
        assert_eq!(res, Literal::False);
        let (_, res) = literal("nil".into())?;
        assert_eq!(res, Literal::Nil);
        Ok(())
    }

    #[test]
    fn test_grouping() -> Result<(), Box<dyn Error>> {
        let (_, res) = grouping("(1 + 2)".into())?;
        if let Expression::Binary(bin) = res.ast {
            assert_eq!(bin.left.ast, Expression::Literal(Literal::Number(1.0)));
            assert_eq!(bin.right.ast, Expression::Literal(Literal::Number(2.0)));
            assert_eq!(bin.op, Operator::Add);
            Ok(())
        } else {
            Err("not binary".into())
        }
    }

    #[test]
    fn test_pos() {
        let (_, res) = expression("1-2".into()).unwrap();
        assert_eq!(res.get_line(), 1);
        // let bin = match res.branch {
        //     Expression::Binary(bin) => bin,
        //     _ => panic!("not binary"),
        // };
        // let one = match bin.right.branch {
        //     Expression::Unary(Unary::Negative(Expression { pos, branch:Expression::Literal(l) })) => u,

        // }
        // assert_eq!(
        //     bin.right.branch,
        //     Expression::Unary(Unary::Negative(Literal::Number(1.0)))
        // );
        // assert_eq!(
        //     ,
        //     Ok((
        //         "",
        //         Expression::Binary(Binary {
        //             left: Box::new(Expression::Grouping(Box::new(Expression::Binary(Binary {
        //                 left: Box::new(Expression::Literal(Literal::Number(5.0))),
        //                 op: Operator::Subtract,
        //                 right: Box::new(Expression::Grouping(Box::new(Expression::Binary(
        //                     Binary {
        //                         left: Box::new(Expression::Literal(Literal::Number(3.0))),
        //                         op: Operator::Subtract,
        //                         right: Box::new(Expression::Literal(Literal::Number(1.0)))
        //                     }
        //                 ))))
        //             })))),
        //             op: Operator::Add,
        //             right: Box::new(Expression::Unary(Unary::Negative(Box::new(
        //                 Expression::Literal(Literal::Number(1.0))
        //             ))))
        //         })
        //     ))
        // );
    }
}
