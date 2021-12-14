use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{digit1, none_of},
    combinator::{cut, map, opt, peek, recognize, value},
    error::context,
    sequence::tuple,
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
    Assignment(Assignment<'a>),
    Literal(Literal),
    Unary(Unary<'a>),
    Binary(Binary<'a>),
    Grouping(Box<LocatedAst<Expression<'a>>>),
    Variable(&'a str),
}

#[derive(Debug, PartialEq)]
pub struct Assignment<'a> {
    pub id: &'a str,
    pub expr: Box<LocatedAst<Expression<'a>>>,
}

/// going from lowest to highest.
///
/// Name|	Operators|	Associates
/// ---|---|---
/// Assignment|	=	|Right
/// Equality|	== !=	|Left
/// Comparison|	> >= < <=	|Left
/// Term|	- +	|Left
/// Factor|	/ *	|Left
/// Unary|	! -	|Right
pub fn expression(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    include_assignment(input)
}

fn include_assignment(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    let (input, pos) = position(input)?;
    let (input, lhs) = opt(tuple((
        include_equality,
        comment_whitespace0,
        tag("="),
        peek(none_of("=")),
    )))(input)?;
    if let Some((lvalue, _, eq, _)) = lhs {
        if let LocatedAst {
            ast: Expression::Variable(id),
            ..
        } = lvalue
        {
            let (input, _) = comment_whitespace0(input)?;
            let (input, expr) = cut(include_assignment)(input)?;
            let expr = Expression::Assignment(Assignment {
                id,
                expr: Box::new(expr),
            });
            Ok((input, LocatedAst::new(pos, expr)))
        } else {
            Err(nom::Err::Failure(GrammarError {
                error_kind: GrammarErrorKind::Grammar {
                    kind: "Invalid assignment target.",
                    at: Some(eq),
                },
                input,
            }))
        }
    } else {
        include_equality(input)
    }
}

#[derive(Debug, PartialEq)]
pub struct Binary<'a> {
    pub left: Box<LocatedAst<Expression<'a>>>,
    pub op: Operator,
    pub right: Box<LocatedAst<Expression<'a>>>,
}

fn include_equality(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    let (input, pos) = position(input)?;
    let (mut input, mut left) = include_comparison(input)?;
    loop {
        let op: Option<Operator>;
        (input, op) = opt(alt((
            map(tag("=="), |_| -> Operator { Operator::Equal }),
            map(tag("!="), |_| -> Operator { Operator::NotEqual }),
        )))(input)?;
        if let Some(op) = op {
            input = comment_whitespace0(input)?.0;
            let right: LocatedAst<Expression>;
            (input, right) = cut(include_comparison)(input)?;
            left = LocatedAst::new(
                pos.clone(),
                Expression::Binary(Binary {
                    left: Box::new(left),
                    op,
                    right: Box::new(right),
                }),
            );
        } else {
            break Ok((input, left));
        }
    }
}

fn include_comparison(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    let (input, pos) = position(input)?;
    let (mut input, mut left) = include_term(input)?;
    loop {
        let op: Option<Operator>;
        (input, op) = opt(alt((
            map(tag("<="), |_| -> Operator { Operator::LessEqual }),
            map(char('<'), |_| -> Operator { Operator::Less }),
            map(tag(">="), |_| -> Operator { Operator::GreaterEqual }),
            map(char('>'), |_| -> Operator { Operator::Greater }),
        )))(input)?;
        if let Some(op) = op {
            input = comment_whitespace0(input)?.0;
            let right: LocatedAst<Expression>;
            (input, right) = cut(include_term)(input)?;
            left = LocatedAst::new(
                pos.clone(),
                Expression::Binary(Binary {
                    left: Box::new(left),
                    op,
                    right: Box::new(right),
                }),
            );
        } else {
            break Ok((input, left));
        }
    }
    // let (input, pos) = position(input)?;
    // let (input, left) = include_term(input)?;
    // let (input, op) = opt(alt((
    //     map(tag("<="), |_| -> Operator { Operator::LessEqual }),
    //     map(char('<'), |_| -> Operator { Operator::Less }),
    //     map(tag(">="), |_| -> Operator { Operator::GreaterEqual }),
    //     map(char('>'), |_| -> Operator { Operator::Greater }),
    // )))(input)?;
    // if let Some(op) = op {
    //     let (input, _) = comment_whitespace0(input)?;
    //     let (input, right) = cut(include_comparison)(input)?;
    //     let branch = Expression::Binary(Binary {
    //         left: Box::new(left),
    //         op,
    //         right: Box::new(right),
    //     });
    //     Ok((input, LocatedAst::new(pos, branch)))
    // } else {
    //     Ok((input, left))
    // }
}

fn include_term(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    let (input, pos) = position(input)?;
    let (mut input, mut left) = include_factor(input)?;
    loop {
        let op: Option<Operator>;
        (input, op) = opt(alt((
            map(char('+'), |_| -> Operator { Operator::Add }),
            map(char('-'), |_| -> Operator { Operator::Subtract }),
        )))(input)?;
        if let Some(op) = op {
            input = comment_whitespace0(input)?.0;
            let right: LocatedAst<Expression>;
            (input, right) = cut(include_factor)(input)?;
            left = LocatedAst::new(
                pos.clone(),
                Expression::Binary(Binary {
                    left: Box::new(left),
                    op,
                    right: Box::new(right),
                }),
            );
        } else {
            break Ok((input, left));
        }
    }

    // let (input, pos) = position(input)?;
    // let (input, left) = include_factor(input)?;
    // let (input, op) = opt(alt((
    //     map(char('+'), |_| -> Operator { Operator::Add }),
    //     map(char('-'), |_| -> Operator { Operator::Subtract }),
    // )))(input)?;
    // if let Some(op) = op {
    //     let (input, _) = comment_whitespace0(input)?;
    //     let (input, right) = cut(include_term)(input)?;
    //     let branch = Expression::Binary(Binary {
    //         left: Box::new(left),
    //         op,
    //         right: Box::new(right),
    //     });
    //     Ok((input, LocatedAst::new(pos, branch)))
    // } else {
    //     Ok((input, left))
    // }
}
fn include_factor(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    let (input, pos) = position(input)?;
    let (mut input, mut left) = include_unary(input)?;
    loop {
        let op: Option<Operator>;
        (input, op) = opt(alt((
            map(char('*'), |_| -> Operator { Operator::Multiply }),
            map(char('/'), |_| -> Operator { Operator::Divide }),
        )))(input)?;
        if let Some(op) = op {
            input = comment_whitespace0(input)?.0;
            let right: LocatedAst<Expression>;
            (input, right) = cut(include_unary)(input)?;
            left = LocatedAst::new(
                pos.clone(),
                Expression::Binary(Binary {
                    left: Box::new(left),
                    op,
                    right: Box::new(right),
                }),
            );
        } else {
            break Ok((input, left));
        }
    }

    // let (input, pos) = position(input)?;
    // let (input, left) = include_unary(input)?;
    // let (input, op) = opt(alt((
    //     map(char('*'), |_| -> Operator { Operator::Multiply }),
    //     map(char('/'), |_| -> Operator { Operator::Divide }),
    // )))(input)?;
    // if let Some(op) = op {
    //     let (input, _) = comment_whitespace0(input)?;
    //     let (input, right) = cut(include_factor)(input)?;
    //     let branch = Expression::Binary(Binary {
    //         left: Box::new(left),
    //         op,
    //         right: Box::new(right),
    //     });
    //     Ok((input, LocatedAst::new(pos, branch)))
    // } else {
    //     Ok((input, left))
    // }
}

fn include_unary(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    let (input, pos) = position(input)?;
    alt((
        map(
            alt((
                map(preceded(tag("-"), cut(include_unary)), |e| {
                    Unary::Negative(Box::new(e))
                }),
                map(preceded(tag("!"), cut(include_unary)), |e| {
                    Unary::Not(Box::new(e))
                }),
            )),
            move |u| LocatedAst::new(pos, Expression::Unary(u)),
        ),
        include_primary,
    ))(input)
}

fn include_primary(input: Span) -> IResult<Span, LocatedAst<Expression>, GrammarError<Span>> {
    let (input, pos) = position(input)?;
    let (input, expr) = alt((
        map(grouping, |g| Expression::Grouping(g)),
        map(literal, |l| Expression::Literal(l)),
        map(identifier, |v| Expression::Variable(v.fragment())),
    ))(input)?;
    let (input, _) = comment_whitespace0(input)?;
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
    alt((
        map(number, |n| -> Literal { Literal::Number(n) }),
        map(string, |s| -> Literal { Literal::String(s) }),
        map(tag("true"), |_| -> Literal { Literal::True }),
        map(tag("false"), |_| -> Literal { Literal::False }),
        map(tag("nil"), |_| -> Literal { Literal::Nil }),
    ))(input)
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
            error_kind: GrammarErrorKind::Grammar {
                kind: "Unterminated string.",
                at: None,
            },
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

// grouping       → "(" expression ")" ;
fn grouping(input: Span) -> IResult<Span, Box<LocatedAst<Expression>>, GrammarError<Span>> {
    let (input, _) = char('(')(input)?;
    let (input, _) = comment_whitespace0(input)?;
    let (input, e) = context("group expression", cut(expression))(input)?;
    let (input, _) = char(')')(input)?;
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
            GrammarErrorKind::Grammar {
                kind: "Unterminated string.",
                at: None,
            },
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
    fn test_unary() {
        let (_, res) = expression("-0 < 0".into()).unwrap();
        if let Expression::Binary(Binary {
            left:
                box LocatedAst {
                    ast: Expression::Unary(Unary::Negative(box LocatedAst { ast: left, .. })),
                    ..
                },
            op: crate::ast::expression::Operator::Less,
            right,
        }) = res.ast
        {
            assert_eq!(left, Expression::Literal(Literal::Number(0.0)));
            assert_eq!(right.ast, Expression::Literal(Literal::Number(0.0)));
        } else {
            panic!("Expected binary expression, got {:?}", res.ast);
        }
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
    fn test_term() {
        let (_, res) = expression("a + b".into()).unwrap();
        match res.ast {
            Expression::Binary(Binary {
                left,
                op: Operator::Add,
                right,
            }) => {
                assert_eq!(left.ast, Expression::Variable("a"));
                assert_eq!(right.ast, Expression::Variable("b"));
            }
            _ => panic!("Expected binary expression, got {:?}", res.ast),
        }
    }

    #[test]
    fn test_assigment() {
        let (_, res) = expression("a = b = 1".into()).unwrap();
        match res.ast {
            Expression::Assignment(Assignment {
                id: a,
                expr:
                    box LocatedAst {
                        ast:
                            Expression::Assignment(Assignment {
                                id: b,
                                expr: box LocatedAst { ast: v, .. },
                                ..
                            }),
                        ..
                    },
            }) => {
                assert_eq!(a, "a");
                assert_eq!(b, "b");
                assert_eq!(v, Expression::Literal(Literal::Number(1.0)));
            }
            _ => panic!("Expected assignment, got {:?}", res.ast),
        }
    }

    #[test]
    fn test_equality() {
        let (_, res) = expression("false == true == true".into()).unwrap();
        match res.ast {
            Expression::Binary(Binary {
                left:
                    box LocatedAst {
                        ast:
                            Expression::Binary(Binary {
                                left: box LocatedAst { ast: v1, .. },
                                op: Operator::Equal,
                                right: box LocatedAst { ast: v2, .. },
                            }),
                        ..
                    },
                op: Operator::Equal,
                right: box LocatedAst { ast: v3, .. },
            }) => {
                assert_eq!(v1, Expression::Literal(Literal::False));
                assert_eq!(v2, Expression::Literal(Literal::True));
                assert_eq!(v3, Expression::Literal(Literal::True));
            }
            _ => panic!("Expected binary expression, got {:?}", res.ast),
        }
    }
}
