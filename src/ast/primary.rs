use nom::character::complete::char;
use nom::{
    branch::alt,
    bytes::complete::{tag, take_until},
    character::complete::digit1,
    combinator::{map, opt, recognize},
    sequence::tuple,
    IResult,
};

use super::parse::{GrammarError, GrammarErrorKind, Span};
// literal        → NUMBER | STRING | "true" | "false" | "nil" ;
#[derive(Debug, PartialEq)]
pub enum Literal {
    Number(f64),
    String(String),
    True,
    False,
    Nil,
}

pub fn literal(input: Span) -> IResult<Span, Literal, GrammarError<Span>> {
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
    let (input, s) = take_until("\"")(input).map_err(|e: nom::Err<nom::error::Error<Span>>| {
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
    let (input, _) = char('"')(input)?;
    Ok((input, s.to_string()))
}

#[cfg(test)]
mod test {
    use std::error::Error;

    use super::*;
    #[test]
    fn test_string() {
        let (rest, res) = string("\"hello\"".into()).unwrap();
        assert_eq!(res, "hello");
        assert_eq!(*rest.fragment(), "");
        let (_, res) = string("\"\"".into()).unwrap();
        assert_eq!(res, "");
        let (_, res) = string("\"\\\\\"".into()).unwrap();
        assert_eq!(res, "\\\\");
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
}
