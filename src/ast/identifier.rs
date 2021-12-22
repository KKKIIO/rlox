use nom::{
    bytes::complete::take_while1, character::complete::anychar, combinator::cut, error::ParseError,
    IResult,
};
use phf::{phf_set, Set};

use super::parse::{GrammarError, GrammarErrorKind, Span};

static KEYWORDS: Set<&'static str> = phf_set! {
  "and",
  "class",
  "else",
  "false",
  "for",
  "fun",
  "if",
  "nil",
  "or",
  "print",
  "return",
  "super",
  "this",
  "true",
  "var",
  "while",
};

pub fn identifier(input: Span) -> IResult<Span, Span, GrammarError<Span>> {
    let (consumed_input, word) = identifier_or_keyword(input)?;
    if KEYWORDS.contains(word.fragment()) {
        Err(nom::Err::Error(GrammarError {
            input,
            error_kind: GrammarErrorKind::Grammar {
                kind: "Expect variable name.",
                at: Some(word),
            },
        }))
    } else {
        Ok((consumed_input, word))
    }
}

fn identifier_or_keyword(input: Span) -> IResult<Span, Span, GrammarError<Span>> {
    let (_, c) = anychar(input)?;
    if !is_alpha(c) {
        Err(nom::Err::Error(GrammarError::from_char(input, c)))
    } else {
        cut(take_while1(is_alpha_numeric))(input)
    }
}

pub fn is_alpha_numeric(c: char) -> bool {
    is_alpha(c) || c.is_ascii_digit()
}
fn is_alpha(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}
