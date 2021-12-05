use std::fmt::Display;

use nom::{
    error::{ContextError, ParseError},
    IResult, Parser,
};
use nom_locate::{position, LocatedSpan};

pub type Span<'a> = LocatedSpan<&'a str>;

#[derive(Debug, PartialEq)]
pub struct LocatedAst<T> {
    pub ast: T,
    line: u32,
}

impl<T> LocatedAst<T> {
    pub fn new(pos: Span, token: T) -> Self {
        Self {
            ast: token,
            line: pos.location_line(),
        }
    }
    pub fn get_line(&self) -> u32 {
        self.line
    }
    pub fn include_pos<'a, F>(
        mut parser: F,
    ) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, LocatedAst<T>, GrammarError<Span<'a>>>
    where
        F: Parser<Span<'a>, T, GrammarError<Span<'a>>>,
    {
        move |input: Span| {
            let (input, pos) = position(input)?;
            let (input, ast) = parser.parse(input)?;
            Ok((
                input,
                Self {
                    ast,
                    line: pos.location_line(),
                },
            ))
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct GrammarError<I> {
    pub input: I,
    pub error_kind: GrammarErrorKind,
}

#[derive(Debug, PartialEq)]
pub enum GrammarErrorKind {
    Grammar(&'static str),
    /// Error kind given by various nom parsers
    Nom(nom::error::ErrorKind),
}

impl<I> ParseError<I> for GrammarError<I> {
    fn from_error_kind(input: I, kind: nom::error::ErrorKind) -> Self {
        GrammarError {
            input,
            error_kind: GrammarErrorKind::Nom(kind),
        }
    }

    fn append(_: I, _: nom::error::ErrorKind, other: Self) -> Self {
        other
    }
}

impl<I> ContextError<I> for GrammarError<I> {}

impl<'a> Display for GrammarError<Span<'a>> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.error_kind {
            GrammarErrorKind::Grammar(s) => {
                write!(f, "[line {}] Error: {}", self.input.location_line(), s)
            }
            GrammarErrorKind::Nom(ref kind) => write!(f, "error {:?} at: {}", kind, self.input),
        }
    }
}
