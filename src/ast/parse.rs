use std::fmt::Display;

use nom::error::{ContextError, ParseError};
use nom_locate::LocatedSpan;

pub type Span<'a> = LocatedSpan<&'a str>;

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
