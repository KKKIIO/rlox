use std::fmt::Display;

use nom::error::{ContextError, ParseError};
use nom_locate::LocatedSpan;

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

    pub fn map<R>(self, f: impl FnOnce(T) -> R) -> LocatedAst<R> {
        LocatedAst {
            ast: f(self.ast),
            line: self.line,
        }
    }

    // pub fn include_pos<'a, F>(
    //     mut parser: F,
    // ) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, LocatedAst<T>, GrammarError<Span<'a>>>
    // where
    //     F: Parser<Span<'a>, T, GrammarError<Span<'a>>>,
    // {
    //     move |input: Span| {
    //         let (input, pos) = position(input)?;
    //         let (input, ast) = parser.parse(input)?;
    //         Ok((
    //             input,
    //             Self {
    //                 ast,
    //                 line: pos.location_line(),
    //             },
    //         ))
    //     }
    // }
}

#[derive(Debug, PartialEq)]
pub struct GrammarError<I> {
    pub input: I,
    pub error_kind: GrammarErrorKind<I>,
}

#[derive(Debug, PartialEq)]
pub enum GrammarErrorKind<I> {
    Grammar {
        kind: &'static str,
        at: Option<I>,
    },
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

    fn or(self, other: Self) -> Self {
        if let GrammarErrorKind::Grammar { .. } = &self.error_kind {
            self
        } else if let GrammarErrorKind::Grammar { .. } = &other.error_kind {
            other
        } else {
            self
        }
    }
}

impl<I> ContextError<I> for GrammarError<I> {}

impl<'a> Display for GrammarError<Span<'a>> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.error_kind {
            &GrammarErrorKind::Grammar { kind, at } => match at {
                Some(at) => write!(
                    f,
                    "[line {}] Error at '{}': {}",
                    self.input.location_line(),
                    at.fragment(),
                    kind
                ),
                None => write!(f, "[line {}] Error: {}", self.input.location_line(), kind),
            },
            GrammarErrorKind::Nom(ref kind) => write!(f, "error {:?} at: {}", kind, self.input),
        }
    }
}
