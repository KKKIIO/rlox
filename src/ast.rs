use nom::{
    error::{Error},
    Finish,
};

use self::{
    parse::Span,
    program::{parse_program, Program},
};

pub mod comment;
pub mod expression;
pub mod parse;
pub mod program;
pub mod statement;

pub fn parse_source(input: Span) -> Result<Program, Error<Span>> {
    parse_program(input.into())
        .finish()
        .map(|(_, program)| program)
}
