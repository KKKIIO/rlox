use nom::Finish;

use self::{
    parse::{GrammarError, Span},
    program::{program, Program},
};

pub mod comment;
pub mod expression;
pub mod identifier;
pub mod parse;
pub mod program;
pub mod statement;

pub fn parse_source(input: Span) -> Result<Program, GrammarError<Span>> {
    program(input.into()).finish().map(|(_, program)| program)
}
