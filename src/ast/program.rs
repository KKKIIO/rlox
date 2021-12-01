use nom::{
    character::complete::multispace0,
    combinator::{eof, map},
    error::{ContextError, ParseError},
    multi::many0,
    IResult,
};

use super::{
    parse::Span,
    statement::{statement, Statement},
};

/*
program        → statement* EOF ;
 */
#[derive(Debug, PartialEq)]
pub struct Program<'a> {
    pub statements: Vec<Statement<'a>>,
}

pub fn parse_program<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, Program, E> {
    let (input, _) = multispace0(input)?;
    if input.is_empty() {
        return Ok((input, Program { statements: vec![] }));
    }
    let (input, program) = map(many0(statement), |statements| Program { statements })(input)?;
    let (input, _) = eof(input)?;
    Ok((input, program))
}
