use nom::{
    combinator::{eof, map},
    multi::many_till,
    IResult,
};

use super::{
    comment::comment_whitespace0,
    parse::{GrammarError, Span},
    statement::{decl_or_stmt, DeclOrStmt},
};

/*
program        → statement* EOF ;
 */
#[derive(Debug, PartialEq)]
pub struct Program<'a> {
    pub statements: Vec<DeclOrStmt<'a>>,
}

pub fn program(input: Span) -> IResult<Span, Program, GrammarError<Span>> {
    let (input, _) = comment_whitespace0(input)?;
    if input.is_empty() {
        return Ok((input, Program { statements: vec![] }));
    }
    let (input, program) = map(many_till(decl_or_stmt, eof), |(statements, _)| Program {
        statements,
    })(input)?;
    Ok((input, program))
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::parse::GrammarErrorKind;

    #[test]
    fn test_err_passthough() {
        let err = match program(
            "// [line 2] Error: Unterminated string.\n\"this string has no close quote".into(),
        )
        .unwrap_err()
        {
            nom::Err::Failure(e) => e,
            other => panic!("Expected Failure, got {}", other),
        };
        assert_eq!(
            err.error_kind,
            GrammarErrorKind::Grammar {
                kind: "Unterminated string.",
                at: None,
            }
        );
    }
}
