use std::fmt::Display;

use super::token::Token;

#[derive(Debug, PartialEq)]
pub struct GrammarError<'a> {
    kind: &'static str,
    at: Option<Token<'a>>,
    line: u32,
}
impl<'a> GrammarError<'a> {
    pub fn at_token(kind: &'static str, at: Token<'a>) -> Self {
        let line = at.line;
        Self {
            kind,
            at: Some(at),
            line,
        }
    }
    pub fn at_line(kind: &'static str, line: u32) -> Self {
        Self {
            kind,
            at: None,
            line,
        }
    }
}

impl<'a> Display for GrammarError<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.at {
            Some(at) => write!(
                f,
                "[line {}] Error at '{}': {}",
                self.line, at.lexeme, self.kind
            ),
            None => write!(f, "[line {}] Error: {}", self.line, self.kind),
        }
    }
}
