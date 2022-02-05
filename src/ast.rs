use self::{error::GrammarError, scanner::Scanner, statement::File, token::TokenType};

pub mod error;
pub mod expression;
pub mod parser;
pub mod scanner;
pub mod statement;
pub mod token;

pub fn parse_source<'a>(src: &'a [u8]) -> Result<File<'a>, Vec<GrammarError<'a>>> {
    let mut scanner = Scanner::new(src);
    let mut tokens = vec![];
    loop {
        let token: token::Token<'a> = scanner.scan_token().map_err(|e| vec![e])?;
        let eof = token.ttype == TokenType::Eof;
        tokens.push(token);
        if eof {
            break;
        }
    }
    parser::parse(tokens)
}
