use std::str::from_utf8_unchecked;

use super::{
    error::GrammarError,
    token::{Token, TokenType},
};

pub struct Scanner<'a> {
    src: &'a [u8],
    start: usize,
    next: usize,
    line: u32,
}

fn is_alpha(c: char) -> bool {
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_';
}
fn is_digit(c: char) -> bool {
    return c >= '0' && c <= '9';
}

impl<'a> Scanner<'a> {
    pub fn new(src: &'a [u8]) -> Self {
        Self {
            src,
            start: 0,
            next: 0,
            line: 1,
        }
    }
    fn is_at_end(&self) -> bool {
        self.next >= self.src.len()
    }
    fn advance(&mut self) -> char {
        let src = self.src;
        let c = src[self.next];
        self.next += 1;
        c.into()
    }
    fn match_c(&mut self, src: &'a [u8], expected: char) -> bool {
        if self.is_at_end() {
            return false;
        }
        let c: char = src[self.next].into();
        if c != expected {
            return false;
        }
        self.next += 1;
        return true;
    }
    fn make_token(&self, ttype: TokenType) -> Token<'a> {
        let src = self.src;
        Token {
            ttype,
            lexeme: unsafe { from_utf8_unchecked(&src[self.start..self.next]) },
            line: self.line,
        }
    }

    fn skip_whitespace(&mut self) {
        loop {
            let c = self.peek();
            match c {
                ' ' | '\r' | '\t' => {
                    self.advance();
                }
                '\n' => {
                    self.line += 1;
                    self.advance();
                }
                '/' => {
                    if self.peek_next() == '/' {
                        // A comment goes until the end of the line.
                        while self.peek() != '\n' && !self.is_at_end() {
                            self.advance();
                        }
                    } else {
                        return;
                    }
                }
                _ => {
                    break;
                }
            }
        }
    }

    fn identifier(&mut self) -> Result<Token<'a>, GrammarError<'a>> {
        while is_alpha(self.peek()) || self.peek().is_ascii_digit() {
            self.advance();
        }
        Ok(self.make_token(self.identifier_type()))
    }
    fn identifier_type(&self) -> TokenType {
        let src = self.src;
        match src[self.start].into() {
            'a' => self.check_keyword(1, 2, "nd", TokenType::And),
            'c' => self.check_keyword(1, 4, "lass", TokenType::Class),
            'e' => self.check_keyword(1, 3, "lse", TokenType::Else),
            'f' => {
                if self.next > 1 {
                    match src[self.start + 1].into() {
                        'a' => self.check_keyword(2, 3, "lse", TokenType::False),
                        'o' => self.check_keyword(2, 1, "r", TokenType::For),
                        'u' => self.check_keyword(2, 1, "n", TokenType::Fun),
                        _ => TokenType::Identifier,
                    }
                } else {
                    TokenType::Identifier
                }
            }

            'i' => self.check_keyword(1, 1, "f", TokenType::If),
            'n' => self.check_keyword(1, 2, "il", TokenType::Nil),
            'o' => self.check_keyword(1, 1, "r", TokenType::Or),
            'p' => self.check_keyword(1, 4, "rint", TokenType::Print),
            'r' => self.check_keyword(1, 5, "eturn", TokenType::Return),
            's' => self.check_keyword(1, 4, "uper", TokenType::Super),
            't' => {
                if self.next > 1 {
                    match src[self.start + 1].into() {
                        'r' => self.check_keyword(2, 2, "ue", TokenType::True),
                        'h' => self.check_keyword(2, 2, "is", TokenType::This),
                        _ => TokenType::Identifier,
                    }
                } else {
                    TokenType::Identifier
                }
            }
            'v' => self.check_keyword(1, 2, "ar", TokenType::Var),
            'w' => self.check_keyword(1, 4, "hile", TokenType::While),
            _ => TokenType::Identifier,
        }
    }
    fn check_keyword(
        &self,
        start: usize,
        length: usize,
        rest: &'static str,
        kwt: TokenType,
    ) -> TokenType {
        let src = self.src;
        if self.next == (self.start + start + length)
            && &src[(self.start + start)..self.next] == rest.as_bytes()
        {
            kwt
        } else {
            TokenType::Identifier
        }
    }
    fn number(&mut self) -> Result<Token<'a>, GrammarError<'a>> {
        while self.peek().is_ascii_digit() {
            self.advance();
        }

        // Look for a fractional part.
        if self.peek() == '.' && self.peek_next().is_ascii_digit() {
            // Consume the ".".
            self.advance();

            while self.peek().is_ascii_digit() {
                self.advance();
            }
        }

        Ok(self.make_token(TokenType::Number))
    }
    fn string(&mut self) -> Result<Token<'a>, GrammarError<'a>> {
        while self.peek() != '"' && !self.is_at_end() {
            if self.peek() == '\n' {
                self.line += 1;
            };
            self.advance();
        }

        if self.is_at_end() {
            Err(GrammarError::at_line("Unterminated string.", self.line))
        } else {
            // The closing quote.
            self.advance();
            Ok(self.make_token(TokenType::String))
        }
    }
    fn peek(&self) -> char {
        let src = self.src;
        if self.next >= self.src.len() {
            '\0'
        } else {
            src[self.next].into()
        }
    }
    fn peek_next(&self) -> char {
        let src = self.src;
        if self.next + 1 >= self.src.len() {
            '\0'
        } else {
            src[self.next + 1].into()
        }
    }
    pub fn scan_token<'s>(&'s mut self) -> Result<Token<'a>, GrammarError<'a>> {
        let src = self.src;
        self.skip_whitespace();
        self.start = self.next;
        if self.is_at_end() {
            return Ok(self.make_token(TokenType::Eof));
        };
        let c = self.advance();
        if is_alpha(c) {
            return self.identifier();
        };
        if is_digit(c) {
            return self.number();
        };
        //< scan-number

        match c {
            '(' => {
                return Ok(self.make_token(TokenType::LeftParen));
            }
            ')' => {
                return Ok(self.make_token(TokenType::RightParen));
            }
            '{' => {
                return Ok(self.make_token(TokenType::LeftBrace));
            }
            '}' => {
                return Ok(self.make_token(TokenType::RightBrace));
            }
            ';' => {
                return Ok(self.make_token(TokenType::Semicolon));
            }
            ',' => {
                return Ok(self.make_token(TokenType::Comma));
            }
            '.' => {
                return Ok(self.make_token(TokenType::Dot));
            }
            '-' => {
                return Ok(self.make_token(TokenType::Minus));
            }
            '+' => {
                return Ok(self.make_token(TokenType::Plus));
            }
            '/' => {
                return Ok(self.make_token(TokenType::Slash));
            }
            '*' => {
                return Ok(self.make_token(TokenType::Star));
            }
            //> two-char
            '!' => {
                let ttype = if self.match_c(src, '=') {
                    TokenType::BangEqual
                } else {
                    TokenType::Bang
                };
                return Ok(self.make_token(ttype));
            }
            '=' => {
                let ttype = if self.match_c(src, '=') {
                    TokenType::EqualEqual
                } else {
                    TokenType::Equal
                };
                return Ok(self.make_token(ttype));
            }
            '<' => {
                let ttype = if self.match_c(src, '=') {
                    TokenType::LessEqual
                } else {
                    TokenType::Less
                };
                return Ok(self.make_token(ttype));
            }
            '>' => {
                let ttype = if self.match_c(src, '=') {
                    TokenType::GreaterEqual
                } else {
                    TokenType::Greater
                };
                return Ok(self.make_token(ttype));
            }
            //< two-char
            //> scan-string
            '"' => {
                return self.string();
            }

            _ => {
                return Err(GrammarError::at_line("Unexpected character.", self.line));
            }
        }
    }
}
