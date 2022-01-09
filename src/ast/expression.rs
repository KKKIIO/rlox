use super::token::TokenType;

#[derive(Debug, PartialEq)]
pub enum LiteralValue {
    Number(f64),
    String(String),
    True,
    False,
    Nil,
}

#[derive(Debug, PartialEq)]
pub struct Literal {
    pub value: LiteralValue,
    pub line: u32,
}

#[derive(Debug, PartialEq)]
pub enum Expression<'a> {
    Assignment(Assignment<'a>),
    Literal(Literal),
    Unary(Unary<'a>),
    Binary(Binary<'a>),
    Grouping(Box<Expression<'a>>),
    Variable(Variable<'a>),
}

#[derive(Debug, PartialEq)]
pub struct Assignment<'a> {
    pub var_name: &'a str,
    pub op_line: u32,
    pub expr: Box<Expression<'a>>,
}
#[derive(Debug, PartialEq)]
pub struct Variable<'a> {
    pub name: &'a str,
    pub line: u32,
}

#[derive(Debug, PartialEq)]
pub struct Binary<'a> {
    pub left: Box<Expression<'a>>,
    pub op: TokenType,
    pub op_line: u32,
    pub right: Box<Expression<'a>>,
}

#[derive(Debug, PartialEq)]
pub struct Unary<'a> {
    pub op: TokenType,
    pub op_line: u32,
    pub right: Box<Expression<'a>>,
}
