use super::token::Token;

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
    Super(Super<'a>),
    This(This<'a>),
    Variable(Variable<'a>),
    Get(Get<'a>),
    Call(Call<'a>),
}

#[derive(Debug, PartialEq)]
pub enum LValue<'a> {
    Variable(Variable<'a>),
    Get(Get<'a>),
}

#[derive(Debug, PartialEq)]
pub struct Assignment<'a> {
    pub lvalue: LValue<'a>,
    pub op_line: u32,
    pub expr: Box<Expression<'a>>,
}
#[derive(Debug, PartialEq)]
pub struct Variable<'a> {
    pub name: Token<'a>,
}

#[derive(Debug, PartialEq)]
pub struct Binary<'a> {
    pub left: Box<Expression<'a>>,
    pub op: Token<'a>,
    pub right: Box<Expression<'a>>,
}

#[derive(Debug, PartialEq)]
pub struct Unary<'a> {
    pub op: Token<'a>,
    pub right: Box<Expression<'a>>,
}

#[derive(Debug, PartialEq)]
pub struct Super<'a> {
    pub super_: Token<'a>,
    pub method: Token<'a>,
}

#[derive(Debug, PartialEq)]
pub struct This<'a> {
    pub this: Token<'a>,
}

#[derive(Debug, PartialEq)]
pub struct Get<'a> {
    pub expr: Box<Expression<'a>>,
    pub dot: Token<'a>,
    pub name: Token<'a>,
}

#[derive(Debug, PartialEq)]
pub struct Call<'a> {
    pub callee: Box<Expression<'a>>,
    pub left_paren_line: u32,
    pub args: Vec<Expression<'a>>,
}
