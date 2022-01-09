use super::{expression::Expression, token::Token};

#[derive(Debug, PartialEq)]
pub enum DeclOrStmt<'a> {
    Decl(VarDecl<'a>),
    Stmt(Statement<'a>),
}

// declaration    → varDecl | statement ;
#[derive(Debug, PartialEq)]
pub struct VarDecl<'a> {
    pub name: Token<'a>,
    pub init_expr: Option<Expression<'a>>,
}

#[derive(Debug, PartialEq)]
pub enum Statement<'a> {
    Expr(ExprStmt<'a>),
    For(ForStmt<'a>),
    If(IfStmt<'a>),
    Print(PrintStmt<'a>),
    While(WhileStmt<'a>),
    Block(BlockStmt<'a>),
}

#[derive(Debug, PartialEq)]
pub struct ExprStmt<'a> {
    pub expr: Expression<'a>,
    pub semicolon_line: u32,
}

#[derive(Debug, PartialEq)]
pub struct PrintStmt<'a> {
    pub print_line: u32,
    pub expr: Expression<'a>,
}

#[derive(Debug, PartialEq)]
pub struct BlockStmt<'a> {
    pub left_brace_line: u32,
    pub stmts: Vec<DeclOrStmt<'a>>,
}

#[derive(Debug, PartialEq)]
pub struct IfStmt<'a> {
    pub if_line: u32,
    pub cond: Expression<'a>,
    pub then_branch: Box<Statement<'a>>,
    pub else_branch: Option<Box<Statement<'a>>>,
}

#[derive(Debug, PartialEq)]
pub struct ForStmt<'a> {
    pub for_line: u32,
    pub init: Option<Box<DeclOrStmt<'a>>>,
    pub cond: Option<Box<Expression<'a>>>,
    pub post: Option<Box<Expression<'a>>>,
    pub body: Box<Statement<'a>>,
}

#[derive(Debug, PartialEq)]
pub struct WhileStmt<'a> {
    pub while_line: u32,
    pub cond: Box<Expression<'a>>,
    pub body: Box<Statement<'a>>,
}

#[derive(Debug, PartialEq)]
pub struct Program<'a> {
    pub statements: Vec<DeclOrStmt<'a>>,
}
