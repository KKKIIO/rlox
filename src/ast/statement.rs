use super::{expression::Expression, token::Token};

#[derive(Debug, PartialEq)]
pub enum DeclOrStmt<'a> {
    ClassDecl(ClassDecl<'a>),
    FunDecl(FunDecl<'a>),
    VarDecl(VarDecl<'a>),
    Stmt(Statement<'a>),
}

#[derive(Debug, PartialEq)]
pub struct ClassDecl<'a> {
    pub class_line: u32,
    pub name: Token<'a>,
    pub super_class: Option<Token<'a>>,
    pub methods: Vec<FunDecl<'a>>,
}

#[derive(Debug, PartialEq)]
pub struct FunDecl<'a> {
    pub fun_line: u32,
    pub name: Token<'a>,
    pub params: Vec<Token<'a>>,
    pub body: BlockStmt<'a>,
}

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
    Return(ReturnStmt<'a>),
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
    pub right_brace_line: u32,
    pub stmts: Vec<DeclOrStmt<'a>>,
}

#[derive(Debug, PartialEq)]
pub struct IfStmt<'a> {
    pub if_: Token<'a>,
    pub cond: Expression<'a>,
    pub then_branch: Box<Statement<'a>>,
    pub then_branch_last: Token<'a>,
    pub else_branch: Option<(Token<'a>, Box<Statement<'a>>, Token<'a>)>,
}

#[derive(Debug, PartialEq)]
pub struct ForStmt<'a> {
    pub for_: Token<'a>,
    pub init: Option<Box<DeclOrStmt<'a>>>,
    pub cond: Option<Box<Expression<'a>>>,
    pub post: Option<Box<Expression<'a>>>,
    pub body: Box<Statement<'a>>,
    pub body_last: Token<'a>,
}

#[derive(Debug, PartialEq)]
pub struct WhileStmt<'a> {
    pub while_: Token<'a>,
    pub cond: Box<Expression<'a>>,
    pub body: Box<Statement<'a>>,
    pub body_last: Token<'a>,
}

#[derive(Debug, PartialEq)]
pub struct ReturnStmt<'a> {
    pub return_: Token<'a>,
    pub value: Option<Expression<'a>>,
}

#[derive(Debug, PartialEq)]
pub struct File<'a> {
    pub statements: Vec<DeclOrStmt<'a>>,
    pub eof_line: u32,
}
