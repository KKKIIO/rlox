use core::result::Result;
use std::vec;

use crate::ast::expression::Literal;

use super::{
    error::GrammarError,
    expression::{
        Assignment, Binary, Call, Expression, Get, LValue, LiteralValue, Super, This, Unary,
        Variable,
    },
    statement::{
        BlockStmt, ClassDecl, DeclOrStmt, ExprStmt, File, ForStmt, FunDecl, IfStmt, PrintStmt,
        ReturnStmt, Statement, VarDecl, WhileStmt,
    },
    token::{Token, TokenType},
};

struct Parser<'a> {
    tokens: Vec<Token<'a>>,
    current: usize,
    errs: Vec<GrammarError<'a>>,
}

enum FunType {
    Fun,
    Method,
}

pub fn parse<'a>(tokens: Vec<Token<'a>>) -> Result<File<'a>, Vec<GrammarError<'a>>> {
    let mut parser = Parser {
        tokens,
        current: 0,
        errs: vec![],
    };
    let mut statements = vec![];
    while !parser.is_at_end() {
        if let Some(d) = parser.declaration() {
            statements.push(d);
        }
    }
    if parser.errs.is_empty() {
        Ok(File {
            statements,
            eof_line: parser.peek().line,
        })
    } else {
        Err(parser.errs)
    }
}
impl<'a> Parser<'a> {
    fn expression(&mut self) -> Result<Expression<'a>, GrammarError<'a>> {
        self.assignment()
    }

    // return option instead of Result to continue parsing
    fn declaration(&mut self) -> Option<DeclOrStmt<'a>> {
        let rs = if self.match_t(TokenType::Class) {
            self.class_declaration().map(DeclOrStmt::ClassDecl)
        } else if self.match_t(TokenType::Fun) {
            self.function(FunType::Fun).map(DeclOrStmt::FunDecl)
        } else if self.match_t(TokenType::Var) {
            self.var_declaration().map(DeclOrStmt::VarDecl)
        } else {
            self.statement().map(DeclOrStmt::Stmt)
        };

        match rs {
            Ok(d) => Some(d),
            Err(e) => {
                self.errs.push(e);
                self.synchronize();
                None
            }
        }
    }

    fn class_declaration(&mut self) -> Result<ClassDecl<'a>, GrammarError<'a>> {
        let class_line = self.previous().line;
        let name = self.consume(TokenType::Identifier, "Expect class name.")?;
        let super_cls = if self.match_t(TokenType::Less) {
            Some(self.consume(TokenType::Identifier, "Expect superclass name.")?)
        } else {
            None
        };
        self.consume(TokenType::LeftBrace, "Expect '{' before class body.")?;
        let mut methods = vec![];
        while !self.check(TokenType::RightBrace) && !self.is_at_end() {
            methods.push(self.function(FunType::Method)?);
        }
        self.consume(TokenType::RightBrace, "Expect '}' after class body.")?;
        Ok(ClassDecl {
            class_line,
            name,
            super_cls,
            methods,
        })
    }

    fn statement(&mut self) -> Result<Statement<'a>, GrammarError<'a>> {
        Ok(if self.match_t(TokenType::For) {
            Statement::For(self.for_statement()?)
        } else if self.match_t(TokenType::If) {
            Statement::If(self.if_statement()?)
        } else if self.match_t(TokenType::Print) {
            Statement::Print(self.print_statement()?)
        } else if self.match_t(TokenType::Return) {
            Statement::Return(self.return_statement()?)
        } else if self.match_t(TokenType::While) {
            Statement::While(self.while_statement()?)
        } else if self.match_t(TokenType::LeftBrace) {
            Statement::Block(self.block()?)
        } else {
            Statement::Expr(self.expression_statement()?)
        })
    }

    fn for_statement(&mut self) -> Result<ForStmt<'a>, GrammarError<'a>> {
        let for_ = self.previous();
        self.consume(TokenType::LeftParen, "Expect '(' after 'for'.")?;
        let init = if self.match_t(TokenType::Semicolon) {
            None
        } else if self.match_t(TokenType::Var) {
            Some(DeclOrStmt::VarDecl(self.var_declaration()?))
        } else {
            Some(DeclOrStmt::Stmt(Statement::Expr(
                self.expression_statement()?,
            )))
        };

        let cond = if !self.check(TokenType::Semicolon) {
            Some(self.expression()?)
        } else {
            None
        };
        self.consume(TokenType::Semicolon, "Expect ';' after loop condition.")?;

        let post = if !self.check(TokenType::RightParen) {
            Some(self.expression()?)
        } else {
            None
        };
        self.consume(TokenType::RightParen, "Expect ')' after for clauses.")?;
        let body = self.statement()?;
        let body_last = self.previous();
        Ok(ForStmt {
            for_,
            init: init.map(|d| d.into()),
            cond: cond.map(|e| e.into()),
            post: post.map(|e| e.into()),
            body: body.into(),
            body_last,
        })
    }

    fn if_statement(&mut self) -> Result<IfStmt<'a>, GrammarError<'a>> {
        let if_ = self.previous();
        self.consume(TokenType::LeftParen, "Expect '(' after 'if'.")?;
        let cond = self.expression()?;
        self.consume(TokenType::RightParen, "Expect ')' after if condition.")?;

        let then_branch = self.statement()?;
        let then_branch_last = self.previous();
        let else_branch = if self.match_t(TokenType::Else) {
            let else_ = self.previous();
            let branch = self.statement()?;
            let branch_last = self.previous();
            Some((else_, branch.into(), branch_last))
        } else {
            None
        };
        Ok(IfStmt {
            if_,
            cond: cond.into(),
            then_branch: then_branch.into(),
            then_branch_last,
            else_branch,
        })
    }

    fn print_statement(&mut self) -> Result<PrintStmt<'a>, GrammarError<'a>> {
        let print_line = self.previous().line;
        let expr = self.expression()?;
        self.consume(TokenType::Semicolon, "Expect ';' after value.")?;
        Ok(PrintStmt { print_line, expr })
    }
    fn return_statement(&mut self) -> Result<ReturnStmt<'a>, GrammarError<'a>> {
        let return_ = self.previous();
        let value = if !self.check(TokenType::Semicolon) {
            Some(self.expression()?)
        } else {
            None
        };
        self.consume(TokenType::Semicolon, "Expect ';' after return value.")?;
        Ok(ReturnStmt {
            return_,
            value: value.map(|e| e.into()),
        })
    }

    fn var_declaration(&mut self) -> Result<VarDecl<'a>, GrammarError<'a>> {
        let name = self.consume(TokenType::Identifier, "Expect variable name.")?;

        let init_expr = if self.match_t(TokenType::Equal) {
            Some(self.expression()?)
        } else {
            None
        };

        self.consume(
            TokenType::Semicolon,
            "Expect ';' after variable declaration.",
        )?;
        Ok(VarDecl { name, init_expr })
    }

    fn while_statement(&mut self) -> Result<WhileStmt<'a>, GrammarError<'a>> {
        let while_ = self.previous();
        self.consume(TokenType::LeftParen, "Expect '(' after 'while'.")?;
        let cond = self.expression()?;
        self.consume(TokenType::RightParen, "Expect ')' after condition.")?;
        let body = self.statement()?;
        let body_last = self.previous();

        Ok(WhileStmt {
            while_,
            cond: cond.into(),
            body: body.into(),
            body_last,
        })
    }

    fn expression_statement(&mut self) -> Result<ExprStmt<'a>, GrammarError<'a>> {
        let expr = self.expression()?;
        let semicolon_line = self
            .consume(TokenType::Semicolon, "Expect ';' after expression.")?
            .line;
        Ok(ExprStmt {
            expr,
            semicolon_line,
        })
    }

    fn function(&mut self, fun_type: FunType) -> Result<FunDecl<'a>, GrammarError<'a>> {
        let (err_name, err_leftparen, err_function_left_bracket) = match fun_type {
            FunType::Fun => (
                ERROR_FUNCTION_NAME,
                ERROR_FUNCTION_LEFT_PAREN,
                ERROR_FUNCTION_LEFT_BRACKET,
            ),
            FunType::Method => (
                ERROR_METHOD_NAME,
                ERROR_METHOD_LEFT_PAREN,
                ERROR_METHOD_LEFT_BRACKET,
            ),
        };
        let fun = self.previous();
        let name = self.consume(TokenType::Identifier, err_name)?;
        self.consume(TokenType::LeftParen, err_leftparen)?;
        let mut params = vec![];
        if !self.check(TokenType::RightParen) {
            loop {
                if params.len() >= 255 {
                    self.errs.push(GrammarError::at_token(
                        "Can't have more than 255 parameters.",
                        self.peek(),
                    ));
                }

                let token = self.consume(TokenType::Identifier, "Expect parameter name.")?;
                params.push(token);
                if !self.match_t(TokenType::Comma) {
                    break;
                }
            }
        }
        self.consume(TokenType::RightParen, "Expect ')' after parameters.")?;

        if let Err(err) = self.consume(TokenType::LeftBrace, err_function_left_bracket) {
            self.errs.push(err);
        }
        let body = self.block()?;
        Ok(FunDecl {
            fun,
            name,
            params,
            body,
        })
    }

    fn block(&mut self) -> Result<BlockStmt<'a>, GrammarError<'a>> {
        let mut stmts = vec![];

        while !self.check(TokenType::RightBrace) && !self.is_at_end() {
            if let Some(d) = self.declaration() {
                stmts.push(d);
            }
        }

        let right_brace_line = self
            .consume(TokenType::RightBrace, "Expect '}' after block.")?
            .line;
        Ok(BlockStmt {
            right_brace_line,
            stmts,
        })
    }

    fn assignment(&mut self) -> Result<Expression<'a>, GrammarError<'a>> {
        let left = self.or()?;

        if self.match_t(TokenType::Equal) {
            let equals = self.previous();
            let right = self.assignment()?;

            match left {
                Expression::Variable(v) => Ok(Expression::Assignment(Assignment {
                    lvalue: LValue::Variable(v),
                    expr: right.into(),
                    op_line: equals.line,
                })),
                Expression::Get(g) => Ok(Expression::Assignment(Assignment {
                    lvalue: LValue::Get(g),
                    expr: right.into(),
                    op_line: equals.line,
                })),
                _ => {
                    // [no-throw]
                    self.errs
                        .push(GrammarError::at_token("Invalid assignment target.", equals));
                    Ok(left)
                }
            }
        } else {
            Ok(left)
        }
    }

    fn or(&mut self) -> Result<Expression<'a>, GrammarError<'a>> {
        let mut expr = self.and()?;

        while self.match_t(TokenType::Or) {
            let op = self.previous();
            let right = self.and();
            expr = Expression::Binary(Binary {
                left: Box::new(expr),
                op,
                right: Box::new(right?),
            });
        }

        Ok(expr)
    }
    fn and(&mut self) -> Result<Expression<'a>, GrammarError<'a>> {
        let mut left = self.equality()?;

        while self.match_t(TokenType::And) {
            let op = self.previous();
            let right = self.equality()?;
            left = Expression::Binary(Binary {
                left: left.into(),
                op,
                right: right.into(),
            });
        }

        return Ok(left);
    }

    fn equality(&mut self) -> Result<Expression<'a>, GrammarError<'a>> {
        let mut left = self.comparison()?;

        while self.match_t(TokenType::BangEqual) || self.match_t(TokenType::EqualEqual) {
            let op = self.previous();
            let right = self.comparison()?;
            left = Expression::Binary(Binary {
                left: left.into(),
                op,
                right: right.into(),
            })
        }

        return Ok(left);
    }
    fn comparison(&mut self) -> Result<Expression<'a>, GrammarError<'a>> {
        let mut left = self.term()?;

        while self.match_t(TokenType::Greater)
            || self.match_t(TokenType::GreaterEqual)
            || self.match_t(TokenType::Less)
            || self.match_t(TokenType::LessEqual)
        {
            let op = self.previous();
            let right = self.term()?;
            left = Expression::Binary(Binary {
                left: left.into(),
                op,
                right: right.into(),
            })
        }

        Ok(left)
    }
    fn term(&mut self) -> Result<Expression<'a>, GrammarError<'a>> {
        let mut left = self.factor()?;

        while self.match_t(TokenType::Minus) || self.match_t(TokenType::Plus) {
            let op = self.previous();
            let right = self.factor()?;
            left = Expression::Binary(Binary {
                left: left.into(),
                op,
                right: right.into(),
            });
        }

        Ok(left)
    }

    fn factor(&mut self) -> Result<Expression<'a>, GrammarError<'a>> {
        let mut left = self.unary()?;

        while self.match_t(TokenType::Slash) || self.match_t(TokenType::Star) {
            let op = self.previous();
            let right = self.unary()?;
            left = Expression::Binary(Binary {
                left: left.into(),
                op,
                right: right.into(),
            })
        }

        Ok(left)
    }

    fn unary(&mut self) -> Result<Expression<'a>, GrammarError<'a>> {
        if self.match_t(TokenType::Bang) || self.match_t(TokenType::Minus) {
            let op = self.previous();
            let right = self.unary()?;
            return Ok(Expression::Unary(Unary {
                op,
                right: right.into(),
            }));
        }

        self.call()
    }

    fn finish_call(&mut self, callee: Expression<'a>) -> Result<Expression<'a>, GrammarError<'a>> {
        let left_paren = self.previous();
        let mut args = vec![];
        if !self.check(TokenType::RightParen) {
            loop {
                if args.len() >= 255 {
                    self.errs.push(GrammarError::at_token(
                        "Can't have more than 255 arguments.",
                        self.peek(),
                    ));
                }

                args.push(self.expression()?);
                if !self.match_t(TokenType::Comma) {
                    break;
                }
            }
        }

        self.consume(TokenType::RightParen, "Expect ')' after arguments.")?;

        Ok(Expression::Call(Call {
            callee: callee.into(),
            left_paren,
            args,
        }))
    }

    fn call(&mut self) -> Result<Expression<'a>, GrammarError<'a>> {
        let mut expr = self.primary()?;

        loop {
            if self.match_t(TokenType::LeftParen) {
                expr = self.finish_call(expr)?;
            } else if self.match_t(TokenType::Dot) {
                let dot = self.previous();
                let name =
                    self.consume(TokenType::Identifier, "Expect property name after '.'.")?;
                expr = Expression::Get(Get {
                    src: expr.into(),
                    dot,
                    name,
                });
            } else {
                break;
            }
        }
        Ok(expr)
    }

    fn primary(&mut self) -> Result<Expression<'a>, GrammarError<'a>> {
        let line = self.peek().line;
        if self.match_t(TokenType::True) {
            Ok(Expression::Literal(Literal {
                value: LiteralValue::True,
                line,
            }))
        } else if self.match_t(TokenType::False) {
            Ok(Expression::Literal(Literal {
                value: LiteralValue::False,
                line,
            }))
        } else if self.match_t(TokenType::Nil) {
            Ok(Expression::Literal(Literal {
                value: LiteralValue::Nil,
                line,
            }))
        } else if self.match_t(TokenType::Number) {
            let token = self.previous();
            let n = token.lexeme.parse().unwrap();
            Ok(Expression::Literal(Literal {
                value: LiteralValue::Number(n),
                line,
            }))
        } else if self.match_t(TokenType::String) {
            let token = self.previous();
            let s = token.lexeme[1..token.lexeme.len() - 1].to_string();
            Ok(Expression::Literal(Literal {
                value: LiteralValue::String(s),
                line,
            }))
        } else if self.match_t(TokenType::Super) {
            let super_ = self.previous();
            self.consume(TokenType::Dot, "Expect '.' after 'super'.")?;
            let method = self.consume(TokenType::Identifier, "Expect superclass method name.")?;
            Ok(Expression::Super(Super { super_, method }))
        } else if self.match_t(TokenType::This) {
            Ok(Expression::This(This {
                this: self.previous(),
            }))
        } else if self.match_t(TokenType::Identifier) {
            Ok(Expression::Variable(Variable {
                name: self.previous(),
            }))
        } else if self.match_t(TokenType::LeftParen) {
            let expr = self.expression()?;
            self.consume(TokenType::RightParen, "Expect ')' after expression.")?;
            Ok(Expression::Grouping(expr.into()))
        } else {
            Err(GrammarError::at_token("Expect expression.", self.peek()))
        }
    }
    fn match_t(&mut self, ttype: TokenType) -> bool {
        if self.check(ttype) {
            self.advance();
            true
        } else {
            false
        }
    }
    fn consume(
        &mut self,
        ttype: TokenType,
        message: &'static str,
    ) -> Result<Token<'a>, GrammarError<'a>> {
        if self.check(ttype) {
            Ok(self.advance())
        } else {
            let at = self.peek();
            Err(GrammarError::at_token(message, at))
        }
    }
    fn check(&self, ttype: TokenType) -> bool {
        if self.is_at_end() {
            return false;
        }
        self.peek().ttype == ttype
    }
    fn advance(&mut self) -> Token<'a> {
        if !self.is_at_end() {
            self.current += 1;
        }
        self.previous()
    }
    pub fn is_at_end(&self) -> bool {
        self.peek().ttype == TokenType::Eof
    }

    fn peek(&self) -> Token<'a> {
        self.tokens[self.current]
    }

    fn previous(&self) -> Token<'a> {
        self.tokens[self.current - 1]
    }
    fn synchronize(&mut self) -> () {
        self.advance();

        while !self.is_at_end() {
            if self.previous().ttype == TokenType::Semicolon {
                return;
            }

            match self.peek().ttype {
                TokenType::Class
                | TokenType::Fun
                | TokenType::Var
                | TokenType::For
                | TokenType::If
                | TokenType::While
                | TokenType::Print
                | TokenType::Return => {
                    return;
                }
                _ => {
                    self.advance();
                }
            }
        }
    }
}

const ERROR_FUNCTION_NAME: &'static str = "Expect function name.";
const ERROR_FUNCTION_LEFT_PAREN: &'static str = "Expect '(' after function name.";
const ERROR_FUNCTION_LEFT_BRACKET: &'static str = "Expect '{' before function body.";

const ERROR_METHOD_NAME: &'static str = "Expect method name.";
const ERROR_METHOD_LEFT_PAREN: &'static str = "Expect '(' after method name.";
const ERROR_METHOD_LEFT_BRACKET: &'static str = "Expect '{' before method body.";
