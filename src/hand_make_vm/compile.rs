use core::fmt::Debug;
use std::{cell::RefCell, convert::TryInto, ops::Deref, rc::Rc};

use crate::ast::{
    expression::{Expression, LiteralValue},
    statement::{DeclOrStmt, Program, Statement, VarDecl},
    token::TokenType,
};

use super::{
    error::InterpreteError,
    vm::{Chunk, JumpIfParam, OpCode},
};

pub struct StrPool {
    pool: RefCell<Vec<Rc<str>>>,
}

impl StrPool {
    pub fn new() -> Self {
        Self {
            pool: RefCell::new(Vec::new()),
        }
    }

    pub fn register(&self, name: &str) -> Rc<str> {
        let pos_res = self
            .pool
            .borrow()
            .iter()
            .position(|n| (*n).as_ref() == name);
        let idx = if let Some(i) = pos_res {
            i
        } else {
            let mut p = self.pool.borrow_mut();
            p.push(name.to_string().into_boxed_str().into());
            p.len() - 1
        };
        self.pool.borrow().get(idx).unwrap().clone()
    }
}

struct Scopes {
    vars: Vec<Rc<str>>,
    var_count_per_scope: Vec<u8>,
}

impl Scopes {
    fn new() -> Self {
        Self {
            vars: Vec::new(),
            var_count_per_scope: Vec::new(),
        }
    }
    fn is_empty(&self) -> bool {
        self.var_count_per_scope.is_empty()
    }
    fn enter_scope(&mut self) {
        self.var_count_per_scope.push(0);
    }
    fn new_var(&mut self, name: Rc<str>) -> Result<(), &'static str> {
        if self.vars.len() >= u8::MAX as usize {
            return Err("too many variables");
        }
        self.vars.push(name);
        let cnt = self.var_count_per_scope.last_mut().unwrap();
        *cnt += 1;
        Ok(())
    }
    fn position(&self, name: &str) -> Option<u8> {
        self.vars
            .iter()
            .rev()
            .position(|n| n.as_ref() == name)
            .map(|i| (self.vars.len() - i - 1) as u8)
    }
    fn leave_scope(&mut self) -> u8 {
        let cnt = self.var_count_per_scope.pop().unwrap();
        self.vars.truncate(self.vars.len() - cnt as usize);
        cnt
    }
}

pub struct CompileRun<'a> {
    str_pool: &'a StrPool,
    chunk: Chunk<Rc<str>>,
    scopes: Scopes,
}
impl<'a> CompileRun<'a> {
    pub fn compile(
        program: &Program,
        str_pool: &'a StrPool,
    ) -> Result<Chunk<Rc<str>>, InterpreteError> {
        let mut run = Self {
            str_pool,
            chunk: Chunk::new(),
            scopes: Scopes::new(),
        };
        for stmt in program.statements.iter() {
            run.compile_decl_or_stmt(&stmt)?;
        }
        Ok(run.chunk)
    }

    fn compile_decl_or_stmt(&mut self, ds: &DeclOrStmt<'_>) -> Result<(), InterpreteError> {
        match ds {
            DeclOrStmt::Decl(l) => {
                self.compile_var_decl(l)?;
            }
            DeclOrStmt::Stmt(ref stmt) => {
                self.compile_stmt(stmt)?;
            }
        };
        Ok(())
    }

    fn compile_var_decl(&mut self, v: &VarDecl<'_>) -> Result<(), InterpreteError> {
        let line = v.name.line;
        let var_decl = v;
        if let Some(init_expr) = &var_decl.init_expr {
            self.compile_expression(init_expr)?;
        } else {
            self.chunk.add_code(OpCode::LoadNil, line);
        }
        if !self.scopes.is_empty() {
            self.scopes
                .new_var(self.str_pool.register(&v.name.lexeme))
                .map_err(|e| InterpreteError {
                    message: e.to_string(),
                    line,
                })?;
        } else {
            self.chunk.add_code(
                OpCode::DefGlobalVar(self.str_pool.register(v.name.lexeme)),
                line,
            );
        };
        Ok(())
    }

    fn compile_stmt(&mut self, stmt: &Statement<'_>) -> Result<(), InterpreteError> {
        match stmt {
            Statement::Expr(expr) => {
                self.compile_expression(&expr.expr)?;
                self.chunk.add_code(OpCode::Pop(1), expr.semicolon_line);
            }
            Statement::Print(s) => {
                self.compile_expression(&s.expr)?;
                self.chunk.add_code(OpCode::Print, s.print_line);
            }
            Statement::Block(b) => {
                self.scopes.enter_scope();
                for stmt in b.stmts.iter() {
                    self.compile_decl_or_stmt(&stmt)?;
                }
                let var_count = self.scopes.leave_scope();
                self.chunk
                    .add_code(OpCode::Pop(var_count), b.left_brace_line);
            }
            Statement::If(stmt) => {
                let line = stmt.if_line;
                self.compile_expression(&stmt.cond)?;
                let jif = JumpIfFalsePlaceholder::new(&mut self.chunk, true, line);
                self.compile_stmt(&stmt.then_branch)?;
                if let Some(box ref else_branch) = stmt.else_branch {
                    // fixme: use `else`.line
                    let jmp = JumpPlaceholder::new(&mut self.chunk, line);
                    let else_i = self.chunk.get_next_index();
                    jif.set_target(&mut self.chunk, else_i);
                    self.compile_stmt(&else_branch)?;
                    let res_i = self.chunk.get_next_index();
                    jmp.set_target(&mut self.chunk, res_i);
                } else {
                    let res_i = self.chunk.get_next_index();
                    jif.set_target(&mut self.chunk, res_i);
                }
            }
            Statement::While(stmt) => {
                let start_i = self.chunk.get_next_index();
                self.compile_expression(&stmt.cond)?;
                let jif = JumpIfFalsePlaceholder::new(&mut self.chunk, true, stmt.while_line);
                self.compile_stmt(&stmt.body)?;
                let jmp = JumpPlaceholder::new(&mut self.chunk, stmt.while_line);
                jmp.set_target(&mut self.chunk, start_i);
                let res_i = self.chunk.get_next_index();
                jif.set_target(&mut self.chunk, res_i);
            }
            Statement::For(stmt) => {
                self.scopes.enter_scope();
                if let Some(box ref init) = stmt.init {
                    match init {
                        DeclOrStmt::Decl(l) => {
                            self.compile_var_decl(l)?;
                        }
                        DeclOrStmt::Stmt(Statement::Expr(l)) => {
                            self.compile_expression(&l.expr)?;
                        }
                        _ => panic!("for init is not decl or expr, but {:?}", init),
                    }
                }
                let line = stmt.for_line;
                let start_i = self.chunk.get_next_index();
                let jif = if let Some(box ref cond) = stmt.cond {
                    self.compile_expression(cond)?;
                    Some(JumpIfFalsePlaceholder::new(&mut self.chunk, true, line))
                } else {
                    None
                };
                self.compile_stmt(&stmt.body)?;
                if let Some(post) = &stmt.post {
                    self.compile_expression(post)?;
                    self.chunk.add_code(OpCode::Pop(1), line);
                }
                JumpPlaceholder::new(&mut self.chunk, line).set_target(&mut self.chunk, start_i);
                if let Some(jif) = jif {
                    let res_i = self.chunk.get_next_index();
                    jif.set_target(&mut self.chunk, res_i);
                }
                let var_cnt = self.scopes.leave_scope();
                self.chunk.add_code(OpCode::Pop(var_cnt), line);
            }
        };
        Ok(())
    }

    fn compile_expression(&mut self, expr: &'_ Expression) -> Result<(), InterpreteError> {
        match &expr {
            Expression::Literal(l) => {
                let line = l.line;
                match &l.value {
                    LiteralValue::Number(n) => {
                        self.chunk.add_code(OpCode::LoadNumber(*n), line);
                    }
                    LiteralValue::String(s) => {
                        self.chunk.add_const_str(s.clone(), line);
                    }
                    LiteralValue::True => {
                        self.chunk.add_code(OpCode::LoadTrue, line);
                    }
                    LiteralValue::False => {
                        self.chunk.add_code(OpCode::LoadFalse, line);
                    }
                    LiteralValue::Nil => {
                        self.chunk.add_code(OpCode::LoadNil, line);
                    }
                };
            }
            Expression::Unary(u) => {
                let op_code = match u.op {
                    TokenType::Minus => (OpCode::Negate),
                    TokenType::Bang => (OpCode::Not),
                    _ => unreachable!(),
                };
                self.compile_expression(&u.right)?;
                self.chunk.add_code(op_code, u.op_line);
            }
            Expression::Binary(b) => {
                self.compile_expression(&b.left)?;
                let line = b.op_line;
                match b.op {
                    TokenType::And => {
                        let jif = JumpIfFalsePlaceholder::new(&mut self.chunk, false, line);
                        self.compile_expression(&b.right)?;
                        let jres = JumpPlaceholder::new(&mut self.chunk, line);
                        let res_i = self.chunk.get_next_index();
                        jif.set_target(&mut self.chunk, res_i);
                        jres.set_target(&mut self.chunk, res_i);
                    }
                    TokenType::Or => {
                        let jif = JumpIfFalsePlaceholder::new(&mut self.chunk, false, line);
                        let jres = JumpPlaceholder::new(&mut self.chunk, line);
                        let rhs_i = self.chunk.get_next_index();
                        jif.set_target(&mut self.chunk, rhs_i);
                        self.compile_expression(&b.right)?;
                        let res_i = self.chunk.get_next_index();
                        jres.set_target(&mut self.chunk, res_i);
                    }
                    TokenType::EqualEqual => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Equal, line);
                    }
                    TokenType::BangEqual => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Equal, line);
                        self.chunk.add_code(OpCode::Not, line);
                    }
                    TokenType::Less => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Less, line);
                    }
                    TokenType::LessEqual => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Greater, line);
                        self.chunk.add_code(OpCode::Not, line);
                    }
                    TokenType::Greater => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Greater, line);
                    }
                    TokenType::GreaterEqual => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Less, line);
                        self.chunk.add_code(OpCode::Not, line);
                    }
                    TokenType::Plus => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Add, line);
                    }
                    TokenType::Minus => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Subtract, line);
                    }
                    TokenType::Star => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Multiply, line);
                    }
                    TokenType::Slash => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Divide, line);
                    }
                    _ => unreachable!(),
                };
            }
            Expression::Grouping(g) => self.compile_expression(&g)?,
            &Expression::Variable(v) => {
                if let Some(idx) = self.scopes.position(v.name) {
                    self.chunk.add_code(OpCode::LoadLocalVar(idx), v.line);
                } else {
                    self.chunk.add_code(
                        OpCode::LoadGlobalVar(self.str_pool.register(v.name)),
                        v.line,
                    );
                }
            }
            Expression::Assignment(a) => {
                self.compile_expression(&a.expr)?;
                if let Some(idx) = self.scopes.position(a.var_name) {
                    self.chunk.add_code(OpCode::SetLobalVar(idx), a.op_line);
                } else {
                    self.chunk.add_code(
                        OpCode::SetGlobalVar(self.str_pool.register(a.var_name)),
                        a.op_line,
                    );
                }
            }
            Expression::Call(c) => {
                self.compile_expression(&c.callee)?;
                for ele in c.args.iter() {
                    self.compile_expression(ele)?;
                }
                self.chunk.add_code(
                    OpCode::Call(c.args.len().try_into().unwrap()),
                    c.left_paren_line,
                );
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {

    use crate::ast::parse_source;

    use super::*;
    #[test]
    fn test_compile_program() {
        let program = parse_source("print 1;".as_bytes()).unwrap();
        let str_pool = StrPool::new();
        let chunk = CompileRun::compile(&program, &str_pool).unwrap();
        chunk.print_chunk();
    }

    #[test]
    fn test_str_pool() {
        let str_pool = StrPool::new();
        let s1 = str_pool.register("hello");
        let s2 = str_pool.register("hello");
        assert_eq!(s1, s2);
    }
}

struct JumpPlaceholder {
    jump_i: u16,
}

impl JumpPlaceholder {
    fn new<Str>(chunk: &mut Chunk<Str>, src_line: u32) -> Self
    where
        Str: Deref<Target = str> + Debug,
    {
        let jump_i = chunk.get_next_index();
        chunk.add_code(OpCode::Jump(u16::MAX), src_line);
        Self { jump_i }
    }
    fn set_target<Str>(&self, chunk: &mut Chunk<Str>, target_i: u16)
    where
        Str: Deref<Target = str> + Debug,
    {
        chunk.set(self.jump_i, OpCode::Jump(target_i));
    }
}

struct JumpIfFalsePlaceholder {
    jump_i: u16,
    pop_value: bool,
}

impl JumpIfFalsePlaceholder {
    fn new<Str>(chunk: &mut Chunk<Str>, pop_value: bool, src_line: u32) -> Self
    where
        Str: Deref<Target = str> + Debug,
    {
        let jump_i = chunk.get_next_index();
        chunk.add_code(
            OpCode::JumpIfFalse(JumpIfParam {
                pop_value,
                target: u16::MAX,
            }),
            src_line,
        );
        Self { jump_i, pop_value }
    }
    fn set_target<Str>(&self, chunk: &mut Chunk<Str>, target: u16)
    where
        Str: Deref<Target = str> + Debug,
    {
        chunk.set(
            self.jump_i,
            OpCode::JumpIfFalse(JumpIfParam {
                pop_value: self.pop_value,
                target,
            }),
        );
    }
}
