use core::fmt::Debug;
use std::{cell::RefCell, ops::Deref, rc::Rc};

use crate::ast::{
    expression::{Expression, Operator, Unary},
    parse::LocatedAst,
    primary::Literal,
    program::Program,
    statement::{DeclOrStmt, Statement},
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

    pub fn compile_decl_or_stmt(
        &mut self,
        ds: &LocatedAst<DeclOrStmt<'_>>,
    ) -> Result<(), InterpreteError> {
        match ds.ast {
            DeclOrStmt::Decl(ref d) => {
                if let Some(init_expr) = &d.init_expr {
                    self.compile_expression(init_expr)?;
                } else {
                    self.chunk.build_for(ds).code(OpCode::LoadNil);
                }
                if !self.scopes.is_empty() {
                    self.scopes
                        .new_var(self.str_pool.register(&d.name))
                        .map_err(|e| InterpreteError {
                            message: e.to_string(),
                            line: ds.get_line(),
                        })?;
                } else {
                    self.chunk
                        .build_for(ds)
                        .code(OpCode::DefGlobalVar(self.str_pool.register(d.name)));
                }
            }
            DeclOrStmt::Stmt(ref stmt) => {
                self.compile_stmt(stmt, ds.get_line())?;
            }
        };
        Ok(())
    }

    pub fn compile_stmt(&mut self, stmt: &Statement<'_>, line: u32) -> Result<(), InterpreteError> {
        match stmt {
            Statement::Expr(expr) => {
                self.compile_expression(expr)?;
                self.chunk.add_code(OpCode::Pop(1), line);
            }
            Statement::Print(expr) => {
                self.compile_expression(expr)?;
                self.chunk.add_code(OpCode::Print, line);
            }
            Statement::Block(statements) => {
                self.scopes.enter_scope();
                for stmt in statements.iter() {
                    self.compile_decl_or_stmt(&stmt)?;
                }
                let var_count = self.scopes.leave_scope();
                self.chunk.add_code(OpCode::Pop(var_count), line);
            }
            Statement::If(stmt) => {
                self.compile_expression(&stmt.cond)?;
                let jif = JumpIfFalsePlaceholder::new(&mut self.chunk, true, line);
                self.compile_stmt(&stmt.then_branch.ast, stmt.then_branch.get_line())?;
                if let Some(box ref else_branch) = stmt.else_branch {
                    let jmp = JumpPlaceholder::new(&mut self.chunk, line);
                    let else_i = self.chunk.get_next_index();
                    jif.set_target(&mut self.chunk, else_i);
                    self.compile_stmt(&else_branch.ast, else_branch.get_line())?;
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
                let jif = JumpIfFalsePlaceholder::new(&mut self.chunk, true, line);
                self.compile_stmt(&stmt.body.ast, stmt.body.get_line())?;
                let jmp = JumpPlaceholder::new(&mut self.chunk, line);
                jmp.set_target(&mut self.chunk, start_i);
                let res_i = self.chunk.get_next_index();
                jif.set_target(&mut self.chunk, res_i);
            }
        };
        Ok(())
    }

    fn compile_expression(
        &mut self,
        expr: &'_ LocatedAst<Expression>,
    ) -> Result<(), InterpreteError> {
        match &expr.ast {
            Expression::Literal(l) => {
                let mut builder = self.chunk.build_for(expr);
                match l {
                    Literal::Number(n) => builder.code(OpCode::LoadNumber(*n)),
                    Literal::String(s) => builder.add_const_str(s.clone()),
                    Literal::True => builder.code(OpCode::LoadTrue),
                    Literal::False => builder.code(OpCode::LoadFalse),
                    Literal::Nil => builder.code(OpCode::LoadNil),
                };
            }
            Expression::Unary(u) => {
                let (op_code, u_expr) = match u {
                    Unary::Negative(n) => (OpCode::Negate, n),
                    Unary::Not(n) => (OpCode::Not, n),
                };
                self.compile_expression(u_expr)?;
                self.chunk.add_code(op_code, expr.get_line());
            }
            Expression::Binary(b) => {
                self.compile_expression(&b.left)?;
                match b.op {
                    Operator::LogicAnd => {
                        let jif =
                            JumpIfFalsePlaceholder::new(&mut self.chunk, false, expr.get_line());
                        self.compile_expression(&b.right)?;
                        let jres = JumpPlaceholder::new(&mut self.chunk, expr.get_line());
                        let res_i = self.chunk.get_next_index();
                        jif.set_target(&mut self.chunk, res_i);
                        jres.set_target(&mut self.chunk, res_i);
                    }
                    Operator::LogicOr => {
                        let jif =
                            JumpIfFalsePlaceholder::new(&mut self.chunk, false, expr.get_line());
                        let jres = JumpPlaceholder::new(&mut self.chunk, expr.get_line());
                        let rhs_i = self.chunk.get_next_index();
                        jif.set_target(&mut self.chunk, rhs_i);
                        self.compile_expression(&b.right)?;
                        let res_i = self.chunk.get_next_index();
                        jres.set_target(&mut self.chunk, res_i);
                    }
                    Operator::Equal => {
                        self.compile_expression(&b.right)?;
                        let mut builder = self.chunk.build_for(expr);
                        builder.code(OpCode::Equal);
                    }
                    Operator::NotEqual => {
                        self.compile_expression(&b.right)?;
                        let mut builder = self.chunk.build_for(expr);
                        builder.code(OpCode::Equal).code(OpCode::Not);
                    }
                    Operator::Less => {
                        self.compile_expression(&b.right)?;
                        let mut builder = self.chunk.build_for(expr);
                        builder.code(OpCode::Less);
                    }
                    Operator::LessEqual => {
                        self.compile_expression(&b.right)?;
                        let mut builder = self.chunk.build_for(expr);
                        builder.code(OpCode::Greater).code(OpCode::Not);
                    }
                    Operator::Greater => {
                        self.compile_expression(&b.right)?;
                        let mut builder = self.chunk.build_for(expr);
                        builder.code(OpCode::Greater);
                    }
                    Operator::GreaterEqual => {
                        self.compile_expression(&b.right)?;
                        let mut builder = self.chunk.build_for(expr);
                        builder.code(OpCode::Less).code(OpCode::Not);
                    }
                    Operator::Add => {
                        self.compile_expression(&b.right)?;
                        let mut builder = self.chunk.build_for(expr);
                        builder.code(OpCode::Add);
                    }
                    Operator::Subtract => {
                        self.compile_expression(&b.right)?;
                        let mut builder = self.chunk.build_for(expr);
                        builder.code(OpCode::Subtract);
                    }
                    Operator::Multiply => {
                        self.compile_expression(&b.right)?;
                        let mut builder = self.chunk.build_for(expr);
                        builder.code(OpCode::Multiply);
                    }
                    Operator::Divide => {
                        self.compile_expression(&b.right)?;
                        let mut builder = self.chunk.build_for(expr);
                        builder.code(OpCode::Divide);
                    }
                };
            }
            Expression::Grouping(g) => self.compile_expression(&g)?,
            &Expression::Variable(v) => {
                if let Some(idx) = self.scopes.position(v) {
                    self.chunk.build_for(expr).code(OpCode::LoadLocalVar(idx));
                } else {
                    self.chunk
                        .build_for(expr)
                        .code(OpCode::LoadGlobalVar(self.str_pool.register(v)));
                }
            }
            Expression::Assignment(a) => {
                self.compile_expression(&a.expr)?;
                if let Some(idx) = self.scopes.position(a.id) {
                    self.chunk.build_for(expr).code(OpCode::SetLobalVar(idx));
                } else {
                    self.chunk
                        .build_for(expr)
                        .code(OpCode::SetGlobalVar(self.str_pool.register(a.id)));
                }
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
        let program = parse_source("print 1;".into()).unwrap();
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
