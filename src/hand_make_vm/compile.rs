use std::{cell::RefCell, rc::Rc};

use crate::ast::{
    expression::{Expression, Literal, Operator, Unary},
    parse::LocatedAst,
    program::Program,
    statement::{DeclOrStmt, Statement},
};

use super::{
    error::InterpreteError,
    vm::{Chunk, OpCode},
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
            run.compile_statement(&stmt)?;
        }
        Ok(run.chunk)
    }

    pub fn compile_statement(
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
            DeclOrStmt::Stmt(ref stmt) => match &stmt {
                Statement::Expression(expr) => {
                    self.compile_expression(expr)?;
                    self.chunk.add_code(OpCode::Pop(1), ds.get_line());
                }
                Statement::Print(expr) => {
                    self.compile_expression(expr)?;
                    self.chunk.add_code(OpCode::Print, ds.get_line());
                }
                Statement::Block(statements) => {
                    self.scopes.enter_scope();
                    for stmt in statements.iter() {
                        self.compile_statement(&stmt)?;
                    }
                    let var_count = self.scopes.leave_scope();
                    self.chunk.build_for(ds).code(OpCode::Pop(var_count));
                }
            },
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
                self.compile_expression(&b.right)?;
                let mut builder = self.chunk.build_for(expr);
                match b.op {
                    Operator::Equal => builder.code(OpCode::Equal),
                    Operator::NotEqual => builder.code(OpCode::Equal).code(OpCode::Not),
                    Operator::Less => builder.code(OpCode::Less),
                    Operator::LessEqual => builder.code(OpCode::Greater).code(OpCode::Not),
                    Operator::Greater => builder.code(OpCode::Greater),
                    Operator::GreaterEqual => builder.code(OpCode::Less).code(OpCode::Not),
                    Operator::Add => builder.code(OpCode::Add),
                    Operator::Subtract => builder.code(OpCode::Subtract),
                    Operator::Multiply => builder.code(OpCode::Multiply),
                    Operator::Divide => builder.code(OpCode::Divide),
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
        chunk.print_chunk("test");
    }

    #[test]
    fn test_str_pool() {
        let str_pool = StrPool::new();
        let s1 = str_pool.register("hello");
        let s2 = str_pool.register("hello");
        assert_eq!(s1, s2);
    }
}
