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

pub struct Compiler {}
impl Compiler {
    pub fn new() -> Compiler {
        return Compiler {};
    }
    pub fn compile_program(
        &self,
        program: &Program,
        str_pool: &StrPool,
    ) -> Result<Chunk<Rc<str>>, InterpreteError> {
        let mut chunk = Chunk::new();
        for stmt in program.statements.iter() {
            self.compile_statement(&mut chunk, &stmt, str_pool)?;
        }
        Ok(chunk)
    }

    pub fn compile_statement<'a, 'c, 'p>(
        &self,
        chunk: &'c mut Chunk<Rc<str>>,
        ds: &DeclOrStmt<'a>,
        str_pool: &'p StrPool,
    ) -> Result<(), InterpreteError> {
        match ds {
            &DeclOrStmt::Decl(ref d) => {
                if let Some(init_expr) = &d.ast.init_expr {
                    self.compile_expression(chunk, init_expr, str_pool)?;
                } else {
                    chunk.build_for(d).code(OpCode::LoadNil);
                }
                chunk
                    .build_for(d)
                    .code(OpCode::DefVar(str_pool.register(d.ast.name)))
                    .code(OpCode::Pop);
            }
            &DeclOrStmt::Stmt(ref stmt) => match &stmt.ast {
                Statement::Expression(expr) => {
                    self.compile_expression(chunk, expr, str_pool)?;
                    chunk.add_code(OpCode::Pop, stmt.get_line());
                }
                Statement::Print(expr) => {
                    self.compile_expression(chunk, expr, str_pool)?;
                    chunk.add_code(OpCode::Print, stmt.get_line());
                }
            },
        };
        Ok(())
    }

    fn compile_expression<'c, 'p>(
        &self,
        chunk: &'c mut Chunk<Rc<str>>,
        expr: &'_ LocatedAst<Expression>,
        str_pool: &'p StrPool,
    ) -> Result<(), InterpreteError> {
        match &expr.ast {
            Expression::Literal(l) => {
                let mut builder = chunk.build_for(expr);
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
                self.compile_expression(chunk, u_expr, str_pool)?;
                chunk.add_code(op_code, expr.get_line());
            }
            Expression::Binary(b) => {
                self.compile_expression(chunk, &b.left, str_pool)?;
                self.compile_expression(chunk, &b.right, str_pool)?;
                let mut builder = chunk.build_for(expr);
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
            Expression::Grouping(g) => self.compile_expression(chunk, &g, str_pool)?,
            &Expression::Variable(v) => {
                chunk.add_code(OpCode::LoadVar(str_pool.register(v)), expr.get_line());
            }
            Expression::Assignment(a) => {
                self.compile_expression(chunk, &a.expr, str_pool)?;
                chunk.add_code(OpCode::SetVar(str_pool.register(&a.id)), expr.get_line());
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
        let compiler = Compiler {};
        let str_pool = StrPool::new();
        let chunk = compiler.compile_program(&program, &str_pool).unwrap();
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
