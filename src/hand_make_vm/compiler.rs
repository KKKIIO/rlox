use std::{
    cell::{Ref, RefCell},
    rc::Rc,
};

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
        let idx = if let Some(i) = self
            .pool
            .borrow()
            .iter()
            .position(|n| (*n).as_ref() == name)
        {
            i
        } else {
            let mut p = self.pool.borrow_mut();
            p.push(name.to_string().into_boxed_str().into());
            p.len() - 1
        };
        Ref::map(self.pool.borrow(), |p| &p[idx]).clone()
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
                    chunk.add_code(
                        OpCode::SetGlobalVar(str_pool.register(d.ast.name)),
                        d.get_line(),
                    );
                } else {
                    chunk.add_code(OpCode::LoadNil, d.get_line());
                    chunk.add_code(
                        OpCode::SetGlobalVar(str_pool.register(d.ast.name)),
                        d.get_line(),
                    );
                }
            }
            &DeclOrStmt::Stmt(ref stmt) => match &stmt.ast {
                Statement::Expression(expr) => {
                    self.compile_expression(chunk, expr, str_pool)?;
                }
                Statement::Print(expr) => {
                    self.compile_expression(chunk, expr, str_pool)?;
                    chunk.build_for(stmt.get_line()).add_code(OpCode::Print);
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
                let mut builder = chunk.build_for(expr.get_line());
                match l {
                    Literal::Number(n) => builder.add_code(OpCode::LoadNumber(*n)),
                    Literal::String(s) => builder.add_const_str(s.clone()),
                    Literal::True => builder.add_code(OpCode::LoadTrue),
                    Literal::False => builder.add_code(OpCode::LoadFalse),
                    Literal::Nil => builder.add_code(OpCode::LoadNil),
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
                let mut builder = chunk.build_for(expr.get_line());
                match b.op {
                    Operator::Equal => builder.add_code(OpCode::Equal),
                    Operator::NotEqual => builder.add_code(OpCode::Equal).add_code(OpCode::Not),
                    Operator::Less => builder.add_code(OpCode::Less),
                    Operator::LessEqual => builder.add_code(OpCode::Greater).add_code(OpCode::Not),
                    Operator::Greater => builder.add_code(OpCode::Greater),
                    Operator::GreaterEqual => builder.add_code(OpCode::Less).add_code(OpCode::Not),
                    Operator::Add => builder.add_code(OpCode::Add),
                    Operator::Subtract => builder.add_code(OpCode::Subtract),
                    Operator::Multiply => builder.add_code(OpCode::Multiply),
                    Operator::Divide => builder.add_code(OpCode::Divide),
                };
            }
            Expression::Grouping(g) => self.compile_expression(chunk, &g, str_pool)?,
            &Expression::Variable(v) => {
                chunk.add_code(OpCode::LoadGlobalVar(str_pool.register(v)), expr.get_line());
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
}
