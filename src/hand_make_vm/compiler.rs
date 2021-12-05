use crate::ast::{
    expression::{Expression, Literal, Operator, Unary},
    parse::LocatedAst,
    program::Program,
    statement::{DeclOrStmt, Statement},
};

use super::vm::{Chunk, OpCode};

pub struct Compiler {}
impl Compiler {
    pub fn new() -> Compiler {
        return Compiler {};
    }
    pub fn compile_program(&self, program: &Program) -> Chunk {
        let mut chunk = Chunk::new();
        for stmt in program.statements.iter() {
            self.compile_statement(&mut chunk, &stmt);
        }
        chunk
    }

    pub fn compile_statement<'a, 'c>(&self, chunk: &mut Chunk, ds: &DeclOrStmt<'a>) {
        match ds {
            &DeclOrStmt::Decl(ref d) => {
                if let Some(init_expr) = &d.ast.init_expr {
                    let name_idx = chunk.add_global_var(d.ast.name.to_string());
                    self.compile_expression(chunk, init_expr);
                    chunk.add_code(OpCode::SetGlobalVar(name_idx), d.get_line());
                } else {
                    let name_idx = chunk.add_global_var(d.ast.name.to_string());
                    chunk
                        .build_for(d.get_line())
                        .add_code(OpCode::LoadNil)
                        .add_code(OpCode::SetGlobalVar(name_idx));
                }
            }
            &DeclOrStmt::Stmt(ref stmt) => match &stmt.ast {
                Statement::Expression(expr) => {
                    self.compile_expression(chunk, expr);
                }
                Statement::Print(expr) => {
                    self.compile_expression(chunk, expr);
                    chunk.build_for(stmt.get_line()).add_code(OpCode::Print);
                }
            },
        }
    }
    fn compile_expression(&self, chunk: &mut Chunk, expr: &LocatedAst<Expression>) {
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
                self.compile_expression(chunk, u_expr);
                chunk.build_for(expr.get_line()).add_code(op_code);
            }
            Expression::Binary(b) => {
                self.compile_expression(chunk, &b.left);
                self.compile_expression(chunk, &b.right);
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
            Expression::Grouping(g) => self.compile_expression(chunk, &g),
            Expression::Variable(_) => todo!(),
        }
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
        let chunk = compiler.compile_program(&program);
        chunk.print_chunk("test");
    }
}
