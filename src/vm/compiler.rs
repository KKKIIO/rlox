use std::fmt::Display;

use gpoint::GPoint;

use crate::ast::{
    expression::{ExprBranch, Expression, Literal, Operator, Unary},
    program::Program,
    statement::{Statement, StmtBranch},
};
use std::convert::TryFrom;

#[derive(Debug, PartialEq)]
pub enum OpCode {
    LoadNil,
    LoadFalse,
    LoadTrue,
    LoadNumber(f64),
    LoadConstStr(u8),
    LoadConstStrLong(u32),
    Equal,
    Less,
    Greater,
    Add,
    Subtract,
    Multiply,
    Divide,
    Not,
    Negate,
    Print,
    // Return,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    Nil,
    Bool(bool),
    Number(f64),
    String(String),
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Nil => write!(f, "nil"),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Number(n) => write!(f, "{}", GPoint(*n)),
            Value::String(s) => write!(f, "{}", s),
        }
    }
}

pub struct Chunk {
    pub codes: Vec<OpCode>,
    lines: Vec<u32>,
    pub const_str_pool: Vec<String>,
}

impl Chunk {
    pub fn new() -> Chunk {
        return Chunk {
            codes: vec![],
            lines: vec![],
            const_str_pool: vec![],
        };
    }

    pub fn add_code(&mut self, code: OpCode, line: u32) {
        assert_eq!(self.codes.len(), self.lines.len());
        self.codes.push(code);
        self.lines.push(line);
    }

    pub fn add_const_str(&mut self, str: String, line: u32) {
        let idx = self.const_str_pool.len();
        let code = if let Ok(i) = u8::try_from(idx) {
            OpCode::LoadConstStr(i)
        } else {
            OpCode::LoadConstStrLong(u32::try_from(idx).unwrap())
        };
        self.const_str_pool.push(str);
        self.add_code(code, line);
    }

    pub fn get_line(&self, ip: usize) -> u32 {
        self.lines[ip]
    }

    pub fn print_chunk(&self, name: &str) {
        println!("== {} ==", name);
        for (i, code) in self.codes.iter().enumerate() {
            let line = if i > 0 && self.lines[i] == self.lines[i - 1] {
                "   |".to_string()
            } else {
                format!("{:4}", self.lines[i])
            };
            println!("{:04}.\t{} {:?}", i, line, code);
        }
    }
}

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

    pub fn compile_statement<'a>(&self, chunk: &mut Chunk, stmt: &Statement<'a>) {
        match &stmt.branch {
            StmtBranch::Expression(expr) => {
                self.compile_expression(chunk, expr);
            }
            StmtBranch::Print(expr) => {
                self.compile_expression(chunk, &expr);
                chunk.add_code(OpCode::Print, stmt.pos.location_line());
            }
        }
    }
    fn compile_expression<'a>(&self, chunk: &mut Chunk, expr: &Expression<'a>) {
        match &expr.branch {
            ExprBranch::Literal(l) => match l {
                Literal::Number(n) => {
                    chunk.add_code(OpCode::LoadNumber(*n), expr.pos.location_line())
                }
                Literal::String(s) => chunk.add_const_str(s.clone(), expr.pos.location_line()),
                Literal::True => chunk.add_code(OpCode::LoadTrue, expr.pos.location_line()),
                Literal::False => chunk.add_code(OpCode::LoadFalse, expr.pos.location_line()),
                Literal::Nil => chunk.add_code(OpCode::LoadNil, expr.pos.location_line()),
            },
            ExprBranch::Unary(u) => {
                let (op_code, u_expr) = match u {
                    Unary::Negative(n) => (OpCode::Negate, n),
                    Unary::Not(n) => (OpCode::Not, n),
                };
                self.compile_expression(chunk, u_expr);
                chunk.add_code(op_code, expr.pos.location_line());
            }
            ExprBranch::Binary(b) => {
                self.compile_expression(chunk, &b.left);
                self.compile_expression(chunk, &b.right);
                let line = expr.pos.location_line();
                match b.op {
                    Operator::Equal => chunk.add_code(OpCode::Equal, line),
                    Operator::NotEqual => {
                        chunk.add_code(OpCode::Equal, line);
                        chunk.add_code(OpCode::Not, line);
                    }
                    Operator::Less => chunk.add_code(OpCode::Less, line),
                    Operator::LessEqual => {
                        chunk.add_code(OpCode::Greater, line);
                        chunk.add_code(OpCode::Not, line);
                    }
                    Operator::Greater => chunk.add_code(OpCode::Greater, line),
                    Operator::GreaterEqual => {
                        chunk.add_code(OpCode::Less, line);
                        chunk.add_code(OpCode::Not, line);
                    }
                    Operator::Add => chunk.add_code(OpCode::Add, line),
                    Operator::Subtract => chunk.add_code(OpCode::Subtract, line),
                    Operator::Multiply => chunk.add_code(OpCode::Multiply, line),
                    Operator::Divide => chunk.add_code(OpCode::Divide, line),
                };
            }
            ExprBranch::Grouping(g) => self.compile_expression(chunk, &g),
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
