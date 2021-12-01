use std::error::Error;

use crate::{ast::program::Program, vm::compiler::OpCode};

use self::compiler::{Chunk, Compiler, Value};

use std::convert::TryFrom;

mod compiler;

pub struct VM {
    compiler: Compiler,
    chunk: Option<Chunk>,
    ip: usize,
    stack: Vec<Value>,
}

static ARITHMETIC_OPERANDS_ERR_MSG: &'static str = "Operands must be numbers.";

impl VM {
    pub fn new() -> VM {
        VM {
            compiler: Compiler::new(),
            chunk: None,
            ip: 0,
            stack: vec![],
        }
    }
    pub fn run(&mut self, program: &Program) -> Result<(), Box<dyn Error>> {
        self.chunk = Some(self.compiler.compile_program(program)?);
        let chunk = self.chunk.as_ref().unwrap();
        self.ip = 0;
        while self.ip < chunk.codes.len() {
            let ip = self.ip;
            self.ip += 1;
            let op_code = &chunk.codes[ip];

            if cfg!(debug_assertions) {
                let line = if ip > 0 && chunk.lines[ip] == chunk.lines[ip - 1] {
                    "   |".to_string()
                } else {
                    format!("{:4}", chunk.lines[ip])
                };
                println!("{:04}.\t{} {:?}", ip, line, op_code);
            }

            match op_code {
                OpCode::LoadConst(i) => {
                    let v = chunk.constant_pool[usize::from(*i)].clone();
                    self.stack.push(v);
                }
                OpCode::LoadConstLong(i) => {
                    let v = chunk.constant_pool[usize::try_from(*i).unwrap()].clone();
                    self.stack.push(v);
                }
                OpCode::Add => {
                    let (a, b) = Self::try_pop2num(&mut self.stack)?;
                    self.stack.push(Value::Num(a + b));
                }
                OpCode::Subtract => {
                    let (a, b) = Self::try_pop2num(&mut self.stack)?;
                    self.stack.push(Value::Num(a - b));
                }
                OpCode::Multiply => {
                    let (a, b) = Self::try_pop2num(&mut self.stack)?;
                    self.stack.push(Value::Num(a * b));
                }
                OpCode::Divide => {
                    let (a, b) = Self::try_pop2num(&mut self.stack)?;
                    self.stack.push(Value::Num(a / b));
                }
                OpCode::Negate => {
                    let v = self.stack.last_mut().unwrap();
                    match v {
                        Value::Num(n) => *n = -*n,
                        _ => return Err(ARITHMETIC_OPERANDS_ERR_MSG.into()),
                    }
                }
                OpCode::Return => {
                    println!("{}", self.stack.pop().unwrap());
                    break;
                }
                OpCode::Print => println!("{}", self.stack.pop().unwrap()),
                OpCode::LoadNil => self.stack.push(Value::Nil),
                OpCode::LoadTrue => self.stack.push(Value::Bool(true)),
                OpCode::LoadFalse => self.stack.push(Value::Bool(false)),
                OpCode::Equal => {
                    let b = self.stack.pop().unwrap();
                    let a = self.stack.pop().unwrap();
                    self.stack.push(Value::Bool(a == b));
                }
                OpCode::Less => todo!(),
                OpCode::Greater => todo!(),
                OpCode::Not => {
                    let v = self.stack.pop().unwrap();
                    self.stack.push(Value::Bool(Self::is_falsey(&v)));
                }
            }
        }
        Ok(())
    }
    fn try_pop2num(stack: &mut Vec<Value>) -> Result<(f64, f64), Box<dyn Error>> {
        let len = stack.len();
        let bi = len - 1;
        let ai = bi - 1;
        let b = match stack[bi] {
            Value::Num(n) => n,
            _ => return Err(ARITHMETIC_OPERANDS_ERR_MSG.into()),
        };
        let a = match stack[ai] {
            Value::Num(n) => n,
            _ => return Err(ARITHMETIC_OPERANDS_ERR_MSG.into()),
        };
        stack.pop();
        stack.pop();
        Ok((a, b))
    }
    fn is_falsey(value: &Value) -> bool {
        match value {
            Value::Nil => true,
            Value::Bool(b) => !b,
            _ => false,
        }
    }
}
