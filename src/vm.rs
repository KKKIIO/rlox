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
pub struct RuntimeError {
    pub message: String,
    pub line: u32,
}

static ARITHMETIC_OPERANDS_ERR_MSG: &'static str = "Operands must be numbers.";
static ADD_OPERANDS_ERR_MSG: &'static str = "Operands must be two numbers or two strings.";

impl VM {
    pub fn new() -> VM {
        VM {
            compiler: Compiler::new(),
            chunk: None,
            ip: 0,
            stack: vec![],
        }
    }
    pub fn run(&mut self, program: &Program) -> Result<(), RuntimeError> {
        self.chunk = Some(self.compiler.compile_program(program));
        let chunk = self.chunk.as_ref().unwrap();
        self.ip = 0;
        while self.ip < chunk.codes.len() {
            let ip = self.ip;
            self.ip += 1;
            let op_code = &chunk.codes[ip];

            // if cfg!(debug_assertions) {
            //     let line = if ip > 0 && chunk.lines[ip] == chunk.lines[ip - 1] {
            //         "   |".to_string()
            //     } else {
            //         format!("{:4}", chunk.lines[ip])
            //     };
            //     println!("{:04}.\t{} {:?}", ip, line, op_code);
            // }

            match op_code {
                &OpCode::LoadNumber(n) => self.stack.push(Value::Number(n)),
                &OpCode::LoadConstStr(i) => {
                    let s = &chunk.const_str_pool[usize::from(i)];
                    self.stack.push(Value::String(s.clone()));
                }
                &OpCode::LoadConstStrLong(i) => {
                    let s = &chunk.const_str_pool[usize::try_from(i).unwrap()];
                    self.stack.push(Value::String(s.clone()));
                }
                OpCode::Add => {
                    let b_idx = self.stack.len() - 1;
                    let a_idx = b_idx - 1;
                    match (&self.stack[b_idx], &self.stack[a_idx]) {
                        (Value::Number(_), Value::Number(_)) => (),
                        (Value::String(_), Value::String(_)) => (),
                        _ => {
                            return Err(RuntimeError {
                                message: ADD_OPERANDS_ERR_MSG.to_string(),
                                line: chunk.get_line(ip),
                            });
                        }
                    }
                    let b = self.stack.pop().unwrap();
                    let a = self.stack.pop().unwrap();
                    match a {
                        Value::String(mut str_a) => match b {
                            Value::String(str_b) => {
                                str_a.push_str(&str_b);
                                self.stack.push(Value::String(str_a));
                            }
                            _ => unreachable!(),
                        },
                        Value::Number(a) => match b {
                            Value::Number(b) => self.stack.push(Value::Number(a + b)),
                            _ => unreachable!(),
                        },
                        _ => unreachable!(),
                    }
                }
                OpCode::Subtract => {
                    let (a, b) = Self::try_pop2num(&mut self.stack, chunk.get_line(ip))?;
                    self.stack.push(Value::Number(a - b));
                }
                OpCode::Multiply => {
                    let (a, b) = Self::try_pop2num(&mut self.stack, chunk.get_line(ip))?;
                    self.stack.push(Value::Number(a * b));
                }
                OpCode::Divide => {
                    let (a, b) = Self::try_pop2num(&mut self.stack, chunk.get_line(ip))?;
                    self.stack.push(Value::Number(a / b));
                }
                OpCode::Negate => {
                    let v = self.stack.last_mut().unwrap();
                    match v {
                        Value::Number(n) => *n = -*n,
                        _ => {
                            return Err(RuntimeError {
                                message: ARITHMETIC_OPERANDS_ERR_MSG.to_string(),
                                line: chunk.get_line(ip),
                            })
                        }
                    }
                }
                // OpCode::Return => {
                //     println!("{}", self.stack.pop().unwrap());
                //     break;
                // }
                OpCode::Print => println!("{}", self.stack.pop().unwrap()),
                OpCode::LoadNil => self.stack.push(Value::Nil),
                OpCode::LoadTrue => self.stack.push(Value::Bool(true)),
                OpCode::LoadFalse => self.stack.push(Value::Bool(false)),
                OpCode::Equal => {
                    let b = self.stack.pop().unwrap();
                    let a = self.stack.pop().unwrap();
                    self.stack.push(Value::Bool(a == b));
                }
                OpCode::Less => {
                    let (a, b) = Self::try_pop2num(&mut self.stack, chunk.get_line(ip))?;
                    self.stack.push(Value::Bool(a < b));
                }
                OpCode::Greater => {
                    let (a, b) = Self::try_pop2num(&mut self.stack, chunk.get_line(ip))?;
                    self.stack.push(Value::Bool(a > b));
                }
                OpCode::Not => {
                    let v = self.stack.pop().unwrap();
                    self.stack.push(Value::Bool(Self::is_falsey(&v)));
                }
            }
        }
        Ok(())
    }
    fn try_pop2num(stack: &mut Vec<Value>, line: u32) -> Result<(f64, f64), RuntimeError> {
        let len = stack.len();
        let bi = len - 1;
        let ai = bi - 1;
        let b = match stack[bi] {
            Value::Number(n) => n,
            _ => {
                return Err(RuntimeError {
                    message: ARITHMETIC_OPERANDS_ERR_MSG.to_string(),
                    line,
                })
            }
        };
        let a = match stack[ai] {
            Value::Number(n) => n,
            _ => {
                return Err(RuntimeError {
                    message: ARITHMETIC_OPERANDS_ERR_MSG.to_string(),
                    line,
                })
            }
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
