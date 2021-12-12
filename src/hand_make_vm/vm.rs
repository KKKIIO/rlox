use core::fmt::Debug;
use std::collections::HashMap;
use std::fmt::Display;
use std::{convert::TryFrom, ops::Deref};

use gpoint::GPoint;

use crate::ast::parse::LocatedAst;

use super::error::InterpreteError;

#[derive(Debug, PartialEq)]
pub enum OpCode<Str>
where
    Str: Deref<Target = str> + Debug,
{
    LoadNil,
    LoadFalse,
    LoadTrue,
    LoadNumber(f64),
    LoadConstStr(u8),
    LoadConstStrLong(u32),
    LoadVar(Str),
    SetVar(Str),
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
    Pop,
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

pub struct Chunk<Str>
where
    Str: Deref<Target = str> + Debug,
{
    pub codes: Vec<OpCode<Str>>,
    lines: Vec<u32>,
    pub const_str_pool: Vec<String>,
}

impl<Str> Chunk<Str>
where
    Str: Deref<Target = str> + Debug,
{
    pub fn new() -> Chunk<Str> {
        return Chunk {
            codes: vec![],
            lines: vec![],
            const_str_pool: vec![],
        };
    }

    pub fn build_for<'c, T>(&'c mut self, ast: &LocatedAst<T>) -> ChunkBuilder<'c, Str> {
        ChunkBuilder {
            chunk: self,
            line: ast.get_line(),
        }
    }

    pub fn add_code(&mut self, code: OpCode<Str>, line: u32) {
        assert_eq!(self.codes.len(), self.lines.len());
        self.codes.push(code);
        self.lines.push(line);
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

pub struct ChunkBuilder<'c, Str>
where
    Str: Deref<Target = str> + Debug,
{
    chunk: &'c mut Chunk<Str>,
    line: u32,
}

impl<'c, Str> ChunkBuilder<'c, Str>
where
    Str: Deref<Target = str> + Debug,
{
    pub fn code(&mut self, code: OpCode<Str>) -> &mut Self {
        self.chunk.add_code(code, self.line);
        self
    }

    pub fn add_const_str(&mut self, str: String) -> &mut Self {
        let ref mut chunk = self.chunk;
        let idx = chunk.const_str_pool.len();
        chunk.const_str_pool.push(str);
        let code = if let Ok(i) = u8::try_from(idx) {
            OpCode::LoadConstStr(i)
        } else {
            OpCode::LoadConstStrLong(idx as u32)
        };
        chunk.add_code(code, self.line);
        self
    }
}
struct GlobalEnvironment {
    variables: HashMap<String, Value>,
}

pub struct VM {
    global_env: GlobalEnvironment,
}

static ARITHMETIC_OPERAND_ERR_MSG: &'static str = "Operand must be a number.";
static ARITHMETIC_OPERANDS_ERR_MSG: &'static str = "Operands must be numbers.";
static ADD_OPERANDS_ERR_MSG: &'static str = "Operands must be two numbers or two strings.";

impl VM {
    pub fn new() -> VM {
        VM {
            global_env: GlobalEnvironment {
                variables: HashMap::new(),
            },
        }
    }

    pub fn run<Str>(&mut self, chunk: &mut Chunk<Str>) -> Result<(), InterpreteError>
    where
        Str: Deref<Target = str> + Debug,
    {
        let mut stack = vec![];
        let mut ip = 0;
        while ip < chunk.codes.len() {
            let curr_ip = ip;
            ip += 1;
            let op_code = &chunk.codes[curr_ip];

            // if cfg!(debug_assertions) {
            //     let line = if ip > 0 && chunk.lines[ip] == chunk.lines[ip - 1] {
            //         "   |".to_string()
            //     } else {
            //         format!("{:4}", chunk.lines[ip])
            //     };
            //     println!("{:04}.\t{} {:?}", ip, line, op_code);
            // }

            match op_code {
                &OpCode::LoadNumber(n) => stack.push(Value::Number(n)),
                &OpCode::LoadConstStr(i) => {
                    let s = &chunk.const_str_pool[usize::from(i)];
                    stack.push(Value::String(s.clone()));
                }
                &OpCode::LoadConstStrLong(i) => {
                    let s = &chunk.const_str_pool[usize::try_from(i).unwrap()];
                    stack.push(Value::String(s.clone()));
                }
                OpCode::LoadVar(name) => {
                    let v = self
                        .global_env
                        .variables
                        .get(name.deref())
                        .ok_or(InterpreteError {
                            message: format!("Undefined variable '{}'.", name.deref()),
                            line: chunk.get_line(curr_ip),
                        })?;
                    stack.push(v.clone());
                }
                OpCode::SetVar(name) => {
                    let value = stack.last().unwrap().clone();
                    if let Some(v) = self.global_env.variables.get_mut(name.deref()) {
                        *v = value;
                    } else {
                        self.global_env.variables.insert(name.to_string(), value);
                    }
                }
                OpCode::Add => {
                    let b_idx = stack.len() - 1;
                    let a_idx = b_idx - 1;
                    match (&stack[b_idx], &stack[a_idx]) {
                        (Value::Number(_), Value::Number(_)) => (),
                        (Value::String(_), Value::String(_)) => (),
                        _ => {
                            return Err(InterpreteError {
                                message: ADD_OPERANDS_ERR_MSG.to_string(),
                                line: chunk.get_line(curr_ip),
                            });
                        }
                    }
                    let b = stack.pop().unwrap();
                    let a = stack.pop().unwrap();
                    match a {
                        Value::String(mut str_a) => match b {
                            Value::String(str_b) => {
                                str_a.push_str(&str_b);
                                stack.push(Value::String(str_a));
                            }
                            _ => unreachable!(),
                        },
                        Value::Number(a) => match b {
                            Value::Number(b) => stack.push(Value::Number(a + b)),
                            _ => unreachable!(),
                        },
                        _ => unreachable!(),
                    }
                }
                OpCode::Subtract => {
                    let (a, b) = Self::try_pop2num(&mut stack, chunk.get_line(curr_ip))?;
                    stack.push(Value::Number(a - b));
                }
                OpCode::Multiply => {
                    let (a, b) = Self::try_pop2num(&mut stack, chunk.get_line(curr_ip))?;
                    stack.push(Value::Number(a * b));
                }
                OpCode::Divide => {
                    let (a, b) = Self::try_pop2num(&mut stack, chunk.get_line(curr_ip))?;
                    stack.push(Value::Number(a / b));
                }
                OpCode::Negate => {
                    let v = stack.last_mut().unwrap();
                    match v {
                        Value::Number(n) => *n = -*n,
                        _ => {
                            return Err(InterpreteError {
                                message: ARITHMETIC_OPERAND_ERR_MSG.to_string(),
                                line: chunk.get_line(curr_ip),
                            })
                        }
                    }
                }
                OpCode::Print => println!("{}", stack.pop().unwrap()),
                OpCode::LoadNil => stack.push(Value::Nil),
                OpCode::LoadTrue => stack.push(Value::Bool(true)),
                OpCode::LoadFalse => stack.push(Value::Bool(false)),
                OpCode::Equal => {
                    let b = stack.pop().unwrap();
                    let a = stack.pop().unwrap();
                    stack.push(Value::Bool(a == b));
                }
                OpCode::Less => {
                    let (a, b) = Self::try_pop2num(&mut stack, chunk.get_line(curr_ip))?;
                    stack.push(Value::Bool(a < b));
                }
                OpCode::Greater => {
                    let (a, b) = Self::try_pop2num(&mut stack, chunk.get_line(curr_ip))?;
                    stack.push(Value::Bool(a > b));
                }
                OpCode::Not => {
                    let v = stack.pop().unwrap();
                    stack.push(Value::Bool(Self::is_falsey(&v)));
                }
                OpCode::Pop => {
                    stack.pop().unwrap();
                }
            };
        }
        Ok(())
    }
    fn try_pop2num(stack: &mut Vec<Value>, line: u32) -> Result<(f64, f64), InterpreteError> {
        let len = stack.len();
        let bi = len - 1;
        let ai = bi - 1;
        let b = match stack[bi] {
            Value::Number(n) => n,
            _ => {
                return Err(InterpreteError {
                    message: ARITHMETIC_OPERANDS_ERR_MSG.to_string(),
                    line,
                })
            }
        };
        let a = match stack[ai] {
            Value::Number(n) => n,
            _ => {
                return Err(InterpreteError {
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
