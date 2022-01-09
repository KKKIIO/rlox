use core::fmt::Debug;
use std::fmt::Display;
use std::{collections::HashMap, convert::TryInto};
use std::{convert::TryFrom, ops::Deref};

use gpoint::GPoint;

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
    LoadGlobalVar(Str),
    DefGlobalVar(Str),
    SetGlobalVar(Str),
    LoadLocalVar(u8),
    SetLobalVar(u8),
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
    Pop(u8),
    Jump(u16),
    JumpIfFalse(JumpIfParam),
    Call(u8),
    // Return,
}

#[derive(Debug, PartialEq)]
pub struct JumpIfParam {
    pub target: u16,
    pub pop_value: bool,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    Nil,
    Bool(bool),
    Number(f64),
    String(String),
    NativeFunc(&'static NativeFun),
}

#[derive(Clone, Copy)]
pub struct NativeFun {
    pub name: &'static str,
    pub fun: fn(Vec<Value>) -> Result<Value, InterpreteError>,
}
impl Debug for NativeFun {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<NativeFun {}>", self.name)
    }
}
impl PartialEq for NativeFun {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

const NATIVE_FUN_TIME: NativeFun = NativeFun {
    name: "time",
    fun: native_fun_time,
};

fn native_fun_time(_args: Vec<Value>) -> Result<Value, InterpreteError> {
    Ok(Value::Number(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs_f64(),
    ))
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Nil => write!(f, "nil"),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Number(n) => write!(f, "{}", GPoint(*n)),
            Value::String(s) => write!(f, "{}", s),
            Value::NativeFunc(nf) => write!(f, "{:?}", nf),
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

    pub fn add_code(&mut self, code: OpCode<Str>, line: u32) -> u16 {
        assert_eq!(self.codes.len(), self.lines.len());
        let i = self.codes.len().try_into().unwrap();
        self.codes.push(code);
        self.lines.push(line);
        i
    }

    pub fn add_const_str(&mut self, str: String, line: u32) {
        let idx = self.const_str_pool.len();
        self.const_str_pool.push(str);
        let code = if let Ok(i) = u8::try_from(idx) {
            OpCode::LoadConstStr(i)
        } else {
            OpCode::LoadConstStrLong(idx as u32)
        };
        self.add_code(code, line);
    }

    pub fn get_next_index(&mut self) -> u16 {
        self.codes.len() as u16
    }

    pub fn set(&mut self, i: u16, code: OpCode<Str>) {
        self.codes[i as usize] = code;
    }

    pub fn get_line(&self, ip: usize) -> u32 {
        self.lines[ip]
    }

    pub fn print_chunk(&self) {
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
        let mut variables = HashMap::new();
        variables.insert(
            NATIVE_FUN_TIME.name.to_string(),
            Value::NativeFunc(&NATIVE_FUN_TIME),
        );
        VM {
            global_env: GlobalEnvironment { variables },
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
                OpCode::DefGlobalVar(name) => {
                    let value = stack.pop().unwrap();
                    if let Some(v) = self.global_env.variables.get_mut(name.deref()) {
                        *v = value;
                    } else {
                        self.global_env.variables.insert(name.to_string(), value);
                    }
                }
                OpCode::LoadGlobalVar(name) => {
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
                OpCode::SetGlobalVar(name) => {
                    let v =
                        self.global_env
                            .variables
                            .get_mut(name.deref())
                            .ok_or(InterpreteError {
                                message: format!("Undefined variable '{}'.", name.deref()),
                                line: chunk.get_line(curr_ip),
                            })?;
                    *v = stack.last().unwrap().clone();
                }
                &OpCode::LoadLocalVar(local_idx) => {
                    let v = stack
                        .get(local_idx as usize)
                        .expect(
                            format!(
                                "Local variable index out of bounds, curr_ip={}, i={}, stack={:?}",
                                curr_ip, local_idx, stack
                            )
                            .as_str(),
                        )
                        .clone();
                    stack.push(v);
                }
                &OpCode::SetLobalVar(i) => {
                    stack[i as usize] = stack.last().unwrap().clone();
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
                &OpCode::Pop(count) => {
                    let rest = stack.len().checked_sub(count.into()).expect(
                        format!(
                            "stack underflow, stack.len={}, pop.count={}",
                            stack.len(),
                            count
                        )
                        .as_str(),
                    );
                    stack.truncate(rest);
                }
                &OpCode::Jump(target_ip) => {
                    ip = target_ip as usize;
                    continue;
                }
                &OpCode::JumpIfFalse(JumpIfParam { target, pop_value }) => {
                    let falsey = Self::is_falsey(&stack.last().unwrap());
                    if pop_value {
                        stack.pop();
                    }
                    if falsey {
                        ip = target as usize;
                        continue;
                    }
                }
                &OpCode::Call(args_count) => {
                    let args = stack.drain((stack.len() - args_count as usize)..).collect();
                    let callee = stack.pop().unwrap();
                    match callee {
                        Value::NativeFunc(nf) => {
                            let result = (nf.fun)(args)?;
                            stack.push(result);
                        }
                        _ => {
                            return Err(InterpreteError {
                                message: "Can only call functions and classes.".to_string(),
                                line: chunk.get_line(curr_ip),
                            });
                        }
                    }
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
