use core::fmt::Debug;
use std::{cell::RefCell, collections::HashMap, convert::TryInto};
use std::{convert::TryFrom, ops::Deref};
use std::{fmt::Display, rc::Rc};

use gpoint::GPoint;

use super::{compile::StrPool, error::InterpreteError};

#[derive(Debug, PartialEq)]
pub enum OpCode {
    LoadNil,
    LoadFalse,
    LoadTrue,
    LoadNumber(f64),
    LoadConstStr(u8),
    LoadConstStrLong(u32),
    LoadGlobalVar(u32),
    DefGlobalVar(u32),
    SetGlobalVar(u32),
    LoadLocalVar(u8),
    SetLobalVar(u8),
    LoadUpvalue(u8),
    SetUpvalue(u8),
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
    PopMaybeUpvalue,
    Jump(u16),
    JumpIfFalse(JumpIfParam),
    Call(u8),
    MakeClosure(u32),
    MakeClass(u32),
    Return,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum UpvalueIndex {
    Local(u8),
    Upvalue(u8),
}

#[derive(Debug, PartialEq)]
pub struct JumpIfParam {
    pub target: u16,
    pub pop_value: bool,
}

#[derive(Debug, PartialEq, Clone)]
enum Value<'m, Str>
where
    Str: Deref<Target = str>,
{
    Nil,
    Bool(bool),
    Number(f64),
    String(Str),
    NativeFunc(NativeFun<Self>),
    Closure(Rc<Closure<'m>>),
}

impl<'m, Str> Value<'m, Str>
where
    Str: Deref<Target = str>,
{
    fn as_closure(&self) -> Option<&Rc<Closure<'m>>> {
        if let Self::Closure(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Returns `true` if the value is [`Closure`].
    ///
    /// [`Closure`]: Value::Closure
    fn is_closure(&self) -> bool {
        matches!(self, Self::Closure(..))
    }
}

impl<Str> Display for Value<'_, Str>
where
    Str: Deref<Target = str> + std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Nil => write!(f, "nil"),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Number(n) => write!(f, "{}", GPoint(*n)),
            Value::String(s) => write!(f, "{}", s),
            Value::NativeFunc(nf) => write!(f, "{:?}", nf),
            Value::Closure(c) => write!(f, "<fn {}>", c.fun.name),
        }
    }
}

#[derive(Clone, Copy)]
pub struct NativeFun<V> {
    pub name: &'static str,
    pub fun: fn(Vec<V>) -> Result<V, InterpreteError>,
}
impl<V> Debug for NativeFun<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<native fn>")
    }
}
impl<V> PartialEq for NativeFun<V> {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

#[derive(Debug, PartialEq, Clone)]
struct Closure<'m> {
    fun: &'m FunPrototype,
    upvalues: Box<[Rc<RefCell<Upvalue<'m>>>]>,
}

#[derive(Debug, PartialEq)]
pub struct FunPrototype {
    pub name: Rc<str>,
    pub arity: u8,
    pub codes: Codes,
    pub upvalue_indexes: Box<[UpvalueIndex]>,
}

#[derive(Debug, PartialEq, Clone)]
struct Class<'m> {
    proto: &'m ClassPrototype,
    super_proto: Option<&'m ClassPrototype>,
    fields: HashMap<Rc<str>, Value<'m, Rc<str>>>,
}

#[derive(Debug, PartialEq)]
pub struct ClassPrototype {
    pub name: Rc<str>,
    pub has_super_class: bool,
    pub methods: HashMap<Rc<str>, FunPrototype>,
}

fn native_fun_clock<Str>(_args: Vec<Value<Str>>) -> Result<Value<Str>, InterpreteError>
where
    Str: Deref<Target = str>,
{
    Ok(Value::Number(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs_f64(),
    ))
}

pub struct Chunk<'p> {
    pub codes: Vec<OpCode>,
    lines: Vec<u32>,
    str_pool: &'p StrPool,
}

impl<'p> Chunk<'p> {
    pub fn new(str_pool: &'p StrPool) -> Chunk {
        return Chunk {
            codes: vec![],
            lines: vec![],
            str_pool,
        };
    }

    pub fn add_code(&mut self, code: OpCode, line: u32) -> u16 {
        assert_eq!(self.codes.len(), self.lines.len());
        let i = self.codes.len().try_into().unwrap();
        self.codes.push(code);
        self.lines.push(line);
        i
    }

    pub fn add_const_str(&mut self, str: &'_ str, line: u32) {
        let idx = self.str_pool.register(str);
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

    pub fn set(&mut self, i: u16, code: OpCode) {
        self.codes[i as usize] = code;
    }

    pub fn build(self) -> Codes {
        Codes {
            codes: self.codes,
            lines: self.lines,
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Codes {
    pub codes: Vec<OpCode>,
    lines: Vec<u32>,
}

impl Codes {
    pub fn get_line(&self, ip: usize) -> u32 {
        self.lines[ip]
    }
}

impl Display for Codes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, code) in self.codes.iter().enumerate() {
            if i > 0 && self.lines[i] == self.lines[i - 1] {
                writeln!(f, "   |.\t{} {:?}", i, code)?
            } else {
                writeln!(f, "{:04}.\t{} {:?}", i, self.lines[i], code)?
            }
        }
        Ok(())
    }
}

pub struct Module {
    pub main: Codes,
    pub funs: Box<[FunPrototype]>,
    pub classes: Box<[Rc<ClassPrototype>]>,
}

impl Display for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "main:")?;
        writeln!(f, "{}", self.main)?;
        for (i, fun) in self.funs.iter().enumerate() {
            writeln!(f, "fun(name={}, id={}, arity={})", fun.name, i, fun.arity)?;
            writeln!(f, "{}", fun.codes)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
struct CallFrame<'m> {
    stack_base: usize,
    return_ip: usize,
    return_codes: &'m Codes,
}

#[derive(Debug, PartialEq, Clone)]
enum Upvalue<'m> {
    Open(usize),
    Closed(Value<'m, Rc<str>>),
}

impl Upvalue<'_> {
    fn get_open_index(&self) -> usize {
        match self {
            Upvalue::Open(i) => *i,
            _ => panic!("Upvalue is not open"),
        }
    }

    fn as_open(&self) -> Option<&usize> {
        if let Self::Open(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

pub struct VM<'p> {
    str_pool: &'p StrPool,
}

static ARITHMETIC_OPERAND_ERR_MSG: &'static str = "Operand must be a number.";
static ARITHMETIC_OPERANDS_ERR_MSG: &'static str = "Operands must be numbers.";
static ADD_OPERANDS_ERR_MSG: &'static str = "Operands must be two numbers or two strings.";

fn add_global_var<'m>(
    vars: &mut Vec<Option<Value<'m, Rc<str>>>>,
    id: u32,
    v: Value<'m, Rc<str>>,
) -> () {
    let id = id as usize;
    if id >= vars.len() {
        vars.resize(id + 1, None);
    }
    vars[id] = Some(v);
}

impl<'p> VM<'p> {
    pub fn new(str_pool: &'p StrPool) -> Self {
        VM { str_pool }
    }

    pub fn run<'m>(&mut self, module: &'m Module) -> Result<(), InterpreteError> {
        let mut codes: &'m Codes = &module.main;
        let mut global_variables = vec![];
        add_global_var(
            &mut global_variables,
            self.str_pool.register("clock"),
            Value::NativeFunc(NativeFun {
                name: "clock",
                fun: native_fun_clock,
            }),
        );
        let mut stack = vec![];
        let mut open_upvalues: Vec<Rc<RefCell<Upvalue>>> = vec![];
        let mut call_frames: Vec<CallFrame> = vec![];
        let mut ip = 0;
        loop {
            let curr_ip = ip;
            ip += 1;
            assert!(
                curr_ip < codes.codes.len(),
                "curr_ip={}, call_frames={:?}",
                curr_ip,
                call_frames
            );
            let op_code = &codes.codes[curr_ip];
            match op_code {
                &OpCode::LoadNumber(n) => stack.push(Value::Number(n)),
                &OpCode::LoadConstStr(i) => {
                    stack.push(Value::String(self.str_pool.get(i.into())));
                }
                &OpCode::LoadConstStrLong(i) => {
                    stack.push(Value::String(self.str_pool.get(i).clone()));
                }
                &OpCode::DefGlobalVar(name_id) => {
                    add_global_var(&mut global_variables, name_id, stack.pop().unwrap());
                }
                &OpCode::LoadGlobalVar(name_id) => {
                    let v = global_variables
                        .get(name_id as usize)
                        .and_then(|o| o.as_ref())
                        .ok_or_else(|| InterpreteError {
                            message: format!(
                                "Undefined variable '{}'.",
                                self.str_pool.get(name_id)
                            ),
                            line: codes.get_line(curr_ip),
                        })?;
                    stack.push(v.clone());
                }
                &OpCode::SetGlobalVar(name_id) => {
                    let v = global_variables
                        .get_mut(name_id as usize)
                        .and_then(|o| o.as_mut())
                        .ok_or_else(|| InterpreteError {
                            message: format!(
                                "Undefined variable '{}'.",
                                self.str_pool.get(name_id)
                            ),
                            line: codes.get_line(curr_ip),
                        })?;
                    *v = stack.last().unwrap().clone();
                }
                &OpCode::LoadLocalVar(local_idx) => {
                    let i = call_frames.last().map_or(0, |f| f.stack_base) + (local_idx as usize);
                    let v = stack
                        .get(i)
                        .expect(
                            format!(
                                "Local variable index out of bounds, curr_ip={}, i={}, stack={:?}",
                                curr_ip, i, stack
                            )
                            .as_str(),
                        )
                        .clone();
                    stack.push(v);
                }
                &OpCode::SetLobalVar(local_idx) => {
                    let i = call_frames.last().map_or(0, |f| f.stack_base) + (local_idx as usize);
                    stack[i as usize] = stack.last().unwrap().clone();
                }
                &OpCode::LoadUpvalue(i) => {
                    let call_frame = call_frames.last().unwrap();
                    let upvalue = &stack[call_frame.stack_base - 1]
                        .as_closure()
                        .unwrap()
                        .upvalues[i as usize];
                    let v = match upvalue.borrow().deref() {
                        &Upvalue::Open(i) => stack[i].clone(),
                        Upvalue::Closed(v) => v.clone(),
                    };
                    stack.push(v);
                }
                &OpCode::SetUpvalue(i) => {
                    let value = stack.last().unwrap().clone();
                    let call_frame = call_frames.last().unwrap();
                    let closure = stack[call_frame.stack_base - 1]
                        .as_closure()
                        .unwrap()
                        .clone();
                    let upvalue = &closure.upvalues[i as usize];
                    let open = upvalue.borrow().as_open().copied();
                    match open {
                        Some(i) => {
                            stack[i] = value;
                        }
                        None => {
                            upvalue.as_ref().replace(Upvalue::Closed(value));
                        }
                    };
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
                                line: codes.get_line(curr_ip),
                            });
                        }
                    }
                    let b = stack.pop().unwrap();
                    let a = stack.pop().unwrap();
                    match a {
                        Value::String(str_a) => match b {
                            Value::String(str_b) => {
                                let mut c = String::from(str_a.as_ref());
                                c.push_str(str_b.as_ref());
                                stack.push(Value::String(c.into()));
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
                    let (a, b) = Self::try_pop2num(&mut stack, codes.get_line(curr_ip))?;
                    stack.push(Value::Number(a - b));
                }
                OpCode::Multiply => {
                    let (a, b) = Self::try_pop2num(&mut stack, codes.get_line(curr_ip))?;
                    stack.push(Value::Number(a * b));
                }
                OpCode::Divide => {
                    let (a, b) = Self::try_pop2num(&mut stack, codes.get_line(curr_ip))?;
                    stack.push(Value::Number(a / b));
                }
                OpCode::Negate => {
                    let v = stack.last_mut().unwrap();
                    match v {
                        Value::Number(n) => *n = -*n,
                        _ => {
                            return Err(InterpreteError {
                                message: ARITHMETIC_OPERAND_ERR_MSG.to_string(),
                                line: codes.get_line(curr_ip),
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
                    let (a, b) = Self::try_pop2num(&mut stack, codes.get_line(curr_ip))?;
                    stack.push(Value::Bool(a < b));
                }
                OpCode::Greater => {
                    let (a, b) = Self::try_pop2num(&mut stack, codes.get_line(curr_ip))?;
                    stack.push(Value::Bool(a > b));
                }
                OpCode::Not => {
                    let v = stack.pop().unwrap();
                    stack.push(Value::Bool(Self::is_falsey(&v)));
                }
                &OpCode::Pop => {
                    stack.pop().unwrap();
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
                &OpCode::MakeClosure(fun_idx) => {
                    let fun = &module.funs[fun_idx as usize];
                    let stack_base = call_frames.last().map_or(0, |f| f.stack_base);
                    let upvalues = fun
                        .upvalue_indexes
                        .iter()
                        .map(|&uv_idx| match uv_idx {
                            UpvalueIndex::Local(local_idx) => {
                                let stack_i = stack_base + (local_idx as usize);
                                let p = open_upvalues
                                    .iter()
                                    .position(|uv| uv.as_ref().borrow().get_open_index() >= stack_i)
                                    .unwrap_or(open_upvalues.len());
                                if p < open_upvalues.len()
                                    && open_upvalues[p].as_ref().borrow().get_open_index()
                                        == stack_i
                                {
                                    open_upvalues[p].clone()
                                } else {
                                    let capture = Rc::new(RefCell::new(Upvalue::Open(stack_i)));
                                    open_upvalues.insert(p, capture.clone());
                                    capture
                                }
                            }
                            UpvalueIndex::Upvalue(upvalue_idx) => {
                                let call_frame = call_frames.last().unwrap();
                                let closure =
                                    stack[call_frame.stack_base - 1].as_closure().unwrap();
                                closure.upvalues[upvalue_idx as usize].clone()
                            }
                        })
                        .collect();
                    stack.push(Value::Closure(Rc::new(Closure {
                        fun: fun.clone(),
                        upvalues,
                    })));
                }
                &OpCode::Call(args_count) => {
                    debug_assert!(stack.len() >= args_count as usize + 1);
                    let args_start = stack.len() - (args_count as usize);
                    let nv = match &stack[args_start - 1] {
                        Value::NativeFunc(_) => true,
                        Value::Closure(closure) => {
                            if args_count != closure.fun.arity {
                                return Err(InterpreteError {
                                    message: format!(
                                        "Expected {} arguments but got {}.",
                                        closure.fun.arity, args_count
                                    ),
                                    line: codes.get_line(curr_ip),
                                });
                            }
                            let next_codes = &closure.fun.codes;
                            call_frames.push(CallFrame {
                                stack_base: args_start,
                                return_ip: ip,
                                return_codes: codes,
                            });
                            ip = 0;
                            codes = next_codes;
                            false
                        }
                        _ => {
                            return Err(InterpreteError {
                                message: "Can only call functions and classes.".to_string(),
                                line: codes.get_line(curr_ip),
                            });
                        }
                    };
                    if nv {
                        let args = stack.drain(args_start..).collect();
                        let callee = stack.pop().unwrap();
                        if let Value::NativeFunc(callee) = callee {
                            stack.push((callee.fun)(args)?);
                        } else {
                            unreachable!("callee={:?}", callee);
                        }
                    }
                }
                OpCode::Return => {
                    let frame: CallFrame = if let Some(frame) = call_frames.pop() {
                        frame
                    } else {
                        return Ok(());
                    };
                    let return_value = stack.pop().unwrap();
                    stack
                        .drain(frame.stack_base..stack.len())
                        .enumerate()
                        .rev()
                        .for_each(|(local_idx, v)| {
                            let stack_i = frame.stack_base + local_idx;
                            if let Some(upvalue_ref) = open_upvalues.last() {
                                let open_idx = upvalue_ref.as_ref().borrow().get_open_index();
                                if open_idx == stack_i {
                                    open_upvalues
                                        .pop()
                                        .unwrap()
                                        .as_ref()
                                        .replace(Upvalue::Closed(v));
                                }
                            }
                        });
                    let c = stack.pop().unwrap();
                    assert!(c.is_closure(), "v={}", c);
                    stack.push(return_value);
                    ip = frame.return_ip;
                    codes = frame.return_codes;
                }
                OpCode::PopMaybeUpvalue => {
                    let v = stack.pop().unwrap();
                    let i = stack.len();
                    let is_open_upvalue = open_upvalues
                        .last()
                        .map(|v| {
                            let open_idx = v.as_ref().borrow().get_open_index();
                            assert!(open_idx <= i);
                            open_idx == i
                        })
                        .unwrap_or(false);
                    if is_open_upvalue {
                        let open_value = open_upvalues.pop().unwrap();
                        open_value.as_ref().replace(Upvalue::Closed(v));
                    }
                }
                OpCode::MakeClass(_) => todo!(),
            };
        }
    }
    fn try_pop2num(
        stack: &mut Vec<Value<Rc<str>>>,
        line: u32,
    ) -> Result<(f64, f64), InterpreteError> {
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
    fn is_falsey(value: &Value<Rc<str>>) -> bool {
        match value {
            Value::Nil => true,
            Value::Bool(b) => !b,
            _ => false,
        }
    }
}
