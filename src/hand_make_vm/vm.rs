use core::fmt::Debug;
use std::borrow::Borrow;
use std::collections::hash_map::Entry;
use std::collections::HashMap;

use std::ops::{AddAssign, Deref, SubAssign};
use std::{fmt::Display, rc::Rc};

use gc::{Finalize, Gc, GcCell, Trace};
use gpoint::GPoint;

use super::chunk::Codes;
use super::{error::InterpreteError, str_pool::StrPool};

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
    GetProp(u32),
    SetProp(u32),
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
    Jump(i16),
    JumpIfFalse(i16),
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

#[derive(Clone, Trace, Finalize)]
enum Value {
    Nil,
    Bool(bool),
    Number(f64),
    String(Rc<str>),
    NativeFunc(#[unsafe_ignore_trace] NativeFun<Self>),
    Closure(Gc<Closure>),
    Method(Gc<Method>),
    Class(Gc<Class>),
    Object(Gc<GcCell<Object>>),
}

fn gccell_ref_eq<T>(a: &Gc<GcCell<T>>, b: &Gc<GcCell<T>>) -> bool
where
    T: Trace,
{
    let a: *const T = a.deref().borrow().deref();
    let b: *const T = b.deref().borrow().deref();
    std::ptr::eq(a, b)
}

fn gc_ref_eq<T>(a: &Gc<T>, b: &Gc<T>) -> bool
where
    T: Trace,
{
    let a: &T = a.deref();
    let b: &T = b.deref();
    std::ptr::eq(a, b)
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Nil, Self::Nil) => true,
            (Self::Bool(l0), Self::Bool(r0)) => l0 == r0,
            (Self::Number(l0), Self::Number(r0)) => l0 == r0,
            (Self::String(l0), Self::String(r0)) => l0 == r0,
            (Self::NativeFunc(l0), Self::NativeFunc(r0)) => l0 == r0,
            (Self::Closure(l0), Self::Closure(r0)) => gc_ref_eq(l0, r0),
            (Self::Method(l0), Self::Method(r0)) => gc_ref_eq(l0, r0),
            (Self::Class(l0), Self::Class(r0)) => gc_ref_eq(l0, r0),
            (Self::Object(l0), Self::Object(r0)) => gccell_ref_eq(l0, r0),
            _ => false,
        }
    }
}

impl Value {
    fn as_closure(&self) -> Option<&Gc<Closure>> {
        if let Self::Closure(v) = self {
            Some(v)
        } else {
            None
        }
    }

    fn as_method(&self) -> Option<&Gc<Method>> {
        if let Self::Method(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Nil => write!(f, "nil"),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Number(n) => write!(f, "{}", GPoint(*n)),
            Value::String(s) => write!(f, "{}", s),
            Value::NativeFunc(nf) => write!(f, "<native fn>"),
            Value::Closure(c) => write!(f, "<fn {}>", c.proto.name),
            Value::Method(m) => write!(f, "<fn {}>", m.fun.name),
            Value::Class(c) => write!(f, "{}", c.proto.name),
            Value::Object(o) => {
                write!(f, "{} instance", o.deref().borrow().class.proto.name)
            }
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

#[derive(Debug, PartialEq)]
pub struct FunPrototype {
    pub name: Rc<str>,
    pub arity: u8,
    pub codes: Rc<Codes>,
    pub upvalue_indexes: Box<[UpvalueIndex]>,
}

#[derive(Trace, Finalize)]
struct Closure {
    #[unsafe_ignore_trace]
    proto: Rc<FunPrototype>,
    upvalues: Box<[Gc<GcCell<Upvalue>>]>,
}

#[derive(Debug, PartialEq)]
pub struct ClassPrototype {
    pub name: Rc<str>,
    pub has_super: bool,
    pub methods: Box<[Rc<FunPrototype>]>,
}

#[derive(Trace, Finalize)]
struct Class {
    super_class: Option<Gc<Class>>,
    #[unsafe_ignore_trace]
    proto: Rc<ClassPrototype>,
    method_tmpls: Box<[Gc<Closure>]>,
}

#[derive(Trace, Finalize)]
struct Object {
    class: Gc<Class>,
    methods: HashMap<u32, Vec<Gc<Method>>>,
    fields: HashMap<Rc<str>, Value>,
}

#[derive(Trace, Finalize)]
struct Method {
    #[unsafe_ignore_trace]
    fun: Rc<FunPrototype>,
    upvalues: Box<[Gc<GcCell<Upvalue>>]>,
    obj: Gc<GcCell<Object>>,
    cls_level: u8,
}

trait Callable {
    fn get_proto(&self) -> &FunPrototype;
    fn get_upvalue(&self, i: u8) -> &Gc<GcCell<Upvalue>>;
    fn ref_from_value(v: &Value) -> Option<&Self>;
}

impl Callable for Closure {
    fn get_proto(&self) -> &FunPrototype {
        &self.proto
    }
    fn get_upvalue(&self, i: u8) -> &Gc<GcCell<Upvalue>> {
        &self.upvalues[i as usize]
    }
    fn ref_from_value(v: &Value) -> Option<&Self> {
        v.as_closure().map(|c| c.borrow())
    }
}
impl Callable for Method {
    fn get_proto(&self) -> &FunPrototype {
        &self.fun
    }
    fn get_upvalue(&self, i: u8) -> &Gc<GcCell<Upvalue>> {
        &self.upvalues[i as usize]
    }
    fn ref_from_value(v: &Value) -> Option<&Self> {
        v.as_method().map(|m| m.borrow())
    }
}

fn native_fun_clock(_args: Vec<Value>) -> Result<Value, InterpreteError> {
    Ok(Value::Number(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs_f64(),
    ))
}

pub struct Module {
    pub main: Codes,
    pub funs: Box<[Rc<FunPrototype>]>,
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
        for (i, cls) in self.classes.iter().enumerate() {
            writeln!(
                f,
                "class(name={}, id={}, has_super={})",
                cls.name, i, cls.has_super
            )?;
            for method in cls.methods.iter() {
                writeln!(f, "method(name={})", method.name)?;
                writeln!(f, "{}", method.codes)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
struct CallFrame {
    stack_base: usize,
    return_ip: usize,
    return_codes: Rc<Codes>,
}

#[derive(Clone, Trace, Finalize)]
enum Upvalue {
    Open(usize),
    Closed(Value),
}

impl Upvalue {
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

struct ExecuteState {
    codes: Rc<Codes>,
    ip: usize,
}

impl ExecuteState {
    fn next(&mut self) -> &OpCode {
        let op_code = &self.codes.codes[self.ip];
        self.ip += 1;
        return op_code;
    }
    fn err(&self, message: String) -> InterpreteError {
        InterpreteError {
            message,
            line: self.codes.get_line(self.ip - 1),
        }
    }
    fn set_fun_codes(&mut self, codes: Rc<Codes>, ip: usize) -> (Rc<Codes>, usize) {
        let curr_ip = self.ip;
        let curr_codes = std::mem::replace(&mut self.codes, codes);
        self.ip = ip;
        (curr_codes, curr_ip)
    }

    fn move_ip(&mut self, offset: i16) -> () {
        if offset < 0 {
            let rhs = offset.unsigned_abs() as usize + 1;
            debug_assert!(self.ip >= rhs);
            self.ip.sub_assign(rhs);
        } else if offset > 0 {
            self.ip.add_assign((offset - 1) as usize);
        }
    }
}

impl<'p> VM<'p> {
    pub fn new(str_pool: &'p StrPool) -> Self {
        VM { str_pool }
    }

    pub fn run(&mut self, module: Module) -> Result<(), InterpreteError> {
        let mut global_variables = HashMap::new();
        global_variables.insert(
            self.str_pool.register("clock"),
            Value::NativeFunc(NativeFun {
                name: "clock",
                fun: native_fun_clock,
            }),
        );
        let mut stack = vec![];
        let mut open_upvalues: Vec<Gc<GcCell<Upvalue>>> = vec![];
        let mut call_frames: Vec<CallFrame> = vec![];
        let mut execute_state = ExecuteState {
            codes: module.main.into(),
            ip: 0,
        };
        loop {
            let op_code = execute_state.next();
            match op_code {
                &OpCode::LoadNumber(n) => stack.push(Value::Number(n)),
                &OpCode::LoadConstStr(i) => {
                    stack.push(Value::String(self.str_pool.get(i.into())));
                }
                &OpCode::LoadConstStrLong(i) => {
                    stack.push(Value::String(self.str_pool.get(i).clone()));
                }
                &OpCode::DefGlobalVar(name_id) => {
                    global_variables.insert(name_id, stack.pop().unwrap());
                }
                &OpCode::LoadGlobalVar(name_id) => {
                    let v = global_variables.get(&name_id).ok_or_else(|| {
                        execute_state.err(format!(
                            "Undefined variable '{}'.",
                            self.str_pool.get(name_id)
                        ))
                    })?;
                    stack.push(v.clone());
                }
                &OpCode::SetGlobalVar(name_id) => {
                    let v = global_variables.get_mut(&name_id).ok_or_else(|| {
                        execute_state.err(format!(
                            "Undefined variable '{}'.",
                            self.str_pool.get(name_id)
                        ))
                    })?;
                    *v = stack.last().unwrap().clone();
                }
                &OpCode::LoadLocalVar(local_idx) => {
                    let i = call_frames.last().map_or(0, |f| f.stack_base) + (local_idx as usize);
                    debug_assert!(i < stack.len());
                    let v = stack.get(i).unwrap().clone();
                    stack.push(v);
                }
                &OpCode::SetLobalVar(local_idx) => {
                    let i = call_frames.last().map_or(0, |f| f.stack_base) + (local_idx as usize);
                    stack[i as usize] = stack.last().unwrap().clone();
                }
                &OpCode::LoadUpvalue(i) => {
                    let call_frame = call_frames.last().unwrap();
                    let upvalue: &Gc<GcCell<Upvalue>> = &stack[call_frame.stack_base - 1]
                        .as_closure()
                        .unwrap()
                        .upvalues[i as usize];
                    let v = match upvalue.deref().borrow().deref() {
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
                    let upvalue: &GcCell<Upvalue> = &(closure.upvalues[i as usize]);
                    let open = upvalue.borrow().as_open().copied();
                    match open {
                        Some(i) => {
                            stack[i] = value;
                        }
                        None => {
                            *upvalue.borrow_mut() = Upvalue::Closed(value);
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
                            return Err(execute_state.err(ADD_OPERANDS_ERR_MSG.to_string()));
                        }
                    }
                    let b = stack.pop().unwrap();
                    let a = stack.pop().unwrap();
                    match &a {
                        Value::String(str_a) => match &b {
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
                    let (a, b) = Self::try_pop2num(&mut stack)
                        .map_err(|e| execute_state.err(e.to_string()))?;
                    stack.push(Value::Number(a - b));
                }
                OpCode::Multiply => {
                    let (a, b) = Self::try_pop2num(&mut stack)
                        .map_err(|e| execute_state.err(e.to_string()))?;
                    stack.push(Value::Number(a * b));
                }
                OpCode::Divide => {
                    let (a, b) = Self::try_pop2num(&mut stack)
                        .map_err(|e| execute_state.err(e.to_string()))?;
                    stack.push(Value::Number(a / b));
                }
                OpCode::Negate => {
                    let v = stack.last_mut().unwrap();
                    match v {
                        Value::Number(n) => *n = -*n,
                        _ => return Err(execute_state.err(ARITHMETIC_OPERAND_ERR_MSG.to_string())),
                    }
                }
                OpCode::Print => {
                    println!("{}", stack.pop().unwrap());
                }
                OpCode::LoadNil => stack.push(Value::Nil),
                OpCode::LoadTrue => stack.push(Value::Bool(true)),
                OpCode::LoadFalse => stack.push(Value::Bool(false)),
                OpCode::Equal => {
                    let b = stack.pop().unwrap();
                    let a = stack.pop().unwrap();
                    stack.push(Value::Bool(a == b));
                }
                OpCode::Less => {
                    let (a, b) = Self::try_pop2num(&mut stack)
                        .map_err(|e| execute_state.err(e.to_string()))?;
                    stack.push(Value::Bool(a < b));
                }
                OpCode::Greater => {
                    let (a, b) = Self::try_pop2num(&mut stack)
                        .map_err(|e| execute_state.err(e.to_string()))?;
                    stack.push(Value::Bool(a > b));
                }
                OpCode::Not => {
                    let v = stack.pop().unwrap();
                    stack.push(Value::Bool(Self::is_falsey(&v)));
                }
                &OpCode::Pop => {
                    stack.pop().unwrap();
                }
                &OpCode::Jump(offset) => {
                    execute_state.move_ip(offset);
                    continue;
                }
                &OpCode::JumpIfFalse(offset) => {
                    if Self::is_falsey(&stack.last().unwrap()) {
                        execute_state.move_ip(offset);
                        continue;
                    }
                }
                &OpCode::MakeClosure(fun_idx) => {
                    let fun = &module.funs[fun_idx as usize];
                    let stack_base = call_frames.last().map_or(0, |f| f.stack_base);
                    let upvalues = make_upvalues::<_, Closure>(
                        &stack,
                        &mut open_upvalues,
                        stack_base,
                        fun.upvalue_indexes.iter(),
                    );
                    stack.push(Value::Closure(Gc::new(Closure {
                        proto: fun.clone(),
                        upvalues,
                    })));
                }
                &OpCode::MakeClass(id) => {
                    let cls_proto = &module.classes[id as usize];
                    let super_class = if cls_proto.has_super {
                        match &stack.pop().unwrap() {
                            Value::Class(c) => Some(c.clone()),
                            _ => {
                                return Err(
                                    execute_state.err("Superclass must be a class.".to_string())
                                );
                            }
                        }
                    } else {
                        None
                    };
                    let stack_base = call_frames.last().map_or(0, |f| f.stack_base);
                    let method_tmpls = cls_proto
                        .methods
                        .iter()
                        .map(|proto| {
                            let upvalues = make_upvalues::<_, Method>(
                                &stack,
                                &mut open_upvalues,
                                stack_base,
                                proto.upvalue_indexes.iter(),
                            );
                            Gc::new(Closure {
                                proto: proto.clone(),
                                upvalues,
                            })
                        })
                        .collect();
                    stack.push(Value::Class(Gc::new(Class {
                        super_class,
                        proto: cls_proto.clone(),
                        method_tmpls,
                    })));
                }
                &OpCode::Call(args_count) => {
                    debug_assert!(stack.len() >= args_count as usize + 1);
                    if call_frames.len() >= 64 {
                        return Err(execute_state.err("Stack overflow.".to_string()));
                    }
                    let args_start = stack.len() - (args_count as usize);
                    match &stack[args_start - 1].clone() {
                        Value::Closure(closure) => {
                            check_arity(args_count, closure.proto.arity)
                                .map_err(|e| execute_state.err(e))?;
                            let (return_codes, return_ip) =
                                execute_state.set_fun_codes(closure.proto.codes.clone(), 0);
                            call_frames.push(CallFrame {
                                stack_base: args_start,
                                return_ip,
                                return_codes,
                            });
                        }
                        Value::Method(method) => {
                            check_arity(args_count, method.fun.arity)
                                .map_err(|e| execute_state.err(e))?;
                            stack.insert(args_start, Value::Object(method.obj.clone()));
                            let (return_codes, return_ip) =
                                execute_state.set_fun_codes(method.fun.codes.clone(), 0);
                            call_frames.push(CallFrame {
                                stack_base: args_start,
                                return_ip,
                                return_codes,
                            });
                        }
                        Value::Class(cls) => {
                            let obj = Gc::new(GcCell::new(Object {
                                class: cls.clone(),
                                fields: HashMap::new(),
                                methods: HashMap::new(),
                            }));
                            self.fill_methods(&obj, cls.clone(), 0);
                            let init_method: Option<Gc<Method>> = obj
                                .deref()
                                .borrow()
                                .methods
                                .get(&self.str_pool.register("init"))
                                .and_then(|ms: &Vec<Gc<Method>>| -> Option<Gc<Method>> {
                                    ms.get(0).map(|m| m.clone())
                                });

                            check_arity(
                                args_count,
                                init_method.as_deref().map_or(0, |m| m.fun.arity),
                            )
                            .map_err(|e| execute_state.err(e))?;
                            if let Some(_) = init_method {
                                todo!("init");
                                // let (return_codes, return_ip) =
                                //     execute_state.set_fun_codes(method.fun.codes.clone(), 0);
                                // call_frames.push(CallFrame {
                                //     stack_base: args_start,
                                //     return_ip,
                                //     return_codes,
                                // });
                            } else {
                                stack.push(Value::Object(obj.clone()));
                            }
                        }
                        Value::NativeFunc(callee) => {
                            let args = stack.drain(args_start..).collect();
                            stack.pop().unwrap();
                            stack.push((callee.fun)(args)?);
                        }
                        _ => {
                            return Err(execute_state
                                .err("Can only call functions and classes.".to_string()));
                        }
                    };
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
                                let open_idx = upvalue_ref.deref().borrow().get_open_index();
                                if open_idx == stack_i {
                                    *open_upvalues.pop().unwrap().borrow_mut() = Upvalue::Closed(v);
                                }
                            }
                        });
                    let c = stack.pop().unwrap();
                    assert!(matches!(c, Value::Closure(_) | Value::Method(_)), "v={}", c);
                    stack.push(return_value);
                    execute_state.set_fun_codes(frame.return_codes, frame.return_ip);
                }
                OpCode::PopMaybeUpvalue => {
                    let v = stack.pop().unwrap();
                    let pop_i = stack.len();
                    let is_open_upvalue = open_upvalues
                        .last()
                        .map(|v| {
                            let open_idx = v.deref().borrow().get_open_index();
                            assert!(open_idx <= pop_i);
                            open_idx == pop_i
                        })
                        .unwrap_or(false);
                    if is_open_upvalue {
                        let upvalue = open_upvalues.pop().unwrap();
                        *upvalue.borrow_mut() = Upvalue::Closed(v);
                    }
                }
                &OpCode::GetProp(str_id) => {
                    // dump_stack(&stack);
                    let prop = self.str_pool.get(str_id);
                    let obj = stack.pop().unwrap();
                    let value = (match &obj {
                        Value::Object(obj) => Ok(obj.clone()),
                        _ => Err(execute_state.err("Only instances have properties.".to_string())),
                    })
                    .and_then(|obj: Gc<GcCell<Object>>| {
                        if let Some(v) = obj.deref().borrow().fields.get(&prop) {
                            Ok(v.clone())
                        } else if let Some(method) = obj
                            .deref()
                            .borrow()
                            .methods
                            .get(&str_id)
                            .and_then(|ms| ms.get(0))
                        {
                            Ok(Value::Method(method.clone()))
                        } else {
                            Err(execute_state.err(format!("Undefined property '{}'.", prop)))
                        }
                    })?;
                    stack.push(value);
                }
                &OpCode::SetProp(str_id) => {
                    let prop = self.str_pool.get(str_id);
                    let value = stack.pop().unwrap();
                    let obj = stack.pop().unwrap();
                    let obj: Gc<GcCell<Object>> = match &obj {
                        Value::Object(obj) => obj.clone(),
                        _ => {
                            return Err(execute_state.err("Only instances have fields.".to_string()))
                        }
                    };
                    match obj.deref().borrow_mut().fields.entry(prop) {
                        Entry::Occupied(mut o) => {
                            *o.get_mut() = value.clone();
                        }
                        Entry::Vacant(v) => {
                            v.insert(value.clone());
                        }
                    };
                    stack.push(value);
                }
            };
        }
    }
    fn try_pop2num(stack: &mut Vec<Value>) -> Result<(f64, f64), &'static str> {
        let len = stack.len();
        let bi = len - 1;
        let ai = bi - 1;
        let b = match stack[bi] {
            Value::Number(n) => n,
            _ => return Err(ARITHMETIC_OPERANDS_ERR_MSG),
        };
        let a = match stack[ai] {
            Value::Number(n) => n,
            _ => return Err(ARITHMETIC_OPERANDS_ERR_MSG),
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

    fn fill_methods(&self, o: &'_ Gc<GcCell<Object>>, cls: Gc<Class>, cls_level: u8) {
        for t in cls.method_tmpls.iter() {
            let m = Method {
                fun: t.proto.clone(),
                upvalues: t.upvalues.clone(),
                cls_level: 0,
                obj: o.clone(),
            };
            match o
                .borrow_mut()
                .methods
                .entry(self.str_pool.register(&t.proto.name))
            {
                Entry::Occupied(mut o) => {
                    o.get_mut().push(m.into());
                }
                Entry::Vacant(v) => {
                    v.insert(vec![m.into()]);
                }
            }
        }
        if let Some(super_cls) = &cls.super_class {
            self.fill_methods(&o, super_cls.clone(), cls_level + 1);
        }
    }
}

fn make_upvalues<'a, I, C>(
    stack: &Vec<Value>,
    open_upvalues: &mut Vec<Gc<GcCell<Upvalue>>>,
    stack_base: usize,
    upvalue_indexes: I,
) -> Box<[Gc<GcCell<Upvalue>>]>
where
    I: Iterator<Item = &'a UpvalueIndex>,
    C: Callable,
{
    upvalue_indexes
        .map(|&uv_idx| match uv_idx {
            UpvalueIndex::Local(local_idx) => {
                capture_caller_local(stack_base, local_idx, open_upvalues)
            }
            UpvalueIndex::Upvalue(upvalue_idx) => C::ref_from_value(&stack[stack_base - 1])
                .unwrap()
                .get_upvalue(upvalue_idx)
                .clone(),
        })
        .collect()
}

fn capture_caller_local(
    stack_base: usize,
    local_idx: u8,
    open_upvalues: &mut Vec<Gc<GcCell<Upvalue>>>,
) -> Gc<GcCell<Upvalue>> {
    let stack_i = stack_base + (local_idx as usize);
    let p = open_upvalues
        .iter()
        .position(|uv| uv.deref().borrow().get_open_index() >= stack_i)
        .unwrap_or(open_upvalues.len());
    if p < open_upvalues.len() && open_upvalues[p].deref().borrow().get_open_index() == stack_i {
        open_upvalues[p].clone()
    } else {
        let capture = Gc::new(GcCell::new(Upvalue::Open(stack_i)));
        open_upvalues.insert(p, capture.clone());
        capture
    }
}

fn check_arity(args_count: u8, arity: u8) -> Result<(), String> {
    if args_count != arity {
        Err(format!(
            "Expected {} arguments but got {}.",
            arity, args_count
        ))
    } else {
        Ok(())
    }
}

fn dump_stack(stack: &Vec<Value>) {
    println!("Stack:");
    for (i, v) in stack.iter().enumerate() {
        println!("{}: {}", i, v);
    }
}
