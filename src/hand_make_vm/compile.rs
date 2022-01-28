use std::{cell::RefCell, convert::TryInto, rc::Rc};

use crate::ast::{
    expression::{Expression, LiteralValue},
    statement::{BlockStmt, DeclOrStmt, Program, Statement, VarDecl},
    token::TokenType,
};

use super::{
    error::InterpreteError,
    vm::{Chunk, ClassPrototype, FunPrototype, JumpIfParam, Module, OpCode, UpvalueIndex},
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

    pub fn register(&self, name: &str) -> u32 {
        let pos_res = self
            .pool
            .borrow()
            .iter()
            .position(|n| (*n).as_ref() == name);
        if let Some(i) = pos_res {
            i
        } else {
            let mut p = self.pool.borrow_mut();
            p.push(name.to_string().into_boxed_str().into());
            p.len() - 1
        }
        .try_into()
        .unwrap()
    }
    pub fn get(&self, i: u32) -> Rc<str> {
        self.pool.borrow()[i as usize].clone()
    }
}

pub fn compile(program: &'_ Program, str_pool: &'_ StrPool) -> Result<Module, InterpreteError> {
    let mut funs = Vec::new();
    let mut classes = Vec::new();
    let mut scopes = vec![];
    let mut c = ScopeCompiler::new(str_pool, &mut scopes, &mut funs, &mut classes);
    for stmt in program.statements.iter() {
        c.compile_decl_or_stmt(&stmt)?;
    }
    c.chunk.add_code(OpCode::Return, program.eof_line);
    Ok(Module {
        main: c.chunk.build(),
        funs: funs.into_iter().map(|f| f.into()).collect(),
        classes: classes.into_iter().map(|c| c.into()).collect(),
    })
}

#[derive(Debug)]
struct Scope<'s> {
    vars: Vec<(&'s str, bool)>,
    var_count_per_block: Vec<u8>,
    upvalue_indexes: Vec<UpvalueIndex>,
}

impl<'s> Scope<'s> {
    fn register_upvalue(&mut self, idx: UpvalueIndex) -> u8 {
        if let Some(i) = self.upvalue_indexes.iter().position(|&x| x == idx) {
            i.try_into().unwrap()
        } else {
            let i = self
                .upvalue_indexes
                .len()
                .try_into()
                .expect("too many upvalues");
            self.upvalue_indexes.push(idx);
            i
        }
    }
    fn new() -> Self {
        Self {
            vars: Vec::new(),
            var_count_per_block: Vec::new(),
            upvalue_indexes: Vec::new(),
        }
    }
    fn is_in_global_scope(&self) -> bool {
        self.var_count_per_block.is_empty()
    }
    fn new_block(&mut self) {
        self.var_count_per_block.push(0);
    }
    fn end_block(&mut self) -> Box<[bool]> {
        let cnt = self.var_count_per_block.pop().unwrap();
        self.vars
            .drain((self.vars.len() - (cnt as usize))..)
            .map(|(_, captured)| captured)
            .collect()
    }
    fn new_var(&mut self, name: &'s str) -> Result<(), &'static str> {
        if self.vars.len() >= u8::MAX as usize {
            return Err("too many variables");
        }
        self.vars.push((name, false));
        let cnt = self.var_count_per_block.last_mut().unwrap();
        *cnt += 1;
        Ok(())
    }
    fn position(&self, name: &'_ str) -> Option<u8> {
        self.vars
            .iter()
            .rev()
            .position(|&(v_name, _)| v_name == name)
            .map(|i| (self.vars.len() - i - 1) as u8)
    }
    fn try_capture(&mut self, name: &'_ str) -> Option<u8> {
        self.position(name).inspect(|&i| {
            self.vars[i as usize].1 = true;
        })
    }
}

struct ScopeCompiler<'p, 's, 'o> {
    str_pool: &'p StrPool,
    scopes: &'o mut Vec<Scope<'s>>,
    funs: &'o mut Vec<FunPrototype>,
    classes: &'o mut Vec<ClassPrototype>,
    chunk: Chunk<'p>,
}

impl<'p, 's, 'o> ScopeCompiler<'p, 's, 'o> {
    fn new(
        str_pool: &'p StrPool,
        scopes: &'o mut Vec<Scope<'s>>,
        funs: &'o mut Vec<FunPrototype>,
        classes: &'o mut Vec<ClassPrototype>,
    ) -> Self {
        scopes.push(Scope::new());
        Self {
            str_pool,
            scopes,
            funs,
            classes,
            chunk: Chunk::new(str_pool),
        }
    }
    fn compile_decl_or_stmt(&'_ mut self, ds: &'_ DeclOrStmt<'s>) -> Result<(), InterpreteError> {
        match ds {
            DeclOrStmt::FunDecl(d) => {
                let in_global_scope = self.scopes.last().unwrap().is_in_global_scope();
                // early bind
                if !in_global_scope {
                    self.scopes
                        .last_mut()
                        .unwrap()
                        .new_var(d.name)
                        .map_err(|e| InterpreteError {
                            message: e.to_string(),
                            line: d.name_line,
                        })?
                }
                let codes = {
                    let mut c = ScopeCompiler::new(
                        self.str_pool,
                        &mut self.scopes,
                        self.funs,
                        self.classes,
                    );
                    c.scopes.last_mut().unwrap().new_block();
                    for &(name, line) in d.params.iter() {
                        let cross_fun_scope = c.scopes.last_mut().unwrap();
                        if cross_fun_scope.is_in_global_scope() {
                            c.chunk
                                .add_code(OpCode::DefGlobalVar(c.str_pool.register(name)), line);
                        } else {
                            cross_fun_scope.new_var(name).map_err(|e| InterpreteError {
                                message: e.to_string(),
                                line,
                            })?
                        }
                    }
                    c.compile_block(&d.body)?;
                    c.chunk.add_code(OpCode::LoadNil, d.body.right_brace_line);
                    c.chunk.add_code(OpCode::Return, d.body.right_brace_line);
                    c.chunk.build()
                };

                let fun = FunPrototype {
                    name: d.name.into(),
                    arity: d.params.len().try_into().unwrap(),
                    codes,
                    upvalue_indexes: self
                        .scopes
                        .pop()
                        .unwrap()
                        .upvalue_indexes
                        .into_boxed_slice(),
                };

                let fun_id = self.funs.len().try_into().unwrap();
                self.funs.push(fun);
                self.chunk.add_code(OpCode::MakeClosure(fun_id), d.fun_line);
                if in_global_scope {
                    self.chunk.add_code(
                        OpCode::DefGlobalVar(self.str_pool.register(d.name)),
                        d.name_line,
                    );
                }
            }
            DeclOrStmt::VarDecl(d) => {
                self.compile_var_decl(d)?;
            }
            DeclOrStmt::Stmt(ref stmt) => {
                self.compile_stmt(stmt)?;
            }
            DeclOrStmt::ClassDecl(cls) => {
                // let id = self.classes.len().try_into().unwrap();
                self.classes.push(ClassPrototype {
                    name: cls.name.into(),
                    has_super_class: cls.super_class.is_some(),
                    methods: todo!(),
                });
            }
        };
        Ok(())
    }

    fn compile_var_decl(&mut self, v: &VarDecl<'s>) -> Result<(), InterpreteError> {
        if let Some(init_expr) = &v.init_expr {
            self.compile_expression(init_expr)?;
        } else {
            self.chunk.add_code(OpCode::LoadNil, v.name.line);
        }
        {
            let name = v.name.lexeme;
            let line = v.name.line;
            let cross_fun_scope = self.scopes.last_mut().unwrap();
            if cross_fun_scope.is_in_global_scope() {
                self.chunk
                    .add_code(OpCode::DefGlobalVar(self.str_pool.register(name)), line);
                Ok(())
            } else {
                cross_fun_scope.new_var(name).map_err(|e| InterpreteError {
                    message: e.to_string(),
                    line,
                })
            }
        }
    }

    fn compile_stmt(&mut self, stmt: &Statement<'s>) -> Result<(), InterpreteError> {
        match stmt {
            Statement::Expr(expr) => {
                self.compile_expression(&expr.expr)?;
                self.chunk.add_code(OpCode::Pop, expr.semicolon_line);
            }
            Statement::Print(s) => {
                self.compile_expression(&s.expr)?;
                self.chunk.add_code(OpCode::Print, s.print_line);
            }
            Statement::Block(b) => {
                self.compile_block(b)?;
            }
            Statement::If(stmt) => {
                let line = stmt.if_line;
                self.compile_expression(&stmt.cond)?;
                let jif = JumpIfFalsePlaceholder::new(&mut self.chunk, true, line);
                self.compile_stmt(&stmt.then_branch)?;
                if let Some((else_line, box ref else_branch)) = stmt.else_branch {
                    let jmp = JumpPlaceholder::new(&mut self.chunk, else_line);
                    let else_i = self.chunk.get_next_index();
                    jif.set_target(&mut self.chunk, else_i);
                    self.compile_stmt(&else_branch)?;
                    let res_i = self.chunk.get_next_index();
                    jmp.set_target(&mut self.chunk, res_i);
                } else {
                    let res_i = self.chunk.get_next_index();
                    jif.set_target(&mut self.chunk, res_i);
                }
            }
            Statement::While(stmt) => {
                let start_i = self.chunk.get_next_index();
                self.compile_expression(&stmt.cond)?;
                let jif = JumpIfFalsePlaceholder::new(&mut self.chunk, true, stmt.while_line);
                self.compile_stmt(&stmt.body)?;
                let jmp = JumpPlaceholder::new(&mut self.chunk, stmt.while_line);
                jmp.set_target(&mut self.chunk, start_i);
                let res_i = self.chunk.get_next_index();
                jif.set_target(&mut self.chunk, res_i);
            }
            Statement::For(stmt) => {
                self.scopes.last_mut().unwrap().new_block();
                if let Some(box ref init) = stmt.init {
                    match init {
                        DeclOrStmt::VarDecl(l) => {
                            self.compile_var_decl(l)?;
                        }
                        DeclOrStmt::Stmt(Statement::Expr(l)) => {
                            self.compile_expression(&l.expr)?;
                        }
                        _ => panic!("for init is not decl or expr, but {:?}", init),
                    }
                }
                let line = stmt.for_line;
                let start_i = self.chunk.get_next_index();
                let jif = if let Some(box ref cond) = stmt.cond {
                    self.compile_expression(cond)?;
                    Some(JumpIfFalsePlaceholder::new(&mut self.chunk, true, line))
                } else {
                    None
                };
                self.compile_stmt(&stmt.body)?;
                if let Some(post) = &stmt.post {
                    self.compile_expression(post)?;
                    self.chunk.add_code(OpCode::Pop, line);
                }
                JumpPlaceholder::new(&mut self.chunk, line).set_target(&mut self.chunk, start_i);
                if let Some(jif) = jif {
                    let res_i = self.chunk.get_next_index();
                    jif.set_target(&mut self.chunk, res_i);
                }
                let vars = self.scopes.last_mut().unwrap().end_block();
                assert!(vars.len() <= 1);
                for &captured in vars.iter() {
                    self.chunk.add_code(
                        if captured {
                            OpCode::PopMaybeUpvalue
                        } else {
                            OpCode::Pop
                        },
                        line,
                    );
                }
            }
            Statement::Return(r) => {
                if let Some(value) = &r.value {
                    self.compile_expression(value)?;
                    self.chunk.add_code(OpCode::Return, r.return_line);
                } else {
                    self.chunk.add_code(OpCode::LoadNil, r.return_line);
                    self.chunk.add_code(OpCode::Return, r.return_line);
                }
            }
        };
        Ok(())
    }

    fn compile_block(&mut self, block: &BlockStmt<'s>) -> Result<(), InterpreteError> {
        self.scopes.last_mut().unwrap().new_block();
        for stmt in block.stmts.iter() {
            self.compile_decl_or_stmt(&stmt)?;
        }
        let vars = self.scopes.last_mut().unwrap().end_block();
        for &captured in vars.iter().rev() {
            self.chunk.add_code(
                if captured {
                    OpCode::PopMaybeUpvalue
                } else {
                    OpCode::Pop
                },
                block.right_brace_line,
            );
        }
        Ok(())
    }
    fn compile_expression(&'_ mut self, expr: &'_ Expression<'s>) -> Result<(), InterpreteError> {
        match &expr {
            Expression::Literal(l) => {
                let line = l.line;
                match &l.value {
                    LiteralValue::Number(n) => {
                        self.chunk.add_code(OpCode::LoadNumber(*n), line);
                    }
                    LiteralValue::String(s) => {
                        self.chunk.add_const_str(&s, line);
                    }
                    LiteralValue::True => {
                        self.chunk.add_code(OpCode::LoadTrue, line);
                    }
                    LiteralValue::False => {
                        self.chunk.add_code(OpCode::LoadFalse, line);
                    }
                    LiteralValue::Nil => {
                        self.chunk.add_code(OpCode::LoadNil, line);
                    }
                };
            }
            Expression::Unary(u) => {
                let op_code = match u.op {
                    TokenType::Minus => (OpCode::Negate),
                    TokenType::Bang => (OpCode::Not),
                    _ => unreachable!(),
                };
                self.compile_expression(&u.right)?;
                self.chunk.add_code(op_code, u.op_line);
            }
            Expression::Binary(b) => {
                self.compile_expression(&b.left)?;
                let line = b.op_line;
                match b.op {
                    TokenType::And => {
                        let jif = JumpIfFalsePlaceholder::new(&mut self.chunk, false, line);
                        self.compile_expression(&b.right)?;
                        let jres = JumpPlaceholder::new(&mut self.chunk, line);
                        let res_i = self.chunk.get_next_index();
                        jif.set_target(&mut self.chunk, res_i);
                        jres.set_target(&mut self.chunk, res_i);
                    }
                    TokenType::Or => {
                        let jif = JumpIfFalsePlaceholder::new(&mut self.chunk, false, line);
                        let jres = JumpPlaceholder::new(&mut self.chunk, line);
                        let rhs_i = self.chunk.get_next_index();
                        jif.set_target(&mut self.chunk, rhs_i);
                        self.compile_expression(&b.right)?;
                        let res_i = self.chunk.get_next_index();
                        jres.set_target(&mut self.chunk, res_i);
                    }
                    TokenType::EqualEqual => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Equal, line);
                    }
                    TokenType::BangEqual => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Equal, line);
                        self.chunk.add_code(OpCode::Not, line);
                    }
                    TokenType::Less => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Less, line);
                    }
                    TokenType::LessEqual => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Greater, line);
                        self.chunk.add_code(OpCode::Not, line);
                    }
                    TokenType::Greater => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Greater, line);
                    }
                    TokenType::GreaterEqual => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Less, line);
                        self.chunk.add_code(OpCode::Not, line);
                    }
                    TokenType::Plus => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Add, line);
                    }
                    TokenType::Minus => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Subtract, line);
                    }
                    TokenType::Star => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Multiply, line);
                    }
                    TokenType::Slash => {
                        self.compile_expression(&b.right)?;
                        self.chunk.add_code(OpCode::Divide, line);
                    }
                    _ => unreachable!(),
                };
            }
            Expression::Grouping(g) => self.compile_expression(&g)?,
            &Expression::Variable(v) => {
                if let Some(idx) = self.scopes.last_mut().unwrap().position(v.name) {
                    self.chunk.add_code(OpCode::LoadLocalVar(idx), v.line);
                } else if let Some(idx) =
                    resolve_upvalue(self.scopes, self.scopes.len() - 1, v.name)
                {
                    self.chunk.add_code(OpCode::LoadUpvalue(idx), v.line);
                } else {
                    self.chunk.add_code(
                        OpCode::LoadGlobalVar(self.str_pool.register(v.name)),
                        v.line,
                    );
                }
            }
            Expression::Assignment(a) => {
                self.compile_expression(&a.expr)?;
                match &a.lvalue {
                    crate::ast::expression::LValue::Variable(v) => {
                        let var_name = v.name;
                        if let Some(idx) = self.scopes.last().unwrap().position(var_name) {
                            self.chunk.add_code(OpCode::SetLobalVar(idx), a.op_line);
                        } else if let Some(idx) =
                            resolve_upvalue(self.scopes, self.scopes.len() - 1, var_name)
                        {
                            self.chunk.add_code(OpCode::SetUpvalue(idx), a.op_line);
                        } else {
                            self.chunk.add_code(
                                OpCode::SetGlobalVar(self.str_pool.register(var_name)),
                                a.op_line,
                            );
                        }
                    }
                    crate::ast::expression::LValue::Get(_) => todo!(),
                }
            }
            Expression::Call(c) => {
                self.compile_expression(&c.callee)?;
                for ele in c.args.iter() {
                    self.compile_expression(ele)?;
                }
                self.chunk.add_code(
                    OpCode::Call(c.args.len().try_into().unwrap()),
                    c.left_paren_line,
                );
            }
            Expression::Super(_) => todo!(),
            Expression::This(_) => todo!(),
            Expression::Get(_) => todo!(),
        }
        Ok(())
    }

    fn curr_scope(&self) -> &Scope<'s> {
        self.scopes.last().unwrap()
    }
    fn curr_scope_mut(&mut self) -> &mut Scope<'s> {
        self.scopes.last_mut().unwrap()
    }
}

fn resolve_upvalue<'s>(scopes: &'_ mut Vec<Scope<'s>>, curr: usize, name: &'s str) -> Option<u8> {
    if curr > 0 {
        let outer = curr - 1;
        if let Some(idx) = scopes[outer].try_capture(name) {
            Some(UpvalueIndex::Local(idx))
        } else if let Some(idx) = resolve_upvalue(scopes, outer, name) {
            Some(UpvalueIndex::Upvalue(idx))
        } else {
            None
        }
    } else {
        None
    }
    .map(|v| scopes[curr].register_upvalue(v))
}

#[cfg(test)]
mod test {

    use crate::ast::parse_source;

    use super::*;
    #[test]
    fn test_compile_program() {
        let program = parse_source("print 1;".as_bytes()).unwrap();
        let str_pool = StrPool::new();
        println!("{}", compile(&program, &str_pool).unwrap());
    }

    #[test]
    fn test_str_pool() {
        let str_pool = StrPool::new();
        let s1 = str_pool.register("hello");
        let s2 = str_pool.register("hello");
        assert_eq!(s1, s2);
    }
}

struct JumpPlaceholder {
    jump_i: u16,
}

impl JumpPlaceholder {
    fn new(chunk: &mut Chunk, src_line: u32) -> Self {
        let jump_i = chunk.get_next_index();
        chunk.add_code(OpCode::Jump(u16::MAX), src_line);
        Self { jump_i }
    }
    fn set_target(&self, chunk: &mut Chunk, target_i: u16) {
        chunk.set(self.jump_i, OpCode::Jump(target_i));
    }
}

struct JumpIfFalsePlaceholder {
    jump_i: u16,
    pop_value: bool,
}

impl JumpIfFalsePlaceholder {
    fn new(chunk: &mut Chunk, pop_value: bool, src_line: u32) -> Self {
        let jump_i = chunk.get_next_index();
        chunk.add_code(
            OpCode::JumpIfFalse(JumpIfParam {
                pop_value,
                target: u16::MAX,
            }),
            src_line,
        );
        Self { jump_i, pop_value }
    }
    fn set_target(&self, chunk: &mut Chunk, target: u16) {
        chunk.set(
            self.jump_i,
            OpCode::JumpIfFalse(JumpIfParam {
                pop_value: self.pop_value,
                target,
            }),
        );
    }
}
