use std::{
    convert::TryInto,
    num::TryFromIntError,
    ops::{Deref, Neg},
    rc::Rc,
};

use crate::ast::{
    error::GrammarError,
    expression::{Expression, LiteralValue},
    statement::{BlockStmt, DeclOrStmt, File, Statement, VarDecl},
    token::{Token, TokenType},
};

use super::{
    chunk::Chunk,
    str_pool::StrPool,
    vm::{ClassPrototype, FunPrototype, Module, OpCode, UpvalueIndex},
};

pub fn compile<'s>(
    program: &'_ File<'s>,
    str_pool: &'_ StrPool,
) -> Result<Module, GrammarError<'s>> {
    let mut funs = Vec::new();
    let mut classes = Vec::new();
    let mut scopes = vec![Scope::new()];
    let mut c = StmtsCompiler::new(
        CompileType::Script,
        str_pool,
        &mut scopes,
        &mut funs,
        &mut classes,
    );
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
    fn new() -> Self {
        Self {
            vars: Vec::new(),
            var_count_per_block: Vec::new(),
            upvalue_indexes: Vec::new(),
        }
    }
    fn is_in_global(&self) -> bool {
        self.var_count_per_block.is_empty()
    }
    fn new_block(&mut self) {
        self.var_count_per_block.push(0);
    }
    fn close_block(&mut self) -> Box<[bool]> {
        let cnt = self.var_count_per_block.pop().unwrap();
        self.vars
            .drain((self.vars.len() - (cnt as usize))..)
            .map(|(_, captured)| captured)
            .collect()
    }
    fn add_local(&mut self, name: &'s str) -> Result<(), &'static str> {
        if self.vars.len() >= u8::MAX as usize {
            return Err("Too many local variables in function.");
        }
        let cnt = self.var_count_per_block.last_mut().unwrap();
        if self.vars[self.vars.len() - (*cnt as usize)..]
            .iter()
            .any(|&(n, _)| n == name)
        {
            return Err("Already a variable with this name in this scope.");
        }
        self.vars.push((name, false));
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
        let position = self.position(name);
        if let &Some(i) = &position {
            self.vars[i as usize].1 = true;
        }
        position
    }
    fn register_upvalue(&mut self, idx: UpvalueIndex) -> Result<u8, &'static str> {
        if let Some(i) = self.upvalue_indexes.iter().position(|&x| x == idx) {
            Ok(i.try_into().unwrap())
        } else {
            let i = self
                .upvalue_indexes
                .len()
                .try_into()
                .map_err(|_| "Too many closure variables in function.")?;
            self.upvalue_indexes.push(idx);
            Ok(i)
        }
    }
}

enum CompileType {
    Script,
    Fun,
    Method,
    Initializer,
}

struct StmtsCompiler<'s, 'o> {
    compile_type: CompileType,
    str_pool: &'o StrPool,
    scopes: &'o mut Vec<Scope<'s>>,
    funs: &'o mut Vec<FunPrototype>,
    classes: &'o mut Vec<ClassPrototype>,
    chunk: Chunk<'o>,
}

impl<'s, 'o> StmtsCompiler<'s, 'o> {
    fn new(
        compile_type: CompileType,
        str_pool: &'o StrPool,
        scopes: &'o mut Vec<Scope<'s>>,
        funs: &'o mut Vec<FunPrototype>,
        classes: &'o mut Vec<ClassPrototype>,
    ) -> Self {
        Self {
            compile_type,
            str_pool,
            scopes,
            funs,
            classes,
            chunk: Chunk::new(str_pool),
        }
    }
    fn compile_decl_or_stmt(&'_ mut self, ds: &'_ DeclOrStmt<'s>) -> Result<(), GrammarError<'s>> {
        match ds {
            DeclOrStmt::FunDecl(decl) => {
                let in_global_scope = self.curr_scope().is_in_global();
                // early bind
                if !in_global_scope {
                    self.curr_scope_mut()
                        .add_local(decl.name.lexeme)
                        .map_err(|e| GrammarError::at_token(e, decl.name))?
                }
                let (codes, upvalue_indexes) = {
                    self.scopes.push(Scope::new());
                    let mut c = StmtsCompiler::new(
                        CompileType::Fun,
                        self.str_pool,
                        &mut self.scopes,
                        self.funs,
                        self.classes,
                    );
                    c.curr_scope_mut().new_block();
                    // trick: unify stack layout with method
                    c.curr_scope_mut().add_local("").unwrap();
                    for name in decl.params.iter() {
                        c.curr_scope_mut()
                            .add_local(name.lexeme)
                            .map_err(|e| GrammarError::at_token(e, *name))?;
                    }
                    let block = &decl.body;
                    for stmt in block.stmts.iter() {
                        c.compile_decl_or_stmt(&stmt)?;
                    }
                    c.compile_implicit_return(decl.body.right_brace_line);
                    (
                        c.chunk.build().into(),
                        c.scopes.pop().unwrap().upvalue_indexes.into_boxed_slice(),
                    )
                };

                let fun = FunPrototype {
                    name: self.str_pool.register_rc(decl.name.lexeme),
                    arity: decl.params.len().try_into().unwrap(),
                    codes,
                    upvalue_indexes,
                };

                let fun_id = self.funs.len().try_into().unwrap();
                self.funs.push(fun);
                self.chunk
                    .add_code(OpCode::MakeClosure(fun_id), decl.fun_line);
                if in_global_scope {
                    self.chunk.add_code(
                        OpCode::DefGlobalVar(self.str_pool.register(decl.name.lexeme)),
                        decl.name.line,
                    );
                }
            }
            DeclOrStmt::VarDecl(d) => self.compile_var_decl(d)?,
            DeclOrStmt::Stmt(ref stmt) => self.compile_stmt(stmt)?,
            DeclOrStmt::ClassDecl(decl) => {
                if let Some(super_cls) = decl.super_class {
                    if decl.name.lexeme == super_cls.lexeme {
                        return Err(GrammarError::at_token(
                            "A class can't inherit from itself.",
                            super_cls,
                        ));
                    }
                    let name = super_cls;
                    if !self.resolve_var(name)? {
                        self.chunk.add_code(
                            OpCode::LoadGlobalVar(self.str_pool.register(name.lexeme)),
                            name.line,
                        );
                    }
                }
                let in_global_scope = self.curr_scope().is_in_global();
                // early bind
                if !in_global_scope {
                    self.curr_scope_mut()
                        .add_local(decl.name.lexeme)
                        .map_err(|e| GrammarError::at_token(e, decl.name))?
                }
                let methods: Box<[Rc<FunPrototype>]> = decl
                    .methods
                    .iter()
                    .map(|d| -> Result<Rc<FunPrototype>, GrammarError<'s>> {
                        self.scopes.push(Scope::new());
                        let compile_type = if d.name.lexeme == "init" {
                            CompileType::Initializer
                        } else {
                            CompileType::Method
                        };
                        let mut c = StmtsCompiler::new(
                            compile_type,
                            self.str_pool,
                            &mut self.scopes,
                            self.funs,
                            self.classes,
                        );
                        c.curr_scope_mut().new_block();
                        c.curr_scope_mut().add_local("this").unwrap();
                        for name in d.params.iter() {
                            c.curr_scope_mut()
                                .add_local(name.lexeme)
                                .map_err(|e| GrammarError::at_token(e, *name))?;
                        }
                        let block = &d.body;
                        for stmt in block.stmts.iter() {
                            c.compile_decl_or_stmt(&stmt)?;
                        }
                        c.compile_implicit_return(d.body.right_brace_line);
                        let upvalue_indexes =
                            c.scopes.pop().unwrap().upvalue_indexes.into_boxed_slice();
                        let codes = c.chunk.build().into();
                        Ok(FunPrototype {
                            name: self.str_pool.register_rc(d.name.lexeme),
                            arity: d.params.len().try_into().unwrap(),
                            codes,
                            upvalue_indexes,
                        }
                        .into())
                    })
                    .collect::<Result<Box<[Rc<FunPrototype>]>, GrammarError<'s>>>()?;

                let id = self.classes.len().try_into().unwrap();
                self.classes.push(ClassPrototype {
                    name: self.str_pool.register_rc(decl.name.lexeme),
                    has_super: decl.super_class.is_some(),
                    methods,
                });
                self.chunk.add_code(OpCode::MakeClass(id), decl.class_line);
                if in_global_scope {
                    self.chunk.add_code(
                        OpCode::DefGlobalVar(self.str_pool.register(decl.name.lexeme)),
                        decl.name.line,
                    );
                }
            }
        };
        Ok(())
    }

    fn compile_var_decl(&mut self, v: &VarDecl<'s>) -> Result<(), GrammarError<'s>> {
        if let Some(init_expr) = &v.init_expr {
            self.compile_expression(init_expr)?;
        } else {
            self.chunk.add_code(OpCode::LoadNil, v.name.line);
        }
        let name = v.name;
        let scope = self.scopes.last_mut().unwrap();
        if scope.is_in_global() {
            self.chunk.add_code(
                OpCode::DefGlobalVar(self.str_pool.register(name.lexeme)),
                name.line,
            );
            Ok(())
        } else {
            scope
                .add_local(name.lexeme)
                .map_err(|e| GrammarError::at_token(e, name))
        }
    }

    fn compile_stmt(&mut self, stmt: &Statement<'s>) -> Result<(), GrammarError<'s>> {
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
                self.compile_expression(&stmt.cond)?;
                let jover_then = JumpIfFalseC::new(&mut self.chunk, stmt.if_.line);
                self.chunk.add_code(OpCode::Pop, stmt.if_.line);
                self.compile_stmt(&stmt.then_branch)?;
                let jover_else = JumpC::new(&mut self.chunk, stmt.if_.line);
                jover_then.jump_forward(&mut self.chunk).map_err(|_| {
                    GrammarError::at_token(ERR_JUMP_OFFSET_OVERFLOW, stmt.then_branch_last)
                })?;
                self.chunk.add_code(OpCode::Pop, stmt.if_.line);
                if let Some((_, else_branch, else_branch_last)) = &stmt.else_branch {
                    self.compile_stmt(&else_branch)?;
                    // workaround for the `GrammarError::at_token`
                    jover_else.jump_forward(&mut self.chunk).map_err(|_| {
                        GrammarError::at_token(ERR_JUMP_OFFSET_OVERFLOW, *else_branch_last)
                    })?;
                } else {
                    jover_else.jump_forward(&mut self.chunk).unwrap();
                }
            }
            Statement::While(stmt) => {
                let cond_i = self.chunk.get_next_index();
                self.compile_expression(&stmt.cond)?;
                let jover_body = JumpIfFalseC::new(&mut self.chunk, stmt.while_.line);
                self.chunk.add_code(OpCode::Pop, stmt.while_.line);
                self.compile_stmt(&stmt.body)?;
                let jback = JumpC::new(&mut self.chunk, stmt.while_.line);
                jback.jump_backward(&mut self.chunk, cond_i).map_err(|_| {
                    GrammarError::at_token(ERR_JUMP_OFFSET_OVERFLOW_IN_LOOP, stmt.body_last)
                })?;
                jover_body.jump_forward(&mut self.chunk).map_err(|_| {
                    GrammarError::at_token(ERR_JUMP_OFFSET_OVERFLOW_IN_LOOP, stmt.body_last)
                })?;
                self.chunk.add_code(OpCode::Pop, stmt.while_.line);
            }
            Statement::For(stmt) => {
                self.scopes.last_mut().unwrap().new_block();
                if let Some(init) = &stmt.init {
                    match init.deref() {
                        DeclOrStmt::VarDecl(l) => {
                            self.compile_var_decl(l)?;
                        }
                        DeclOrStmt::Stmt(Statement::Expr(l)) => {
                            self.compile_expression(&l.expr)?;
                        }
                        _ => panic!("for init is not decl or expr, but {:?}", init),
                    }
                }
                let line = stmt.for_.line;
                let cond_i = self.chunk.get_next_index();
                let jover_body = if let Some(cond) = &stmt.cond {
                    self.compile_expression(cond)?;
                    let jover_body = JumpIfFalseC::new(&mut self.chunk, line);
                    self.chunk.add_code(OpCode::Pop, line);
                    Some(jover_body)
                } else {
                    None
                };
                self.compile_stmt(&stmt.body)?;
                if let Some(post) = &stmt.post {
                    self.compile_expression(post)?;
                    self.chunk.add_code(OpCode::Pop, line);
                }
                JumpC::new(&mut self.chunk, line)
                    .jump_backward(&mut self.chunk, cond_i)
                    .map_err(|_| {
                        GrammarError::at_token(ERR_JUMP_OFFSET_OVERFLOW_IN_LOOP, stmt.body_last)
                    })?;
                if let Some(jif) = jover_body {
                    jif.jump_forward(&mut self.chunk).map_err(|_| {
                        GrammarError::at_token(ERR_JUMP_OFFSET_OVERFLOW_IN_LOOP, stmt.body_last)
                    })?;
                    self.chunk.add_code(OpCode::Pop, line);
                }
                let vars = self.scopes.last_mut().unwrap().close_block();
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
                if self.scopes.len() < 2 {
                    return Err(GrammarError::at_token(
                        "Can't return from top-level code.",
                        r.return_,
                    ));
                }
                if let Some(value) = &r.value {
                    if let CompileType::Initializer = self.compile_type {
                        return Err(GrammarError::at_token(
                            "Can't return a value from an initializer.",
                            r.return_,
                        ));
                    }
                    self.compile_expression(value)?;
                    self.chunk.add_code(OpCode::Return, r.return_.line);
                } else {
                    self.compile_implicit_return(r.return_.line);
                }
            }
        };
        Ok(())
    }

    fn compile_implicit_return(&mut self, src_line: u32) {
        if let CompileType::Initializer = self.compile_type {
            self.chunk.add_code(OpCode::LoadLocalVar(0), src_line);
        } else {
            self.chunk.add_code(OpCode::LoadNil, src_line);
        };
        self.chunk.add_code(OpCode::Return, src_line);
    }

    fn compile_block(&mut self, block: &BlockStmt<'s>) -> Result<(), GrammarError<'s>> {
        self.scopes.last_mut().unwrap().new_block();
        for stmt in block.stmts.iter() {
            self.compile_decl_or_stmt(&stmt)?;
        }
        let vars = self.scopes.last_mut().unwrap().close_block();
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
    fn compile_expression(&'_ mut self, expr: &'_ Expression<'s>) -> Result<(), GrammarError<'s>> {
        match &expr {
            Expression::Literal(l) => {
                let line = l.line;
                match &l.value {
                    &LiteralValue::Number(n) => {
                        self.chunk.add_code(OpCode::LoadNumber(n), line);
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
                let op_code = match u.op.ttype {
                    TokenType::Minus => (OpCode::Negate),
                    TokenType::Bang => (OpCode::Not),
                    _ => panic!("unknown unary op={:?}", u.op),
                };
                self.compile_expression(&u.right)?;
                self.chunk.add_code(op_code, u.op.line);
            }
            Expression::Binary(b) => {
                self.compile_expression(&b.left)?;
                let line = b.op.line;
                match b.op.ttype {
                    TokenType::And => {
                        let jover_rhs = JumpIfFalseC::new(&mut self.chunk, line);
                        self.chunk.add_code(OpCode::Pop, line);
                        self.compile_expression(&b.right)?;
                        jover_rhs
                            .jump_forward(&mut self.chunk)
                            .map_err(|_| GrammarError::at_token(ERR_JUMP_OFFSET_OVERFLOW, b.op))?;
                    }
                    TokenType::Or => {
                        let jto_rhs = JumpIfFalseC::new(&mut self.chunk, line);
                        let jover_rhs = JumpC::new(&mut self.chunk, line);
                        jto_rhs
                            .jump_forward(&mut self.chunk)
                            .map_err(|_| GrammarError::at_token(ERR_JUMP_OFFSET_OVERFLOW, b.op))?;
                        self.chunk.add_code(OpCode::Pop, line);
                        self.compile_expression(&b.right)?;
                        jover_rhs
                            .jump_forward(&mut self.chunk)
                            .map_err(|_| GrammarError::at_token(ERR_JUMP_OFFSET_OVERFLOW, b.op))?;
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
                let name = v.name;
                if !self.resolve_var(name)? {
                    self.chunk.add_code(
                        OpCode::LoadGlobalVar(self.str_pool.register(name.lexeme)),
                        name.line,
                    );
                }
            }
            Expression::This(t) => {
                if !self.resolve_var(t.this)? {
                    return Err(GrammarError::at_token(
                        "Can't use 'this' outside of a class.",
                        t.this,
                    ));
                }
            }
            Expression::Assignment(a) => match &a.lvalue {
                crate::ast::expression::LValue::Variable(v) => {
                    self.compile_expression(&a.expr)?;
                    let name = v.name;
                    if let Some(idx) = self.curr_scope().position(name.lexeme) {
                        self.chunk.add_code(OpCode::SetLobalVar(idx), a.op_line);
                    } else if let Some(idx) =
                        resolve_upvalue(self.scopes, self.scopes.len() - 1, name.lexeme)
                            .map_err(|e| GrammarError::at_token(e, name))?
                    {
                        self.chunk.add_code(OpCode::SetUpvalue(idx), a.op_line);
                    } else {
                        self.chunk.add_code(
                            OpCode::SetGlobalVar(self.str_pool.register(name.lexeme)),
                            a.op_line,
                        );
                    }
                }
                crate::ast::expression::LValue::Get(g) => {
                    self.compile_expression(&g.expr)?;
                    self.compile_expression(&a.expr)?;
                    self.chunk.add_code(
                        OpCode::SetProp(self.str_pool.register(g.name.lexeme)),
                        a.op_line,
                    );
                }
            },
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
            Expression::Get(g) => {
                self.compile_expression(&g.expr)?;
                self.chunk.add_code(
                    OpCode::GetProp(self.str_pool.register(g.name.lexeme)),
                    g.dot.line,
                );
            }
        }
        Ok(())
    }

    fn resolve_var(&mut self, name: Token<'s>) -> Result<bool, GrammarError<'s>> {
        Ok(
            if let Some(idx) = self.curr_scope_mut().position(name.lexeme) {
                self.chunk.add_code(OpCode::LoadLocalVar(idx), name.line);
                true
            } else if let Some(idx) =
                resolve_upvalue(self.scopes, self.scopes.len() - 1, name.lexeme)
                    .map_err(|e| GrammarError::at_token(e, name))?
            {
                self.chunk.add_code(OpCode::LoadUpvalue(idx), name.line);
                true
            } else {
                false
            },
        )
    }

    fn curr_scope(&self) -> &Scope<'s> {
        self.scopes.last().unwrap()
    }
    fn curr_scope_mut(&mut self) -> &mut Scope<'s> {
        self.scopes.last_mut().unwrap()
    }
}

fn resolve_upvalue<'s>(
    scopes: &'_ mut Vec<Scope<'s>>,
    curr: usize,
    name: &'s str,
) -> Result<Option<u8>, &'static str> {
    if curr <= 0 {
        return Ok(None);
    }
    let outer = curr - 1;
    let v = if let Some(idx) = scopes[outer].try_capture(name) {
        UpvalueIndex::Local(idx)
    } else if let Some(idx) = resolve_upvalue(scopes, outer, name)? {
        UpvalueIndex::Upvalue(idx)
    } else {
        return Ok(None);
    };

    scopes[curr].register_upvalue(v).map(|no| Some(no))
}

struct JumpC {
    jump_i: usize,
}

impl JumpC {
    fn new(chunk: &mut Chunk, src_line: u32) -> Self {
        let jump_i = chunk.get_next_index();
        chunk.add_code(OpCode::Jump(i16::MAX), src_line);
        Self { jump_i }
    }

    fn jump_forward(self, chunk: &mut Chunk) -> Result<(), TryFromIntError> {
        let target_i = chunk.get_next_index();
        let jump_i = self.jump_i;
        assert!(jump_i < target_i);
        let offset = (target_i - jump_i).try_into()?;
        chunk.set(jump_i, OpCode::Jump(offset));
        Ok(())
    }
    fn jump_backward(self, chunk: &mut Chunk, target_i: usize) -> Result<(), TryFromIntError> {
        let jump_i = self.jump_i;
        assert!(jump_i > target_i);
        let offset: i16 = (jump_i - target_i).try_into()?;
        chunk.set(jump_i, OpCode::Jump(offset.neg()));
        Ok(())
    }
}

struct JumpIfFalseC {
    jump_i: usize,
}

impl JumpIfFalseC {
    fn new(chunk: &mut Chunk, src_line: u32) -> Self {
        let jump_i = chunk.get_next_index();
        chunk.add_code(OpCode::JumpIfFalse(i16::MAX), src_line);
        Self { jump_i }
    }

    fn jump_forward(self, chunk: &mut Chunk) -> Result<(), TryFromIntError> {
        let target_i = chunk.get_next_index();
        let jump_i = self.jump_i;
        assert!(jump_i < target_i);
        let offset = (target_i - jump_i).try_into()?;
        chunk.set(self.jump_i, OpCode::JumpIfFalse(offset));
        Ok(())
    }
}

#[cfg(test)]
mod test {

    use std::ops::Deref;

    use crate::ast::parse_source;

    use super::*;

    #[test]
    fn test_resolve_upvalue() {
        let mut s1 = Scope::new();
        s1.new_block();
        s1.add_local("a").unwrap();
        let mut vec = vec![s1, Scope::new(), Scope::new()];
        let upvalue_no = resolve_upvalue(&mut vec, 2, "a").unwrap();
        assert_eq!(upvalue_no, Some(0));
        assert_eq!(
            vec.last().unwrap().upvalue_indexes[0],
            UpvalueIndex::Upvalue(0)
        );
    }

    #[test]
    fn test_pop_open_upvalue() {
        let str_pool = StrPool::new();
        let Module { main, funs, .. } = compile(
            &parse_source(
                r#"
{
    var a = 1;
    fun f() {
        print a;
    }
}
        "#
                .as_bytes(),
            )
            .unwrap(),
            &str_pool,
        )
        .unwrap();
        assert_eq!(
            main.codes,
            [
                OpCode::LoadNumber(1.),
                OpCode::MakeClosure(0),
                OpCode::Pop,
                OpCode::PopMaybeUpvalue,
                OpCode::Return,
            ]
            .into()
        );
        let f = &funs[0];
        assert_eq!(f.name.deref(), "f");
        assert_eq!(f.upvalue_indexes, [UpvalueIndex::Local(0)].into());
        assert_eq!(
            f.codes.codes,
            [
                OpCode::LoadUpvalue(0),
                OpCode::Print,
                OpCode::LoadNil,
                OpCode::Return,
            ]
            .into()
        );
    }
    #[test]
    fn test_mix_if_and_logic_op() {
        let str_pool = StrPool::new();
        let Module { main, .. } = compile(
            &parse_source(
                r#"
{
    if ((1 < 2 and 4 < 3) or true) {
        print 1;
    } else {
        print 0;
    }
}
                "#
                .as_bytes(),
            )
            .unwrap(),
            &str_pool,
        )
        .unwrap();
        assert_eq!(
            main.codes,
            [
                OpCode::LoadNumber(1.),
                OpCode::LoadNumber(2.),
                OpCode::Less,
                OpCode::JumpIfFalse(5), // and
                OpCode::Pop,
                OpCode::LoadNumber(4.),
                OpCode::LoadNumber(3.),
                OpCode::Less,
                OpCode::JumpIfFalse(2), // or
                OpCode::Jump(3),
                OpCode::Pop,
                OpCode::LoadTrue,
                OpCode::JumpIfFalse(5), // if
                OpCode::Pop,
                OpCode::LoadNumber(1.),
                OpCode::Print,
                OpCode::Jump(4),
                OpCode::Pop, // else
                OpCode::LoadNumber(0.),
                OpCode::Print,
                OpCode::Return,
            ]
            .into()
        );
    }
}

const ERR_JUMP_OFFSET_OVERFLOW: &str = "Too much code to jump over.";
const ERR_JUMP_OFFSET_OVERFLOW_IN_LOOP: &str = "Loop body too large.";
