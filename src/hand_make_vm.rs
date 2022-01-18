use crate::ast::statement::Program;

use self::{compile::compile, compile::StrPool, error::InterpreteError};

pub mod compile;
pub mod error;
pub mod vm;

pub fn run(program: &Program) -> Result<(), InterpreteError> {
    let pool = StrPool::new();
    let codes = compile(program, &pool)?;
    let mut vm = vm::VM::new(&pool);
    vm.run(&codes)
}

pub fn show_compile(program: &Program) -> Result<(), InterpreteError> {
    let pool = StrPool::new();
    println!("{}", compile(program, &pool)?);
    Ok(())
}
