use crate::ast::program::Program;

use self::{
    compiler::{Compiler, StrPool},
    error::InterpreteError,
};

pub mod compiler;
pub mod error;
pub mod vm;

pub struct HandMakeVM {
    vm: vm::VM,
    compiler: Compiler,
    pool: StrPool,
}

impl HandMakeVM {
    pub fn new() -> HandMakeVM {
        HandMakeVM {
            vm: vm::VM::new(),
            compiler: Compiler::new(),
            pool: StrPool::new(),
        }
    }

    pub fn run(&mut self, program: &Program) -> Result<(), InterpreteError> {
        let mut chunk = self.compiler.compile_program(program, &self.pool)?;
        self.vm.run(&mut chunk)
    }
}
