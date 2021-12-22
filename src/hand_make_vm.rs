use crate::ast::program::Program;

use self::{compile::CompileRun, compile::StrPool, error::InterpreteError};

pub mod compile;
pub mod error;
pub mod vm;

pub struct HandMakeVM {
    vm: vm::VM,
    pool: StrPool,
}

impl HandMakeVM {
    pub fn new() -> HandMakeVM {
        HandMakeVM {
            vm: vm::VM::new(),
            pool: StrPool::new(),
        }
    }

    pub fn run(&mut self, program: &Program) -> Result<(), InterpreteError> {
        let mut chunk = CompileRun::compile(program, &self.pool)?;
        self.vm.run(&mut chunk)
    }

    pub fn show_compile(&mut self, program: &Program) -> Result<(), InterpreteError> {
        CompileRun::compile(program, &self.pool)?.print_chunk();
        Ok(())
    }
}
