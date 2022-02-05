use std::{convert::TryFrom, fmt::Display};

use super::{str_pool::StrPool, vm::OpCode};

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

    pub fn add_code(&mut self, code: OpCode, line: u32) -> usize {
        assert_eq!(self.codes.len(), self.lines.len());
        let i = self.codes.len();
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

    pub fn get_next_index(&mut self) -> usize {
        self.codes.len()
    }

    pub fn set(&mut self, i: usize, code: OpCode) {
        self.codes[i as usize] = code;
    }

    pub fn build(self) -> Codes {
        Codes {
            codes: self.codes.into_boxed_slice(),
            lines: self.lines.into_boxed_slice(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Codes {
    pub codes: Box<[OpCode]>,
    lines: Box<[u32]>,
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
