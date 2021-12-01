use std::{
    env::args,
    fs::File,
    io::{self, Read, Write},
    process::exit,
};

use vm::VM;

use crate::ast::parse_source;

mod ast;
mod vm;
fn main() {
    let args = args().skip(1).collect::<Vec<_>>();
    if args.len() > 1 {
        eprintln!("Usage: rlox [script]");
        exit(64);
    }
    let filepath = args.get(0);
    let mut vm = VM::new();
    if let Some(fp) = filepath {
        let mut f = File::open(fp).unwrap();
        let mut buf = String::new();
        f.read_to_string(&mut buf).unwrap();
        let program = parse_source(buf.as_str().into()).unwrap();
        vm.run(&program).unwrap();
    } else {
        let mut line = String::new();
        loop {
            line.clear();
            print!("> ");
            io::stdout().flush().unwrap();
            if let Err(e) = io::stdin().read_line(&mut line) {
                println!("{}", e);
                exit(74);
            }
            let line = line.trim();
            if line == "exit" {
                break;
            }
            match parse_source(line.into()) {
                Ok(program) => {
                    if let Err(err) = vm.run(&program) {
                        println!("vm.run error: {}", err);
                    }
                }
                Err(e) => {
                    println!("parse error: {}", e);
                }
            }
        }
    }
}
