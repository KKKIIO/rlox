use std::{
    fs::File,
    io::{self, Read, Write},
    process::exit,
};

use clap::{App, Arg};
use hand_make_vm::{str_pool::StrPool, vm::VM};

use crate::{ast::parse_source, hand_make_vm::compile::compile};

mod ast;
mod hand_make_vm;
fn main() {
    let matches = App::new("rlox")
        .arg(Arg::with_name("script").help("Script file path").index(1))
        .arg(
            Arg::with_name("show-compile")
                .short("s")
                .long("show-compile")
                .help("Show compile result"),
        )
        .get_matches();
    let show_compile = matches.is_present("show-compile");
    if let Some(fp) = matches.value_of("script") {
        let mut f = File::open(fp).unwrap();
        let mut buf = Vec::new();
        f.read_to_end(&mut buf).unwrap();
        let program = match parse_source(&buf) {
            Ok(program) => program,
            Err(errs) => {
                for err in errs.iter() {
                    eprintln!("{}", err);
                }
                exit(65);
            }
        };
        let pool = StrPool::new();
        let module = match compile(&program, &pool) {
            Ok(program) => program,
            Err(err) => {
                eprintln!("{}", err);
                exit(65);
            }
        };
        if show_compile {
            println!("{}", module);
        } else {
            let mut vm = VM::new(&pool);
            if let Err(err) = vm.run(module) {
                eprintln!("{}\n[line {}]", err.message, err.line);
                exit(70);
            }
        }
    } else {
        let mut line = String::new();
        let pool = StrPool::new();
        let mut vm = VM::new(&pool);
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
            let program = match parse_source(line.as_bytes()) {
                Ok(program) => program,
                Err(errs) => {
                    for err in errs.iter() {
                        eprintln!("{}", err);
                    }
                    continue;
                }
            };

            let module = match compile(&program, &pool) {
                Ok(program) => program,
                Err(err) => {
                    eprintln!("{}", err);
                    continue;
                }
            };
            if let Err(err) = { vm.run(module) } {
                println!("{}\n[line {}] in script", err.message, err.line);
            }
        }
    }
}
