#![feature(destructuring_assignment)]
#![feature(box_patterns)]
use std::{
    fs::File,
    io::{self, Read, Write},
    process::exit,
};

use clap::{App, Arg};
use hand_make_vm::HandMakeVM;

use crate::ast::parse_source;

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
    let mut vm = HandMakeVM::new();
    if let Some(fp) = matches.value_of("script") {
        let mut f = File::open(fp).unwrap();
        let mut buf = Vec::new();
        f.read_to_end(&mut buf).unwrap();
        match parse_source(&buf) {
            Ok(program) => {
                if let Err(err) = if show_compile {
                    vm.show_compile(&program)
                } else {
                    vm.run(&program)
                } {
                    eprintln!("{}\n[line {}]", err.message, err.line);
                    exit(70);
                }
            }
            Err(errs) => {
                for err in errs.iter() {
                    eprintln!("{}", err);
                }
                exit(65);
            }
        }
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
            match parse_source(line.as_bytes()) {
                Ok(program) => {
                    if let Err(err) = vm.run(&program) {
                        println!("{}\n[line {}] in script", err.message, err.line);
                    }
                }
                Err(errs) => {
                    for err in errs.iter() {
                        eprintln!("{}", err);
                    }
                }
            }
        }
    }
}
