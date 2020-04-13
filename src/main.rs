#![feature(box_syntax, or_patterns)]
#![allow(dead_code)]

mod ast;
mod codegen;
mod lexer;
mod parser;
mod token;

use crate::{codegen::Codegen, parser::Parser};
use anyhow::Result;
use clap::Clap;
use std::{
    env, fs,
    io::{self, Write},
    path::Path,
};

#[derive(Clap)]
#[clap(version = "0.1")]
struct Opts {
    #[clap(short = "b", long = "backtrace", help = "Show backtrace on Err")]
    backtrace: bool,
    #[clap(short = "o", long = "optimize", help = "Optimize LLVM IR")]
    optimize: bool,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    if opts.backtrace {
        env::set_var("RUST_BACKTRACE", "1");
    }
    run_file("./example/main.aoi", opts.optimize)?;
    Ok(())
}

fn run_file(path: impl AsRef<Path>, optimize: bool) -> Result<()> {
    let code = fs::read_to_string(path.as_ref())?;
    let mut parser = Parser::new(code.as_str());
    let program = parser.parse_program();
    match program {
        Ok(program) => {
            println!("{:?}", program);
            let context = inkwell::context::Context::create();
            let codegen = Codegen::new(&context, optimize);
            let success = codegen.compile(program);
            println!("Codegen done with: {:?}", success);
            Ok(())
        }
        Err(e) => {
            eprintln!("{}", e);
            Ok(())
        }
    }
}

fn repl() -> Result<()> {
    let mut buffer = String::with_capacity(128);

    loop {
        print!(">");
        io::stdout().flush()?;

        buffer.clear();
        io::stdin().read_line(&mut buffer)?;

        let mut parser = Parser::new(buffer.as_str());
        let program = parser.parse_program();
        match program {
            Ok(program) => {
                println!("{:?}", program);
                let context = inkwell::context::Context::create();
                let codegen = Codegen::new(&context, false);
                let success = codegen.compile(program);
                println!("Codegen done with: {:?}", success);
            }
            Err(e) => println!("{}", e),
        }

        if buffer == ".exit" {
            break;
        }
    }
    Ok(())
}
