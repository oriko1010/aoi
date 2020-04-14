#![allow(dead_code)]

use anyhow::Result;
use aoi::{codegen::Codegen, parser::Parser};
use clap::Clap;
use rustyline::{config::Config, Editor};
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
    #[clap(short = "p", long = "parse", help = "Run the parser REPL")]
    parse: bool,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    if opts.backtrace {
        env::set_var("RUST_BACKTRACE", "1");
    }
    if opts.parse {
        parse_repl()?;
    } else {
        run_file("./example/main.aoi", opts.optimize)?;
    }
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
            let codegen = Codegen::new(&context, optimize, true);
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

fn parse_repl() -> Result<()> {
    let mut rl = Editor::<()>::with_config(Config::builder().auto_add_history(true).build());
    loop {
        let line = rl.readline(">")?;
        if line == ".exit" {
            break;
        }
        let mut parser = Parser::new(line.as_str());
        match parser.parse_program() {
            Ok(program) => println!("{:#?}", program),
            Err(e) => println!("{}", e),
        }
    }
    Ok(())
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
                let codegen = Codegen::new(&context, false, true);
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
