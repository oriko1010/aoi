#![allow(dead_code)]

use anyhow::Result;
use aoi::{codegen, parser::Parser, AoiOptions};
use clap::Clap;
use rustyline::{config::Config, Editor};
use std::{env, fs};

fn main() -> Result<()> {
    let opts = AoiOptions::parse();
    if opts.backtrace {
        env::set_var("RUST_BACKTRACE", "1");
    }
    if opts.parse {
        parse_repl()?;
    } else {
        run_file(&opts)?;
    }
    Ok(())
}

fn run_file(opts: &AoiOptions) -> Result<()> {
    let code = fs::read_to_string(&opts.file)?;
    let mut parser = Parser::new(code.as_str());
    let program = parser.parse_program();
    match program {
        Ok(program) => {
            if opts.ast {
                println!("{:#?}", program);
            }
            let success = codegen::compile(program, opts);
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
