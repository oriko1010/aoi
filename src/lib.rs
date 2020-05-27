#![feature(or_patterns)]
#![allow(dead_code)]

pub mod ast;
pub mod codegen;
pub mod lexer;
pub mod parser;
pub mod token;

use clap::Clap;

#[derive(Clap)]
#[clap(version = "0.1")]
pub struct AoiOptions {
    #[clap(default_value = "./example/main.aoi")]
    pub file: String,
    #[clap(short = "a", long = "ast", about = "Show parsed AST")]
    pub ast: bool,
    #[clap(short = "b", long = "backtrace", about = "Show backtrace on Err")]
    pub backtrace: bool,
    #[clap(short = "c", long = "libc", about = "Import libc")]
    pub libc: bool,
    #[clap(short = "n", long = "no-verify", about = "Don't verify the LLVM IR")]
    pub no_verify: bool,
    #[clap(short = "o", long = "optimize", about = "Optimize LLVM IR")]
    pub optimize: bool,
    #[clap(short = "p", long = "parse", about = "Run the parser REPL")]
    pub parse: bool,
    #[clap(short = "s", long = "show", about = "Show the compiled LLVM IR")]
    pub show: bool,
}
