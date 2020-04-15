#![feature(box_syntax, or_patterns)]
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
    #[clap(short = "a", long = "ast", help = "Show parsed AST")]
    pub ast: bool,
    #[clap(short = "b", long = "backtrace", help = "Show backtrace on Err")]
    pub backtrace: bool,
    #[clap(short = "c", long = "libc", help = "Import libc")]
    pub libc: bool,
    #[clap(short = "n", long = "no-verify", help = "Don't verify the LLVM IR")]
    pub no_verify: bool,
    #[clap(short = "o", long = "optimize", help = "Optimize LLVM IR")]
    pub optimize: bool,
    #[clap(short = "p", long = "parse", help = "Run the parser REPL")]
    pub parse: bool,
    #[clap(short = "s", long = "show", help = "Show the compiled LLVM IR")]
    pub show: bool,
}
