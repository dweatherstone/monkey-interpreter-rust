use std::io;

use crate::repl::start;

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod repl;
pub mod token;

fn main() {
    println!("Hello! This is the basic interpreter");
    println!("Write the code below:");
    start(io::stdin(), io::stdout());
}
