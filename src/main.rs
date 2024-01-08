#![allow(unused)]

use std::io;

use crate::repl::start;

pub mod lexer;
pub mod repl;
pub mod token;

fn main() {
    println!("Hello! This is the basic interpreter");
    println!("Write the code below:");
    start(io::stdin(), io::stdout());
}
