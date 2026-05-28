mod ast;
mod types;
mod checker;
mod safety;
mod substitution;
mod interpreter;
mod error;
mod lexer;
mod parser;
mod tests;

use tests::test_example;

fn main() {
    println!("tau-relax");
    test_example();

}