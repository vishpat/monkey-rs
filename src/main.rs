mod lexer;
mod ast;
mod parser;
mod evaluator;
mod object;

use linefeed::{Interface, ReadResult};
use crate::lexer::Lexer;

fn main() {

    let mut reader = Interface::new("monkey-rs").unwrap();

    reader.set_prompt("monkey-rs> ").unwrap();

    while let ReadResult::Input(input) = reader.read_line().unwrap() {
        let lexer = Lexer::new(&*input);
        let mut parser = parser::Parser::new(lexer);
        let program = parser.parse_program().unwrap();

        println!("{:?}", program.statements);
    }

    println!("Good bye");
}
