mod lexer;
mod ast;
mod parser;
mod object;
mod environment;
mod evaluator;
mod inbuilt;

use linefeed::{Interface, ReadResult};
use crate::lexer::Lexer;
use crate::evaluator::eval_program;
use std::rc::Rc;
use std::cell::RefCell;
use crate::environment::Environment;

fn main() {

    let mut reader = Interface::new("monkey-rs").unwrap();
    let mut env = Rc::new(RefCell::new(Environment::new()));

    reader.set_prompt("monkey-rs> ").unwrap();

    while let ReadResult::Input(input) = reader.read_line().unwrap() {
        if input.eq("exit") {
            break;
        }
        let lexer = Lexer::new(&*input);
        let mut parser = parser::Parser::new(lexer);
        let program = parser.parse_program().unwrap();

        println!("{}", eval_program(program.as_ref(), &mut env));
    }

    println!("Good bye");
}
