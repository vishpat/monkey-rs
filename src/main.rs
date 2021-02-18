use crate::lexer::{Lexer, Token, TokenType};

mod lexer;

const test_str: &str = "let five = 5;";


fn main() {
    let mut l  = Lexer::new(test_str);
    for s in l.iter() {
        println!("{}", s);
    }
}
