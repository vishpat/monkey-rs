use crate::lexer::{Lexer, Token, TokenType};

mod lexer;

fn main() {
    let mut l  = Lexer::new("x + y");
    let tokens: Vec<Token> = l.iter().map(|s| Token::new(TokenType::ILLEGAL, String::from(s))).collect();
    for token in tokens {
        println!("{}", token.literal);
    }
}
