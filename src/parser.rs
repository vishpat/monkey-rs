use crate::lexer::{Lexer, Token};
use crate::ast::{Program};
use std::error::Error;
use std::fmt;
use std::fmt::{Debug, Display};

#[derive(Debug)]
struct ParseError {
    token: Token,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Problem parsing near token {}", self.token)
    }
}

struct Parser {
    lexer: Box<Lexer>,
    curr_token: Token,
    next_token: Token,
}

impl Parser {
    pub fn new(mut lexer: Box<Lexer>) -> Box<Parser> {
        let curr_token = lexer.next();
        let next_token = lexer.next();
        Box::new(Parser{lexer, curr_token, next_token})
    }

    pub fn next(mut self) -> Token {
        self.curr_token = self.next_token.clone();
        self.next_token = self.lexer.next();
        self.curr_token
    }

    pub fn peek(self) -> Token {
        self.next_token.clone()
    }

    fn parse_program(&mut self) -> Result<Program, ParseError> {
        Err(ParseError{token: self.lexer.peek()})
    }
}