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

    pub fn next(&mut self) -> Token {
        self.curr_token = self.next_token.clone();
        self.next_token = self.lexer.next();
        self.curr_token.clone()
    }

    pub fn peek(&self) -> Token {
        self.next_token.clone()
    }

    fn parse_program(&mut self) -> Result<Program, ParseError> {
        Err(ParseError{token: self.lexer.peek()})
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{Identifier, InfixExpression, LetStatement};
    use crate::lexer::{Lexer, Token};
    use crate::parser::Parser;

    const TEST_STR: &str = "
    let five = 5;
    let ten = 10;

    let add = fn(x, y) {
      x + y;
    };

    let result = add(five, ten);
    !-/*5;
    5 < 10 > 5;

    if (5 < 10) {
      return true;
    } else {
      return false;
    }

    10 == 10;
    10 != 9;
    ";

    #[test]
    fn test_parser() {
        let lexer = Lexer::new(TEST_STR);
        let mut parser = Parser::new(lexer);

        let mut token = parser.next();
        while token != Token::Eof {
            token = parser.next();
            println!("{}", token);
        }
    }
}