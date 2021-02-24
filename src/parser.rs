use crate::lexer::{Lexer, Token};
use crate::ast::*;
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
        Box::new(Parser { lexer, curr_token, next_token })
    }

    pub fn next(&mut self) -> Token {
        self.curr_token = self.next_token.clone();
        self.next_token = self.lexer.next();
        self.curr_token.clone()
    }

    pub fn peek(&self) -> Token {
        self.next_token.clone()
    }

    fn parse_let_statement(&mut self) -> Box<dyn Statement> {
        let token = self.next();
        let identifer = match token {
            Token::Ident(s) => Identifier::new(Box::new(s)),
            _ => panic!("Invalid token in let statement {}", token)
        };

        let token = self.next();
        match token {
            Token::Assign => true,
            _ => panic!("Invalid token in let statement {}", token)
        };

        let expr = self.parse_expression();
        LetStatement::new(identifer, expr)
    }

    //    fn parse_return_statement(&self) -> Box<dyn Statement> {
//        Box::new()
//    }
//
//    fn parse_if_statement(&self) -> Box<dyn Statement> {
//        Box::new()
//    }
//
    fn parse_expression(&mut self) -> Box<dyn Expression> {
        let token = self.next();
        match token {
            Token::Int(val) => {
                let token = self.next();
                match token {
                    Token::Semicolon => {
                        self.next();
                        Integer::new(val)
                    }
                    Token::Plus => {
                        let expr = self.parse_expression();
                        InfixExpression::new(Integer::new(val), Box::new(String::from("+")), expr)
                    }
                    Token::Minus => {
                        let expr = self.parse_expression();
                        InfixExpression::new(Integer::new(val), Box::new(String::from("-")), expr)
                    }
                    _ => panic!("Not implemented {}", token)
                }
            }
            _ => panic!("Not implemented {}", token)
        }
    }

    pub fn parse_program(&mut self) -> Result<Box<Program>, ParseError> {
        let mut program = Box::new(Program { statements: vec![] });

        while self.curr_token != Token::Eof {
            let statement = match self.curr_token {
                Token::Let => self.parse_let_statement(),
                //    Token::Return => self.parse_return_statement(),
                //    Token::If => self.parse_if_statement(),
                _ => panic!("Invalid token {}", self.curr_token)
            };
            program.statements.push(statement);
        }

        Ok(program)
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{Identifier, InfixExpression, LetStatement, AstNode};
    use crate::lexer::{Lexer, Token};
    use crate::parser::Parser;
    use std::any::Any;

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
            let peek_token = parser.peek();
            println!("{} {}", token, peek_token);
        }
    }

    const TEST_LET_STATEMENTS_STR: &str = "
        let five = 5;
        let ten = 10;
        let twenty = 10 + 10;
        let zero = 10 - 10;
    ";

    #[test]
    fn test_parser_let_statements() {
        let lexer = Lexer::new(TEST_LET_STATEMENTS_STR);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program().unwrap();
        let statements = program.statements;

        assert_eq!(statements.len(), 4);

        for stmt in statements.iter() {
            assert_eq!(AstNode::LetStatement, stmt.ast_node_type());
            let let_stmt :&LetStatement = match stmt.as_any().downcast_ref::<LetStatement>() {
                Some(b) => b,
                None => panic!("Invalid type")
            };
            println!("{}", let_stmt);
        }

        assert_eq!(format!("{}", statements[0]), "five = 5;");
        assert_eq!(format!("{}", statements[1]), "ten = 10;");
        assert_eq!(format!("{}", statements[2]), "twenty = 10 + 10;");
        assert_eq!(format!("{}", statements[3]), "zero = 10 - 10;");
    }
}