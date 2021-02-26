use crate::lexer::{Lexer, Token};
use crate::ast::*;
use std::error::Error;
use std::fmt;
use std::fmt::{Debug, Display};
use std::collections::HashMap;
use crate::ast::AstNode::IdentifierExpression;

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd)]
enum Precedence {
    LOWEST,
    EQUALS,
    LESSGREATER,
    SUM,
    PRODUCT,
    PREFIX,
    CALL,
}

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
        Box::new(Parser { lexer, curr_token, next_token})
    }

    pub fn next(&mut self) -> Token {
        self.curr_token = self.next_token.clone();
        self.next_token = self.lexer.next();
        self.curr_token.clone()
    }

    pub fn is_curr_token(&self, token: Token) -> bool {
        self.curr_token == token
    }

    pub fn peek(&self) -> Token {
        self.next_token.clone()
    }

    pub fn peek_precedence(&self) -> Precedence {
        let next_token = self.peek();

        match next_token {
            Token::Plus => Precedence::SUM,
            Token::Asterik => Precedence::PRODUCT,
            Token::Minus => Precedence::SUM,
            Token::Int(i) => Precedence::PREFIX,
            _ => panic!("Precedence not found for peek token {}", next_token),
        }
    }


    pub fn is_next_token(&self, peek_token: Token) -> bool {
        self.next_token == peek_token
    }

    pub fn expect_next_token(&mut self, token: Token) -> bool {
        self.next() == token
    }

    fn parse_let_statement(&mut self) -> Box<dyn Statement> {
        // Get identifier token
        let token = self.next();
        let identifer = match token {
            Token::Ident(s) => Identifier::new(Box::new(s)),
            _ => panic!("Identifier token not found in let statement {}", token)
        };

        // Check assignment token
        if self.expect_next_token(Token::Assign) == false {
            panic!("Assignment token not found in let statement")
        }

        self.next();

        // Parse expression
        let expr = self.parse_expression(Precedence::LOWEST);
        let let_stmt = LetStatement::new(identifer, expr);

        if self.peek() == Token::Semicolon {
            self.next();
        }

        let_stmt
    }

    fn parse_return_statement(&mut self) -> Box<dyn Statement> {
        let expr = self.parse_expression(Precedence::LOWEST);
        ReturnStatement::new(expr)
    }
    //
//    fn parse_if_statement(&self) -> Box<dyn Statement> {
//        Box::new()
//    }
//
    fn parse_identifier(&mut self) -> Box<dyn Expression> {
        let curr_token = &self.curr_token;

        match curr_token {
            Token::Ident(s) => Identifier::new(Box::new(s.clone())),
            _ => panic!("Unable to parse identifier {}", self.curr_token)
        }
    }

    fn parse_integer(&mut self) -> Box<dyn Expression> {
        let curr_token = &self.curr_token;

        match curr_token {
            Token::Int(s) => Integer::new( *s),
            _ => panic!("Unable to parse integer {}", self.curr_token)
        }
    }

    fn parse_expression(&mut self, precedence: Precedence) -> Box<dyn Expression> {

        let curr_token = &self.curr_token;

        // Prefix
        let mut left: Box<dyn Expression> = match curr_token {
            Token::Ident(s) => self.parse_identifier(),
            Token::Int(s) => self.parse_integer(),
            _ => panic!("Invalid token in expression {}", curr_token)
        };

        // Infix
        while self.peek() != Token::Semicolon  && self.peek_precedence() > precedence {
            let next_token = self.peek();
            left = match next_token {
                Token::Asterik| Token::Plus | Token::Minus => {
                    self.next();
                    let precedence = self.peek_precedence();
                    self.next();
                    let expr = InfixExpression::new(left, Box::new(next_token),
                                                    self.parse_expression(precedence));
                    expr
                },
                _ => left
            };
            self.next();
        }

        left
    }

    pub fn parse_program(&mut self) -> Result<Box<Program>, ParseError> {
        let mut program = Box::new(Program { statements: vec![] });

        while self.curr_token != Token::Eof {
            let statement = match self.curr_token {
                Token::Let => self.parse_let_statement(),
                Token::Return => self.parse_return_statement(),
                //    Token::If => self.parse_if_statement(),
                _ => panic!("Invalid token {}", self.curr_token)
            };
            program.statements.push(statement);
            self.next();
        }

        Ok(program)
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{Identifier, InfixExpression, LetStatement, AstNode, ReturnStatement};
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
        let mut idx = 0;
        for stmt in statements.iter() {
            assert_eq!(AstNode::LetStatement, stmt.ast_node_type());

            let let_stmt: &LetStatement = match stmt.as_any().downcast_ref::<LetStatement>() {
                Some(b) => b,
                None => panic!("Invalid type")
            };

            match idx {
                0 => assert_eq!(format!("{}", let_stmt), "let five = 5;"),
                1 => assert_eq!(format!("{}", let_stmt), "let ten = 10;"),
                2 => assert_eq!(format!("{}", let_stmt), "let twenty = 10 + 10;"),
                3 => assert_eq!(format!("{}", let_stmt), "let zero = 10 - 10;"),
                _ => panic!("Unexcepted index {}", idx)
            }

            idx += 1;
        }
    }

    const TEST_RETURN_STATEMENTS_STR: &str = "
        return 5;
        return 10 + 4;
    ";

    #[test]
    fn test_parser_return_statements() {
        let lexer = Lexer::new(TEST_RETURN_STATEMENTS_STR);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program().unwrap();
        let statements = program.statements;

        assert_eq!(statements.len(), 2);

        let mut idx = 0;
        for stmt in statements.iter() {
            assert_eq!(AstNode::ReturnStatement, stmt.ast_node_type());

            let ret_stmt: &ReturnStatement = match stmt.as_any().downcast_ref::<ReturnStatement>() {
                Some(b) => b,
                None => panic!("Invalid type")
            };

            match idx {
                0 => assert_eq!(format!("{}", ret_stmt), "return 5;"),
                1 => assert_eq!(format!("{}", ret_stmt), "return 10 + 4;"),
                _ => panic!("Unexcepted index {}", idx)
            }

            idx += 1;
        }
    }
}