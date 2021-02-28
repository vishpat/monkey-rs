use crate::lexer::{Lexer, Token};
use crate::ast::*;

#[cfg(not(test))]
use log::{info, warn};

#[cfg(test)]
use std::{println as trace, println as debug, println as info, println as warn};

use std::error::Error;
use std::fmt;
use std::fmt::{Debug, Display};
use std::collections::HashMap;
use crate::ast::AstNode::IdentifierExpression;

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd)]
enum Precedence {
    Lowest,
    Equals,
    LessGreater,
    Sum,
    Product,
    Prefix,
    Call,
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
        Box::new(Parser { lexer, curr_token, next_token })
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

    pub fn precedence(&self, token: &Token) -> Precedence {
        match token {
            Token::Eq => Precedence::Equals,
            Token::NotEq => Precedence::Equals,
            Token::Lt => Precedence::LessGreater,
            Token::Gt => Precedence::LessGreater,
            Token::Plus => Precedence::Sum,
            Token::Minus => Precedence::Sum,
            Token::Asterik => Precedence::Product,
            Token::Slash => Precedence::Product,
            Token::LParen => Precedence::Call,
            _ => Precedence::Lowest,
        }
    }

    pub fn curr_precedence(&self) -> Precedence {
        self.precedence(&self.curr_token)
    }

    pub fn peek_precedence(&self) -> Precedence {
        self.precedence(&self.next_token)
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
        let expr = self.parse_expression(Precedence::Lowest);
        let let_stmt = LetStatement::new(identifer, expr);

        if self.peek() == Token::Semicolon {
            self.next();
        }

        let_stmt
    }

    fn parse_return_statement(&mut self) -> Box<dyn Statement> {
        self.next();
        let expr = self.parse_expression(Precedence::Lowest);

        if self.peek() == Token::Semicolon {
            self.next();
        }

        ReturnStatement::new(expr)
    }

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
            Token::Int(s) => Integer::new(*s),
            _ => panic!("Unable to parse integer {}", self.curr_token)
        }
    }

    fn parse_boolean(&mut self) -> Box<dyn Expression> {
        let curr_token = &self.curr_token;

        match curr_token {
            Token::True => Boolean::new(true),
            Token::False => Boolean::new(false),
            _ => panic!("Invalid boolean {}", curr_token)
        }
    }

    fn parse_prefix_expression(&mut self) -> Box<dyn Expression> {
        let op = self.curr_token.clone();

        assert_eq!(op == Token::Bang || op == Token::Minus, true);

        self.next();
        PrefixExpression::new(Box::new(op),
                              self.parse_expression(Precedence::Prefix))
    }

    fn parse_group_expression(&mut self) -> Box<dyn Expression> {
        self.expect_next_token(Token::LParen);
        let expr = self.parse_expression(Precedence::Lowest);
        self.expect_next_token(Token::RParen);

        expr
    }

    fn parse_if_expression(&mut self) -> Box<dyn Expression> {

        self.expect_next_token(Token::If);
        self.expect_next_token(Token::LParen);
        let condition = self.parse_expression(Precedence::Lowest);
        self.expect_next_token(Token::RParen);
        let true_block = self.parse_block_statement();

        let mut false_block: Option<Box<BlockStatement>> = None;
        if self.peek() == Token::Else {
            self.next();
            false_block = Some(self.parse_block_statement());
        }

        IfExpression::new(condition, true_block, false_block)
    }

    fn parse_block_statement(&mut self) -> Box<BlockStatement> {
        let mut statements: Vec<Box<dyn Statement>> = vec![];

        self.expect_next_token(Token::LBrace);
        self.next();

        while self.curr_token != Token::Eof && self.curr_token != Token::RBrace {
            let statement = self.parse_statement();
            statements.push(statement);
            self.next();
        }

        self.expect_next_token(Token::RBrace);

        BlockStatement::new(Box::new(statements))
    }

    pub fn parse_expression_statement(&mut self) -> Box<dyn Statement> {
        let expr = self.parse_expression(Precedence::Lowest);
        if self.peek() == Token::Semicolon {
            self.next();
        }

        ExpressionStatement::new(expr)
    }

    ///
    ///  This function has been implemented using the TDOP algorithm mentioned
    /// [here](https://eli.thegreenplace.net/2010/01/02/top-down-operator-precedence-parsing)
    ///
    fn parse_expression(&mut self, precedence: Precedence) -> Box<dyn Expression> {
        let mut t = self.curr_token.clone();

        // Prefix
        let mut left: Box<dyn Expression> = match t {
            Token::Ident(s) => self.parse_identifier(),
            Token::Int(s) => self.parse_integer(),
            Token::True | Token::False => self.parse_boolean(),
            Token::Bang | Token::Minus => self.parse_prefix_expression(),
            Token::LParen => self.parse_group_expression(),
            Token::If => self.parse_if_expression(),
            Token::Function => unimplemented!(),
            _ => panic!("Invalid token in expression {}", t)
        };

        // Infix
        while self.peek() != Token::Semicolon && self.peek_precedence() > precedence {
            let token = self.next();

            left = match token {
                Token::Plus | Token::Minus | Token::Slash | Token::Asterik |
                Token::Eq | Token::NotEq | Token::Lt | Token::Gt => {
                    self.next();
                    InfixExpression::new(left, Box::new(token.clone()),
                                         self.parse_expression(self.precedence(&token))) }
                ,
                _ => left
            };
        }

        left
    }

    pub fn parse_statement(&mut self) -> Box<dyn Statement> {
        let statement = match self.curr_token {
            Token::Let => self.parse_let_statement(),
            Token::Return => self.parse_return_statement(),
            _ => self.parse_expression_statement(),
        };
        statement
    }

    pub fn parse_program(&mut self) -> Result<Box<Program>, ParseError> {
        let mut program = Box::new(Program { statements: vec![] });

        while self.curr_token != Token::Eof {
            let statement = self.parse_statement();
            program.statements.push(statement);
            self.next();
        }

        Ok(program)
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{Identifier, InfixExpression, LetStatement, AstNode, ReturnStatement, PrefixExpression, BlockStatement, ExpressionStatement, IfExpression};
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
        let twenty = 20 + 20;
        let zero = 30 - 40;
        let complex = 11 - 22 + 11 * 22;
    ";

    #[test]
    fn test_parser_let_statements() {
        let lexer = Lexer::new(TEST_LET_STATEMENTS_STR);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program().unwrap();
        let statements = program.statements;

        assert_eq!(statements.len(), 5);
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
                2 => assert_eq!(format!("{}", let_stmt), "let twenty = (20 + 20);"),
                3 => assert_eq!(format!("{}", let_stmt), "let zero = (30 - 40);"),
                4 => assert_eq!(format!("{}", let_stmt), "let complex = ((11 - 22) + (11 * 22));"),
                _ => panic!("Unexcepted index {}", idx)
            }

            idx += 1;
        }
    }

    const TEST_RETURN_STATEMENTS_STR: &str = "
        return 5;
        return 10 + 4 * 5;
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
                1 => assert_eq!(format!("{}", ret_stmt), "return (10 + (4 * 5));"),
                _ => panic!("Unexcepted index {}", idx)
            }

            idx += 1;
        }
    }


    const TEST_INTEGERS_STR: &str = "
        let x = 5;
        let y = 10;
    ";

    #[test]
    fn test_parser_integer_expressions() {
        let lexer = Lexer::new(TEST_INTEGERS_STR);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program().unwrap();
        let statements = program.statements;

        assert_eq!(statements.len(), 2);
        let mut idx = 0;
        for stmt in statements.iter() {
            assert_eq!(AstNode::LetStatement, stmt.ast_node_type());

            let let_stmt: &LetStatement = match stmt.as_any().downcast_ref::<LetStatement>() {
                Some(b) => {
                    assert_eq!(b.expr.ast_node_type(), AstNode::IntegerExpression);
                    b
                }
                None => panic!("Invalid type")
            };

            match idx {
                0 => {
                    assert_eq!(format!("{}", let_stmt.expr), "5")
                }
                1 => {
                    assert_eq!(format!("{}", let_stmt.expr), "10")
                }
                _ => panic!("Unexcepted index {}", idx)
            }

            idx += 1;
        }
    }

    const TEST_BOOLEAN_STR: &str = "
        let x = true;
        let y = false;
    ";

    #[test]
    fn test_parser_boolean_expressions() {
        let lexer = Lexer::new(TEST_BOOLEAN_STR);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program().unwrap();
        let statements = program.statements;

        assert_eq!(statements.len(), 2);
        let mut idx = 0;
        for stmt in statements.iter() {
            assert_eq!(AstNode::LetStatement, stmt.ast_node_type());

            let let_stmt: &LetStatement = match stmt.as_any().downcast_ref::<LetStatement>() {
                Some(b) => {
                    assert_eq!(b.expr.ast_node_type(), AstNode::BooleanExpression);
                    b
                }
                None => panic!("Invalid type, expected let statement")
            };

            match idx {
                0 => {
                    assert_eq!(format!("{}", let_stmt.expr), "true")
                }
                1 => {
                    assert_eq!(format!("{}", let_stmt.expr), "false")
                }
                _ => panic!("Unexcepted index {}", idx)
            }

            idx += 1;
        }
    }

    const TEST_PREFIX_STR: &str = "
        let x = !y;
        let x = -1;
    ";

    #[test]
    fn test_parser_prefix_expressions() {
        let lexer = Lexer::new(TEST_PREFIX_STR);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program().unwrap();
        let statements = program.statements;

        assert_eq!(statements.len(), 2);
        let mut idx = 0;
        for stmt in statements.iter() {
            assert_eq!(AstNode::LetStatement, stmt.ast_node_type());

            let let_stmt: &LetStatement = match stmt.as_any().downcast_ref::<LetStatement>() {
                Some(b) => {
                    assert_eq!(b.expr.ast_node_type(), AstNode::PrefixExpression);
                    b
                }
                None => panic!("Invalid type")
            };

            let prefix_expr: &PrefixExpression = match let_stmt.expr.as_any().downcast_ref::<PrefixExpression>() {
                Some(px) => {
                    px
                }
                None => panic!("Invalid type, expected prefix expression")
            };

            match idx {
                0 => {
                    assert_eq!(format!("{}", prefix_expr.op), "!");
                    assert_eq!(format!("{}", prefix_expr.expr), "y");
                }
                1 => {
                    assert_eq!(format!("{}", prefix_expr.op), "-");
                    assert_eq!(format!("{}", prefix_expr.expr), "1");
                }
                _ => panic!("Unexcepted index {}", idx)
            }

            idx += 1;
        }
    }

    const TEST_GROUPED_EXPRESSION_STR: &str = "
        let x = (x + y);
        let x = (x + y) + (l + k);
        let x = ((x * 2) + (3 * (2 + 3) + 2));
    ";

    #[test]
    fn test_parser_grouped_expressions() {
        let lexer = Lexer::new(TEST_GROUPED_EXPRESSION_STR);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program().unwrap();
        let statements = program.statements;

        assert_eq!(statements.len(), 3);
        let mut idx = 0;
        for stmt in statements.iter() {
            assert_eq!(AstNode::LetStatement, stmt.ast_node_type());

            let let_stmt: &LetStatement = match stmt.as_any().downcast_ref::<LetStatement>() {
                Some(b) => b,
                None => panic!("Invalid type")
            };

            match idx {
                0 => assert_eq!(format!("{}", let_stmt), "let x = (x + y);"),
                1 => assert_eq!(format!("{}", let_stmt), "let x = ((x + y) + (l + k));"),
                2 => assert_eq!(format!("{}", let_stmt), "let x = ((x * 2) + ((3 * (2 + 3)) + 2));"),
                _ => panic!("Unexcepted index {}", idx)
            }

            idx += 1;
        }
    }

    const TEST_IF_NO_ELSE_STR: &str = "
        if (x > 10) {
            let y = 10;
            let z = 30;
        }
    ";

    #[test]
    fn test_parser_if_no_else() {
        let lexer = Lexer::new(TEST_IF_NO_ELSE_STR);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program().unwrap();
        let statements = program.statements;

        assert_eq!(statements.len(), 1);
        let stmt = &statements[0];

        assert_eq!(AstNode::ExpressionStatement, stmt.ast_node_type());

        let expr_stmt: &ExpressionStatement = match stmt.as_any().downcast_ref::<ExpressionStatement>() {
            Some(b) => b,
            None => panic!("Invalid type, expected expression statement")
        };

        let expr = &expr_stmt.expr;
        assert_eq!(AstNode::IfExpression, expr.ast_node_type());

        let if_expr: &IfExpression = match expr.as_any().downcast_ref::<IfExpression>() {
            Some(x) => x,
            None => panic!("Expected if expression")
        };

        let cond = &if_expr.cond;
        assert_eq!(format!("{}", cond), "(x > 10)");

        let true_block = &if_expr.true_block;
        println!("{:?}",true_block);

        let blk_statements = &true_block.block;

        let statement1 = &blk_statements[0];
        assert_eq!(format!("{}", statement1), "let y = 10;");

        let statement2 = &blk_statements[1];
        assert_eq!(format!("{}", statement2), "let z = 30;");

        let false_block = &if_expr.false_block;
        assert_eq!(false_block.is_none(), true);
    }
}