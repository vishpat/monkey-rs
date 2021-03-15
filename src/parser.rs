use crate::lexer::{Lexer, Token};
use crate::ast::*;
use std::error::Error;
use std::fmt;
use std::fmt::{Debug, Display};

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd)]
pub enum Precedence {
    Lowest,
    Equals,
    LessGreater,
    Sum,
    Product,
    Prefix,
    Call,
}

#[derive(Debug)]
pub struct ParseError {
    token: Token,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Problem parsing near token {}", self.token)
    }
}

pub(crate) struct Parser {
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

    pub fn expect_current_token(&mut self, token: Token) {
        if self.curr_token == token {
            self.next();
        } else {
            panic!("Did not find expected current token {}, found {}", token, self.curr_token);
        }
    }

    pub fn expect_next_token(&mut self, token: Token) {
        if self.peek() == token {
            self.next();
        } else {
            panic!("Did not find expected next token {}, found {}", token, self.peek());
        }
    }

    fn parse_let_statement(&mut self) -> Box<Statement> {
        // Get identifier token
        let token = self.next();
        let identifer = match token {
            Token::Ident(s) => Expression::Identifier(s),
            _ => panic!("Identifier token not found in let statement {}", token)
        };

        // Check assignment token
        self.expect_next_token(Token::Assign);
        self.next();

        // Parse expression
        let expr = self.parse_expression(Precedence::Lowest);
        let let_stmt = Statement::Let(identifer.to_string(), expr);

        if self.peek() == Token::Semicolon {
            self.next();
        }

        Box::new(let_stmt)
    }

    fn parse_return_statement(&mut self) -> Box<Statement> {
        self.next();

        if self.curr_token == Token::Semicolon {
            self.next();
            return Box::new(Statement::Return(None))
        }

        let expr = self.parse_expression(Precedence::Lowest);

        if self.peek() == Token::Semicolon {
            self.next();
        }

        Box::new(Statement::Return(Some(expr)))
    }

    fn parse_identifier(&mut self) -> Box<Expression> {
        let curr_token = &self.curr_token;

        match curr_token {
            Token::Ident(s) => Box::new(Expression::Identifier(s.to_string())),
            _ => panic!("Unable to parse identifier {}", self.curr_token)
        }
    }

    fn parse_integer(&mut self) -> Box<Expression> {
        let curr_token = &self.curr_token;

        match curr_token {
            Token::Int(s) => Box::new(Expression::IntegerLiteral(*s)),
            _ => panic!("Unable to parse integer {}", self.curr_token)
        }
    }

    fn parse_boolean(&mut self) -> Box<Expression> {
        let curr_token = &self.curr_token;

        match curr_token {
            Token::True => Box::new(Expression::Boolean(true)),
            Token::False => Box::new(Expression::Boolean(false)),
            _ => panic!("Invalid boolean {}", curr_token)
        }
    }

    fn parse_prefix_expression(&mut self) -> Box<Expression> {
        let op = self.curr_token.clone();

        let prefix = match op {
            Token::Bang => Prefix::Bang,
            Token::Minus => Prefix::Minus,
            _ => panic!("Invalid token {} prefix expression", op)
        };

        self.next();
        Box::new(Expression::Prefix(prefix, self.parse_expression(Precedence::Prefix)))
    }

    fn parse_group_expression(&mut self) -> Box<Expression> {
        self.expect_current_token(Token::LParen);
        let expr = self.parse_expression(Precedence::Lowest);
        self.expect_next_token(Token::RParen);

        expr
    }

    fn parse_if_expression(&mut self) -> Box<Expression> {
        self.expect_current_token(Token::If);
        let condition = self.parse_group_expression();
        let true_block = self.parse_block_statement();

        let mut false_block: Option<Box<BlockStatement>> = None;
        if self.curr_token == Token::Else {
            false_block = Some(self.parse_block_statement());
        }

       Box::new(Expression::If(condition, true_block, false_block))
    }

    fn parse_block_statement(&mut self) -> Box<BlockStatement> {
        let mut statements: Vec<Statement> = vec![];

        self.expect_next_token(Token::LBrace);
        self.next();

        while self.curr_token != Token::Eof && self.curr_token != Token::RBrace {
            let statement = self.parse_statement();
            statements.push(*statement);
            self.next();
        }

        self.expect_current_token(Token::RBrace);

        Box::new(BlockStatement{stmts: statements})
    }

    pub fn parse_expression_statement(&mut self) -> Box<Statement> {
        let expr = self.parse_expression(Precedence::Lowest);
        if self.peek() == Token::Semicolon {
            self.next();
        }

        Box::new(Statement::Expression(expr))
    }

    ///
    ///  This function has been implemented using the TDOP algorithm mentioned
    /// [here](https://eli.thegreenplace.net/2010/01/02/top-down-operator-precedence-parsing)
    ///
    fn parse_expression(&mut self, precedence: Precedence) -> Box<Expression> {
        let mut t = self.curr_token.clone();
        // Prefix
        let mut expr: Box<Expression> = match t {
            Token::Ident(s) => self.parse_identifier(),
            Token::Int(s) => self.parse_integer(),
            Token::True | Token::False => self.parse_boolean(),
            Token::Bang | Token::Minus => self.parse_prefix_expression(),
            Token::LParen => self.parse_group_expression(),
            Token::If => self.parse_if_expression(),
            Token::Function => self.parse_function(),
            _ => panic!("Invalid token in expression {}", t)
        };

        // Infix
        while self.peek() != Token::Semicolon && self.peek_precedence() > precedence {
            let token = self.next();

            expr = match token {
                Token::Plus | Token::Minus | Token::Slash | Token::Asterik |
                Token::Eq | Token::NotEq | Token::Lt | Token::Gt => {
                    self.next();
                    let infix = match token {
                        Token::Plus => Infix::Plus,
                        Token::Minus => Infix::Minus,
                        Token::Slash => Infix::Slash,
                        Token::Asterik => Infix::Asterisk,
                        Token::Eq => Infix::Eq,
                        Token::NotEq => Infix::NotEq,
                        Token::Lt => Infix::Lt,
                        Token::Gt => Infix::Gt,
                        _ => panic!("Invalid infix token {}", token),
                    };

                    Box::new(Expression::Infix(infix, expr,
                                         self.parse_expression(self.precedence(&token))))
                }
                Token::LParen => {
                    self.parse_function_call(expr)
                }
                _ => expr
            };
        }

        expr
    }

    pub fn parse_call_parameters(&mut self) -> Vec<Expression> {
        let mut parameters: Vec<Expression> = vec![];
        self.expect_current_token(Token::LParen);

        if self.peek() == Token::RParen {
            self.next();
            self.next();
            return parameters;
        }

        while self.curr_token != Token::RParen {
            let expr = self.parse_expression(Precedence::Lowest);
            parameters.push(*expr);

            if self.peek() == Token::Comma {
                self.next();
            }

            self.next();
        }

        parameters
    }

    pub fn parse_function_call(&mut self, left: Box<Expression>) -> Box<Expression> {
        let parameters = self.parse_call_parameters();
        Box::new(Expression::Call(left, parameters))
    }

    pub fn parse_function_parameters(&mut self) -> Vec<String> {
        let mut parameters: Vec<String> = vec![];

        self.expect_current_token(Token::LParen);

        if self.peek() == Token::RParen {
            self.next();
            self.next();
            return parameters;
        }

        while self.curr_token != Token::RParen {
            let idf = &self.curr_token;

            let identifier = match idf {
                Token::Ident(i) => i.to_string(),
                _ => panic!("Unexpected function parameter {}", idf)
            };
            parameters.push(identifier);

            if self.peek() == Token::Comma {
                self.next();
            }

            self.next();
        }

        parameters
    }

    pub fn parse_function(&mut self) -> Box<Expression> {
        self.expect_current_token(Token::Function);

        let parameters = self.parse_function_parameters();
        let body = self.parse_block_statement();

        Box::new(Expression::FunctionLiteral(parameters, body))
    }

    pub fn parse_statement(&mut self) -> Box<Statement> {
        let statement = match self.curr_token {
            Token::Let => self.parse_let_statement(),
            Token::Return => self.parse_return_statement(),
            _ => self.parse_expression_statement(),
        };
        statement
    }

    pub fn parse_program(&mut self) -> Result<Box<Program>, ParseError> {
        let mut program = Box::new(Program { stmts: vec![] });

        while self.curr_token != Token::Eof {
            let statement = self.parse_statement();
            program.stmts.push(*statement);
            self.next();
        }

        Ok(program)
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{Identifier, InfixExpression, LetStatement, AstNode, ReturnStatement, PrefixExpression, BlockStatement, ExpressionStatement, IfExpression, FunctionLiteral, Statement, CallExpression};
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

    fn test_case_statements(input: &str) -> Vec<Box<dyn Statement>> {
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program().unwrap();
        program.statements
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
        let statements = test_case_statements(TEST_LET_STATEMENTS_STR);

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
        let statements = test_case_statements(TEST_RETURN_STATEMENTS_STR);
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
        let statements = test_case_statements(TEST_INTEGERS_STR);

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
        let statements = test_case_statements(TEST_BOOLEAN_STR);

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
        let statements = test_case_statements(TEST_PREFIX_STR);
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
        let statements = test_case_statements(TEST_GROUPED_EXPRESSION_STR);
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
        if (x > y) {
            x
        }
    ";

    #[test]
    fn test_parser_if_no_else() {
        let statements = test_case_statements(TEST_IF_NO_ELSE_STR);

        assert_eq!(statements.len(), 1);
        let mut stmt = &statements[0];

        assert_eq!(AstNode::ExpressionStatement, stmt.ast_node_type());

        let mut expr_stmt: &ExpressionStatement = match stmt.as_any().downcast_ref::<ExpressionStatement>() {
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
        assert_eq!(format!("{}", cond), "(x > y)");

        let true_block = &if_expr.true_block;

        stmt = &true_block.block[0];
        assert_eq!(AstNode::ExpressionStatement, stmt.ast_node_type());

        let expr_stmt2: &ExpressionStatement = match stmt.as_any().downcast_ref::<ExpressionStatement>() {
            Some(b) => b,
            None => panic!("Invalid type, expected expression statement")
        };

        assert_eq!(format!("{}", expr_stmt2.expr), "x");
    }

    const TEST_IF_ELSE_STR: &str = "
        if (x > y) {
            x*2 + 3
        } else {
            4 + 5*y
        }
    ";

    #[test]
    fn test_parser_if_else() {
        let statements = test_case_statements(TEST_IF_ELSE_STR);
        assert_eq!(statements.len(), 1);
        let mut stmt = &statements[0];

        assert_eq!(AstNode::ExpressionStatement, stmt.ast_node_type());

        let mut expr_stmt: &ExpressionStatement = match stmt.as_any().downcast_ref::<ExpressionStatement>() {
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
        assert_eq!(format!("{}", cond), "(x > y)");

        let true_block = &if_expr.true_block;

        stmt = &true_block.block[0];
        assert_eq!(AstNode::ExpressionStatement, stmt.ast_node_type());

        let expr_stmt2: &ExpressionStatement = match stmt.as_any().downcast_ref::<ExpressionStatement>() {
            Some(b) => b,
            None => panic!("Invalid type, expected expression statement")
        };

        assert_eq!(format!("{}", expr_stmt2.expr), "((x * 2) + 3)");

        let false_block = &if_expr.false_block.as_ref().unwrap();
        stmt = &false_block.block[0];
        assert_eq!(AstNode::ExpressionStatement, stmt.ast_node_type());

        let expr_stmt3: &ExpressionStatement = match stmt.as_any().downcast_ref::<ExpressionStatement>() {
            Some(b) => b,
            None => panic!("Invalid type, expected expression statement")
        };
        assert_eq!(format!("{}", expr_stmt3.expr), "(4 + (5 * y))");
    }

    const TEST_FUNCTION_STR1: &str = "
        fn(x,y) {
            x + y;
        }
    ";

    #[test]
    fn test_parser_function() {
        let statements = test_case_statements(TEST_FUNCTION_STR1);
        assert_eq!(statements.len(), 1);
        let mut stmt = &statements[0];

        assert_eq!(AstNode::ExpressionStatement, stmt.ast_node_type());

        let mut expr_stmt: &ExpressionStatement = match stmt.as_any().downcast_ref::<ExpressionStatement>() {
            Some(b) => b,
            None => panic!("Invalid type, expected expression statement")
        };

        let expr = &expr_stmt.expr;
        assert_eq!(AstNode::FunctionLiteralExpression, expr.ast_node_type());
        let mut func_literal: &FunctionLiteral = match expr.as_any().downcast_ref::<FunctionLiteral>() {
            Some(b) => b,
            None => panic!("Invalid type, expected expression statement")
        };

        let parameters = &func_literal.parameters;

        let param1 = &parameters[0];
        assert_eq!(param1.value, Box::new(String::from("x")));

        let param2 = &parameters[1];
        assert_eq!(param2.value, Box::new(String::from("y")));

        let stmt = &func_literal.block.block[0];
        assert_eq!(AstNode::ExpressionStatement, stmt.ast_node_type());

        let expr_stmt2: &ExpressionStatement = match stmt.as_any().downcast_ref::<ExpressionStatement>() {
            Some(b) => b,
            None => panic!("Invalid type, expected expression statement")
        };

        assert_eq!(format!("{}", expr_stmt2.expr), "(x + y)");
    }

    const TEST_FUNCTION_STR2: &str = "
        fn() {
            10*20;
        }
    ";

    #[test]
    fn test_parser_function_no_parameters() {
        let statements = test_case_statements(TEST_FUNCTION_STR2);
        assert_eq!(statements.len(), 1);
        let mut stmt = &statements[0];

        assert_eq!(AstNode::ExpressionStatement, stmt.ast_node_type());

        let mut expr_stmt: &ExpressionStatement = match stmt.as_any().downcast_ref::<ExpressionStatement>() {
            Some(b) => b,
            None => panic!("Invalid type, expected expression statement")
        };

        let expr = &expr_stmt.expr;
        assert_eq!(AstNode::FunctionLiteralExpression, expr.ast_node_type());
        let mut func_literal: &FunctionLiteral = match expr.as_any().downcast_ref::<FunctionLiteral>() {
            Some(b) => b,
            None => panic!("Invalid type, expected expression statement")
        };

        let parameters = &func_literal.parameters;
        assert_eq!(parameters.len(), 0);

        let stmt = &func_literal.block.block[0];
        assert_eq!(AstNode::ExpressionStatement, stmt.ast_node_type());

        let expr_stmt2: &ExpressionStatement = match stmt.as_any().downcast_ref::<ExpressionStatement>() {
            Some(b) => b,
            None => panic!("Invalid type, expected expression statement")
        };

        assert_eq!(format!("{}", expr_stmt2.expr), "(10 * 20)");
    }

    const TEST_FUNCTION_CALL_STR: &str = "
        sum();
        sum3(x, y, z);
        sum_expr(x, y + w, z);
        fn(x, y){x + y;};(2, 3);
    ";

    #[test]
    fn test_parser_call_with_parameters() {
        let statements = test_case_statements(TEST_FUNCTION_CALL_STR);

        // sum()
        let expr_stmt: &ExpressionStatement = match statements[0].as_any().downcast_ref::<ExpressionStatement>() {
            Some(e) => e,
            None => panic!("Invalid expression statement {}", statements[0])
        };

        let call_expr = match expr_stmt.expr.as_any().downcast_ref::<CallExpression>() {
            Some(c) => c,
            None => panic!("Invalid call expression {}", expr_stmt.expr)
        };

        assert_eq!(call_expr.function.to_string(), "sum");
        assert_eq!(call_expr.parameters.len(), 0);

        // sum(x, y, z)
        let expr_stmt2: &ExpressionStatement = match statements[1].as_any().downcast_ref::<ExpressionStatement>() {
            Some(e) => e,
            None => panic!("Invalid expression statement {}", statements[1])
        };

        let call_expr2 = match expr_stmt2.expr.as_any().downcast_ref::<CallExpression>() {
            Some(c) => c,
            None => panic!("Invalid call expression {}", expr_stmt2.expr)
        };

        assert_eq!(call_expr2.function.to_string(), "sum3");
        assert_eq!(call_expr2.parameters.len(), 3);

        let param1 = &call_expr2.parameters[0];
        let param1_id = match param1.as_any().downcast_ref::<Identifier>() {
            Some(i) => i,
            None => panic!("Invalid param {}", param1)
        };
        assert_eq!(param1_id.value, Box::new("x".to_string()));

        let param2 = &call_expr2.parameters[1];
        let param2_id = match param2.as_any().downcast_ref::<Identifier>() {
            Some(i) => i,
            None => panic!("Invalid param {}", param2)
        };
        assert_eq!(param2_id.value, Box::new("y".to_string()));

        let param3 = &call_expr2.parameters[2];
        let param3_id = match param3.as_any().downcast_ref::<Identifier>() {
            Some(i) => i,
            None => panic!("Invalid param {}", param3)
        };
        assert_eq!(param3_id.value, Box::new("z".to_string()));

        // sum_expr(x, y + w, z);
        let expr_stmt3: &ExpressionStatement = match statements[2].as_any().downcast_ref::<ExpressionStatement>() {
            Some(e) => e,
            None => panic!("Invalid expression statement {}", statements[2])
        };

        let call_expr3 = match expr_stmt3.expr.as_any().downcast_ref::<CallExpression>() {
            Some(c) => c,
            None => panic!("Invalid call expression {}", expr_stmt3.expr)
        };

        assert_eq!(call_expr3.function.to_string(), "sum_expr");
        assert_eq!(call_expr3.parameters.len(), 3);

        // fn(x, y){x + y;}(2, 3);
        let expr_stmt4: &ExpressionStatement = match statements[3].as_any().downcast_ref::<ExpressionStatement>() {
            Some(e) => e,
            None => panic!("Invalid expression statement {}", statements[2])
        };

        let call_expr4 = match expr_stmt4.expr.as_any().downcast_ref::<CallExpression>() {
            Some(c) => c,
            None => panic!("Invalid call expression {}", expr_stmt3.expr)
        };

        assert_eq!(call_expr4.function.ast_node_type(), AstNode::FunctionLiteralExpression);
        assert_eq!(call_expr4.parameters.len(), 2);
    }
}