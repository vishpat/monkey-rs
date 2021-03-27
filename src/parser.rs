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
    Index,
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
            Token::LBracket => Precedence::Index,
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

    fn parse_string(&mut self) -> Box<Expression> {
        let curr_token = &self.curr_token;

        match curr_token {
            Token::String(s) => Box::new(Expression::String(s.to_string())),
            _ => panic!("Unable to parse string {}", self.curr_token)
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
        self.next();

        let mut false_block: Option<Box<BlockStatement>> = None;
        if self.curr_token == Token::Else {
            false_block = Some(self.parse_block_statement());
            self.next();
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
            Token::String(s) => self.parse_string(),
            Token::True | Token::False => self.parse_boolean(),
            Token::Bang | Token::Minus => self.parse_prefix_expression(),
            Token::LParen => self.parse_group_expression(),
            Token::If => self.parse_if_expression(),
            Token::Function => self.parse_function(),
            Token::LBracket => self.parse_array_literal(),
            _ => panic!("Invalid token in expression {}, next token {}", t, self.next_token.clone())
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

    pub fn parse_array_literal(&mut self) -> Box<Expression> {

        let mut members: Vec<Expression> = vec![];

        self.expect_current_token(Token::LBracket);
        while self.curr_token != Token::RBracket {
            let member = self.parse_expression(Precedence::Lowest);
            members.push(*member);

            if self.peek() == Token::Comma {
                self.next();
            }

            self.next();
        }

        Box::new(Expression::ArrayLiteral(members))
    }

    pub fn parse_function_parameters(&mut self) -> Vec<String> {
        let mut parameters: Vec<String> = vec![];

        self.expect_current_token(Token::LParen);

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
    use crate::lexer::{Lexer, Token};
    use crate::parser::Parser;
    use std::any::Any;
    use crate::ast::{Statement, Prefix};
    use crate::ast::Expression;

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
    let x = \"x\";
    let y = \"y\";
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

    fn test_case_statements(input: &str) -> Vec<Statement> {
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program().unwrap();
        program.stmts
    }

    const TEST_LET_STATEMENTS_STR: &str = "
        let five = 5;
        let is_true = true;
        let t = ten;
        let twenty = 20 + 20;
        let zero = 30 - 30;
        let complex = 11 - 22 + 11 * 22;
        let x = \"abcd\";
        let arr = [1, \"abc\", 3];
    ";

    #[test]
    fn test_parser_let_statements() {
        let statements = test_case_statements(TEST_LET_STATEMENTS_STR);

        assert_eq!(statements.len(), 8);
        let mut idx = 0;
        for stmt in statements.iter() {
            let let_stmt = match stmt {
                Statement::Let(s, expr) => {
                    match idx {
                        0 => {
                            assert_eq!(stmt.to_string(), "let five = 5;");
                            match **expr {
                                Expression::IntegerLiteral(i) => assert_eq!(i, 5),
                                _ => panic!("Expected integer value of 5"),
                            }
                        },
                        1 => {
                            assert_eq!(stmt.to_string(), "let is_true = true;");
                            match **expr {
                                Expression::Boolean(b) => assert_eq!(b, true),
                                _ => panic!("Expected a true boolean value"),
                            }
                        },
                        2 => assert_eq!(stmt.to_string(), "let t = ten;"),
                        3 => assert_eq!(stmt.to_string(), "let twenty = (20 + 20);"),
                        4 => assert_eq!(stmt.to_string(), "let zero = (30 - 30);"),
                        5 => assert_eq!(stmt.to_string(), "let complex = ((11 - 22) + (11 * 22));"),
                        6 => assert_eq!(stmt.to_string(), "let x = \"abcd\";"),
                        7 => assert_eq!(stmt.to_string(), "let arr = [1,\"abc\",3];"),
                        _ => panic!("Unexcepted index {}", idx)
                    }
                },
                _ => panic!("Expected let statement but found {}", stmt),
            };

            idx += 1;
        }
    }

    const TEST_RETURN_STATEMENTS_STR: &str = "
        return;
        return 5;
        return 10 + 4 * 5;
    ";

    #[test]
    fn test_parser_return_statements() {
        let statements = test_case_statements(TEST_RETURN_STATEMENTS_STR);
        assert_eq!(statements.len(), 3);

        let mut idx = 0;
        for stmt in statements.iter() {
            let ret_stmt = match stmt {
                Statement::Return(expr) => {
                    match idx {
                        0 => {
                            assert_eq!(expr.is_none(), true);
                            assert_eq!(stmt.to_string(), "return;")
                        },
                        1 => assert_eq!(stmt.to_string(), "return 5;"),
                        2 => assert_eq!(stmt.to_string(), "return (10 + (4 * 5));"),
                       _ => panic!("Unexcepted index {}", idx)
                    }
                },
                _ => panic!("{}: Expected return statement but found {}", idx, stmt),
            };

            idx += 1;
        }

    }


    const TEST_PREFIX_STR: &str = "
        !y;
        -1;
    ";

    #[test]
    fn test_parser_prefix_expressions() {
        let statements = test_case_statements(TEST_PREFIX_STR);
        assert_eq!(statements.len(), 2);

        let mut idx = 0;
        for stmt in statements.iter() {
            let prefix_expr= match stmt {
                Statement::Expression(expr) => {
                    match &**expr {
                       Expression::Prefix(prefix, expr2) => match idx {
                            0 => {
                                assert_eq!(*prefix, Prefix::Bang);
                                assert_eq!(expr2.to_string(), "y");
                            },
                            1 => {
                                assert_eq!(*prefix, Prefix::Minus);
                                assert_eq!(expr2.to_string(), "1");
                            },
                            _ => panic!("Unexpected expression index {}", idx)
                        },
                        _ => panic!("Expected prefix expression"),
                    }
                },
                _ => panic!("Expected statement with prefix expression but found {}", stmt),
            };
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
            match stmt {
                Statement::Let(s, expr) => {
                    match idx {
                        0 => assert_eq!(format!("{}", stmt), "let x = (x + y);"),
                        1 => assert_eq!(format!("{}", stmt), "let x = ((x + y) + (l + k));"),
                        2 => assert_eq!(format!("{}", stmt), "let x = ((x * 2) + ((3 * (2 + 3)) + 2));"),
                        _ => panic!("Unexcepted index {}", idx)
                    }
                }
                _ => panic!("Expected let statement found {}")
            }

            idx += 1;
        }
    }

    const TEST_IF_NO_ELSE_STR: &str = "
        if (x > y) {
            let z = x + y;
        };
    ";

    #[test]
    fn test_parser_if_no_else() {
        let statements = test_case_statements(TEST_IF_NO_ELSE_STR);

        assert_eq!(statements.len(), 1);
        let mut stmt = &statements[0];
        match stmt {
            Statement::Expression(expr) => {
                match &**expr {
                    Expression::If(cond, true_block, false_block) => {
                        assert_eq!(cond.to_string(), "(x > y)");
                        assert_eq!(true_block.to_string(), "{let z = (x + y);}");
                        assert_eq!(false_block.is_none(), true);
                    }
                    _ => panic!("Expected if expression")
                }
            }
            _ => panic!("Unexpected expression found")
        }
    }

    const TEST_IF_ELSE_STR: &str = "
        if (x > y) {
            x*2 + 3;
            let x = y;
        } else {
            4 + 5*y;
            x + y;
        }
    ";

    #[test]
    fn test_parser_if_else() {
        let statements = test_case_statements(TEST_IF_ELSE_STR);
        assert_eq!(statements.len(), 1);

        let mut stmt = &statements[0];
        match stmt {
            Statement::Expression(expr) => {
                match &**expr {
                    Expression::If(cond, true_block, false_block) => {
                        assert_eq!(cond.to_string(), "(x > y)");
                        assert_eq!(true_block.to_string(), "{((x * 2) + 3);let x = y;}");
                        assert_eq!(false_block.as_ref().unwrap().to_string(), "{(4 + (5 * y));(x + y);}");
                    }
                    _ => panic!("Expected if expression")
                }
            }
            _ => panic!("Unexpected expression found")
        }
    }

    const TEST_FUNCTION_STR1: &str = "
        fn(x,y,z) {
            let z = x + y;
            z
        };
        let fact = fn(x){
                        if (x > 1) {
                            return x;
                        } else {
                            return 1;
                        };
                    };
    ";

    #[test]
    fn test_parser_function() {
        let statements = test_case_statements(TEST_FUNCTION_STR1);
        assert_eq!(statements.len(), 2);
        let mut stmt = &statements[0];
        match stmt {
            Statement::Expression(expr) => {
                match &**expr {
                    Expression::FunctionLiteral(params, block) => {
                        assert_eq!(params.iter().as_ref().join(","), "x,y,z");
                        assert_eq!(block.stmts[0].to_string(), "let z = (x + y);");
                        assert_eq!(block.stmts[1].to_string(), "z;");
                    }
                    _ => panic!("Expected function literal")
                }
            }
            _ => panic!("Unexpected expression found")
        }
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
        match stmt {
            Statement::Expression(expr) => {
                match &**expr {
                    Expression::FunctionLiteral(params, block) => {
                        assert_eq!(params.len(), 0);
                        assert_eq!(block.stmts[0].to_string(), "(10 * 20);");
                    }
                    _ => panic!("Expected function literal")
                }
            }
            _ => panic!("Unexpected expression found")
        }
    }

    const TEST_FUNCTION_STR3: &str = "
        fn(x, y) {
            x*y;
        }(10, 20);
    ";

    #[test]
    fn test_parser_function_expression() {
        let statements = test_case_statements(TEST_FUNCTION_STR3);
        assert_eq!(statements.len(), 1);
        let mut stmt = &statements[0];
        match stmt {
            Statement::Expression(expr) => {
                println!("{}", expr);
            }
            _ => panic!("Unexpected expression found")
        }
    }

    const TEST_FUNCTION_CALL_STR: &str = "
        sum();
        sum3(x, y, z);
        sum_expr(x, y + w, z);
        fn(x, y){x + y;}(2, 3);
    ";

    #[test]
    fn test_parser_call_with_parameters() {
        let statements = test_case_statements(TEST_FUNCTION_CALL_STR);
        assert_eq!(statements.len(), 4);

        let mut idx = 0;
        for idx in 0..statements.len() {
            match &statements[idx] {
                Statement::Expression(expr) => {
                    match &**expr {
                        Expression::Call(func_expr, params) => {
                            match idx {
                                0 => {
                                    assert_eq!(func_expr.to_string(), "sum");
                                    assert_eq!(params.len(), 0);
                                },
                                1 => {
                                    assert_eq!(func_expr.to_string(), "sum3");
                                    assert_eq!(params.iter().map(|p| p.to_string()).collect::<Vec<String>>().join(","), "x,y,z");
                                },
                                2 => {
                                    assert_eq!(func_expr.to_string(), "sum_expr");
                                    assert_eq!(params.iter().map(|p| p.to_string()).collect::<Vec<String>>().join(","),
                                               "x,(y + w),z");
                                },
                                3 => {
                                    assert_eq!(func_expr.to_string(), "fn(x,y){(x + y);}");
                                    assert_eq!(params.iter().map(|p| p.to_string()).collect::<Vec<String>>().join(","),
                                               "2,3");
                                }
                                _ => panic!("Unexpected idx {}", idx),
                            }


                        },
                        _ => panic!("Expected call expression")
                    }
                },
                _ => panic!("Expected a expression statement"),
            }
        }

    }

    const TEST_STRINGS_STR: &str = "
        \"abcd\";
    ";

    #[test]
    fn test_parser_string_statements() {
        let statements = test_case_statements(TEST_STRINGS_STR);

        assert_eq!(statements.len(), 1);
        let mut idx = 0;
        for stmt in statements.iter() {
            match stmt {
                Statement::Expression(expr) => {
                    match &**expr {
                        Expression::String(s) => println!("{}", s.to_string()),
                        _ => panic!("Expected string literal in expression found {}", expr)
                    }
                },
                _ => panic!("Expected a string expression"),
            }
            idx += 1;
        }
    }
}