use crate::lexer::Token;
use std::fmt;
use std::fmt::Formatter;

#[derive(Debug, PartialEq, Clone)]
pub struct Program {
    pub stmts: Vec<Statement>,
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for stmt in &self.stmts {
            write!(f, "{}", stmt)?;
        }
        Ok(())
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct BlockStatement {
    pub stmts: Vec<Statement>,
}

impl fmt::Display for BlockStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{");
        for stmt in &self.stmts {
            write!(f, "{}", stmt)?;
        }
        write!(f, "}}");
        Ok(())
    }
}


#[derive(Debug, PartialEq, Clone)]
pub enum Prefix {
    Minus,
    Bang
}

impl fmt::Display for Prefix {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Prefix::Minus => write!(f, "-"),
            Prefix::Bang => write!(f, "!"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Infix {
    Eq,
    NotEq,
    Lt,
    Gt,
    Plus,
    Minus,
    Asterisk,
    Slash,
}

impl fmt::Display for Infix {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Infix::Eq => write!(f, "=="),
            Infix::NotEq => write!(f, "!="),
            Infix::Lt => write!(f, "<"),
            Infix::Gt => write!(f, ">"),
            Infix::Plus => write!(f, "+"),
            Infix::Minus => write!(f, "-"),
            Infix::Asterisk => write!(f, "*"),
            Infix::Slash => write!(f, "/"),
        }
    }
}


#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    Identifier(String),
    IntegerLiteral(i64),
    Boolean(bool),
    Prefix(Prefix, Box<Expression>),
    Infix(Infix, Box<Expression>, Box<Expression>),
    If(Box<Expression>, Box<BlockStatement>, Option<Box<BlockStatement>>),
    FunctionLiteral(Vec<String>, Box<BlockStatement>),
    Call(Box<Expression>, Vec<Expression>),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Identifier(s) => write!(f, "{}", s),
            Expression::IntegerLiteral(i) => write!(f, "{}", i),
            Expression::Boolean(b) => write!(f, "{}", b),
            Expression::Prefix(p, exp) => write!(f, "({}{})", p, exp),
            Expression::Infix(op, left, right) =>
                write!(f, "({} {} {})", left, op, right),
            Expression::If(exp, true_blk, Some(false_blk)) =>
                write!(f,"if ({}) {} else {}", exp, true_blk, false_blk),
            Expression::If(exp, true_blk, None) =>
                write!(f,"if ({}) {}", exp, true_blk),
            Expression::FunctionLiteral(params, block) => write!(f, "fn({}), {}", params.join(","), block),
            Expression::Call(exp, params) => write!(f, "{}({})", exp,
                                                    params.iter().map(|a| a.to_string()).collect::<Vec<String>>().join(",")),
        }
    }
}



#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    Let(String, Box<Expression>),
    Return(Option<Box<Expression>>),
            Expression(Box<Expression>),
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Let(s, exp) => write!(f, "let {} = {};", s, exp),
            Statement::Return(None) => write!(f, "return;"),
            Statement::Return(Some(val)) => write!(f, "return {};", val),
            Statement::Expression(exp) => write!(f, "{}", exp),
        }
    }
}
