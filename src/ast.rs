use crate::lexer::Token;
use std::fmt;
use std::fmt::Formatter;

#[derive(Debug, PartialEq, Clone)]
pub struct Program {
    pub stmts: Vec<Statement>,
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for stmt in &self.statements {
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
        for stmt in &self.statements {
            write!(f, "{}", stmt)?;
        }
        write!(f, "}}");
        Ok(())
    }
}


#[derive(Debug, PartialEq, Clone)]
pub enum Prefix {
    Plus,
    Bang
}

impl fmt::Display for Prefix {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Prefix::Plus => write!(f, "+"),
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
    StringLiteral(String),
    Boolean(bool),
    Prefix(Prefix, Box<Expression>),
    Infix(Infix, Box<Expression>, Box<Expression>),
    If(Box<Expression>, BlockStatement, Option<BlockStatement>),
    FunctionLiteral(Vec<String>, BlockStatement),
    Call(Box<Expression>, Vec<Expression>),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Identifier(s) => write!(f, "{}", s),
            Expression::IntegerLiteral(i) => write!(f, "{}", i),
            Expression::StringLiteral(s) => write!(f, "{}", s),
            Expression::Boolean(b) => write!(f, "{}", b),
            Expression::Prefix(p, exp) => write!(f, "{}{}", p, exp),
            Expression::Infix(op, left, right) =>
                write!(f, "{} {} {}", left, op, right),
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
    Let(String, Expression),
    Return(Option<Expression>),
    Expression(Expression),
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

#[cfg(test)]
mod tests {
    use crate::ast::{Identifier, InfixExpression, LetStatement, Node, AstNode};
    use crate::lexer::Token;

    #[test]
    fn test_infix_expression() {
        let x =
            Box::new(Identifier { value: Box::new(String::from("x")) });
        assert_eq!(x.ast_node_type(), AstNode::IdentifierExpression);

        let y =
            Box::new(Identifier { value: Box::new(String::from("y")) });
        assert_eq!(y.ast_node_type(), AstNode::IdentifierExpression);

        let z =
            Box::new(Identifier { value: Box::new(String::from("z")) });
        assert_eq!(z.ast_node_type(), AstNode::IdentifierExpression);

        let infix_expr = Box::new(InfixExpression { left: x, op: Box::new(Token::Plus), right: y });
        assert_eq!(infix_expr.ast_node_type(), AstNode::InfixExpression);

        let let_expr = Box::new(LetStatement { id: z, expr: infix_expr });
        assert_eq!(let_expr.ast_node_type(), AstNode::LetStatement);

        let let_expr_str = format!("{}", let_expr);
        assert_eq!("let z = (x + y);", let_expr_str);
    }
}