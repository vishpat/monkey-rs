use crate::lexer::Token;
use std::ptr::write_bytes;
use std::any::Any;
use proc_macro::Ident;

#[derive(Debug, PartialEq, Clone)]
pub enum Prefix {
    Plus,
    Bang
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

#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    Let(Expression, Expression),
    Return(Option<Expression>),
    Expression(Expression),
    Block(Vec<Statement>),
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