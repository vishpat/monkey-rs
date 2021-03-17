use std;
use crate::ast::BlockStatement;

#[derive(Debug, PartialEq, Clone)]
pub enum Object {
    Error(String),
    Nil,
    Integer(i64),
    Boolean(bool),
    Identifier(String),
    FunctionLiteral(Vec<String>, BlockStatement)
}

impl std::fmt::Display for Object {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Object::Error(e) => write!(fmt, "{}", e),
            Object::Nil => write!(fmt, "nil"),
            Object::Integer(i) => write!(fmt, "{}", i),
            Object::Boolean(b) => write!(fmt, "{}", b),
            Object::Identifier(s) => write!(fmt, "{}", s),
            Object::FunctionLiteral(parameters, block) => write!(fmt,"({}){{ {} }}",
            parameters.join(","), block.to_string()),
            _ => panic!("Invalid object {}", self),
        }
    }
}