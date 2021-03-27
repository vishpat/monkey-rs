use std;
use crate::ast::BlockStatement;
use crate::environment::Environment;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug, PartialEq, Clone)]
pub enum Object {
    Error(String),
    Nil,
    Integer(i64),
    Boolean(bool),
    String(String),
    Identifier(String),
    FunctionInBuilt(String),
    Array(Vec<Object>),
    FunctionLiteral(Vec<String>, BlockStatement, Rc<RefCell<Environment>>),
}

impl std::fmt::Display for Object {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Object::Error(e) => write!(fmt, "{}", e),
            Object::Nil => write!(fmt, "nil"),
            Object::Integer(i) => write!(fmt, "{}", i),
            Object::Boolean(b) => write!(fmt, "{}", b),
            Object::Identifier(s) => write!(fmt, "{}", s),
            Object::String(s) => write!(fmt, "\"{}\"", s),
            Object::Array(arr) =>  write!(fmt, "[{}]", arr.iter().map(|a| a.to_string()).collect::<Vec<String>>().join(",")),
            Object::FunctionLiteral(parameters, block, _) => write!(fmt, "({}){{ {} }}",
                                                                    parameters.join(","), block.to_string()),
            _ => panic!("Invalid object {}", self),
        }
    }
}