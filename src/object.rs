use std::any::Any;
use crate::ast::{Node, AstNode, Integer, Boolean, Identifier, Program};
use crate::ast;

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd)]
pub enum ObjectType {
    Error,
    Integer,
    Boolean,
    Identifier,
    If,
    Let,
    Function,
    Call,
}

pub trait Object: std::fmt::Debug + std::fmt::Display {
    fn obj_type(&self) -> ObjectType;

    // Required to downcast a Trait to specify structure

    fn as_any(&self) -> &dyn Any;
}

impl Object for Integer {
    fn obj_type(&self) -> ObjectType {
        ObjectType::Integer
    }

    fn as_any(&self) -> &dyn Any { self }
}

impl Object for Boolean {
    fn obj_type(&self) -> ObjectType {
        ObjectType::Boolean
    }

    fn as_any(&self) -> &dyn Any { self }
}

#[derive(Debug)]
pub struct Error {
    msg: String
}

impl Error {
    pub fn new(msg: String) -> Box<Error> {
        Box::new(Error{msg})
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{}", self.msg)
    }
}

impl Object for Error {
    fn obj_type(&self) -> ObjectType {
        ObjectType::Error
    }

    fn as_any(&self) -> &dyn Any { self }
}