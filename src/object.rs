use std::any::Any;
use crate::ast::{Node, AstNode, Integer, Boolean, Identifier, Program, BlockStatement, FunctionLiteral};
use crate::ast;
use std::collections::HashMap;
use crate::lexer::Token::Int;

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd)]
pub enum ObjectType {
    Error,
    Nil,
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

#[derive(Debug)]
pub struct Nil {
}

impl Nil {
    pub fn new() -> Box<Nil> {
        Box::new(Nil{})
    }
}

impl std::fmt::Display for Nil {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "Nil")
    }
}

impl Object for Nil {
    fn obj_type(&self) -> ObjectType {
        ObjectType::Nil
    }

    fn as_any(&self) -> &dyn Any { self }
}

#[derive(Debug)]
pub struct Function {
    params: Box<Vec<Box<Identifier>>>,
    block: Box<BlockStatement>,
    env: Box<Environment>
}

impl Function {
    pub fn new(params: Box<Vec<Box<Identifier>>>,
                   block: Box<BlockStatement>,
                   env: Box<Environment>) -> Box<Function> {
        Box::new(Function{params, block, env})
    }
}

impl Object for Function {
    fn obj_type(&self) -> ObjectType {
        ObjectType::Function
    }

    fn as_any(&self) -> &dyn Any { self }
}

impl std::fmt::Display for Function {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{:?} {:?}", self.func, self.env)
    }
}

#[derive(Debug)]
pub struct Environment {
    data: HashMap<String, Box<dyn Object>>,
    parent: Option<Box<Environment>>
}

impl Environment {
    pub fn new(parent: Option<Box<Environment>>) -> Box<Environment> {
        Box::new(Environment{data: HashMap::new(), parent })
    }

    pub fn put(&mut self, k: String, v: Box<dyn Object>) {
        self.data.insert(k, v);
    }

    pub fn get(&self, k:String) -> Option<Box<dyn Object>> {
        let val = self.data.get(&k);
        if val.is_some() {
            let val2 = val.unwrap();
            let val3: Option<Box<dyn Object>> = match val2.obj_type() {
                ObjectType::Integer => Some(Integer::new(val2.as_any().downcast_ref::<Integer>().unwrap().value)),
                ObjectType::Boolean => Some(Boolean::new(val2.as_any().downcast_ref::<Boolean>().unwrap().value)),
                _ => None
            };
            return val3;
        } else if self.parent.is_some() {
           return self.parent.as_ref().unwrap().get(k);
        }

        None
    }
}