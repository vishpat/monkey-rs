use std;
use crate::ast::BlockStatement;
use crate::environment::Environment;
use std::cell::RefCell;
use std::rc::Rc;
use std::collections::{HashMap, BTreeMap};
use std::hash::{Hash, Hasher};

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
    Dict(HashMap<Object, Object>),
    FunctionLiteral(Vec<String>, BlockStatement, Rc<RefCell<Environment>>),
}

impl Eq for Object {}

impl Hash for Object {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Object::String(s) => s.hash(state),
            Object::Integer(i) => i.hash(state),
            _ => panic!("Invalid dict key {}, supported types are string and integer", self)
        }
    }
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
            Object::Dict(dict) => {
                let mut str = String::new();
                str.push_str("{");
                for (k, v) in dict {
                    str.push_str(format!("{}:{},", k, v).as_str());
                }

                if str.ends_with(',') {
                    str.pop();
                }
                str.push_str("}");
                write!(fmt, "{}", str)
            },
            Object::FunctionLiteral(parameters, block, _) => write!(fmt, "({}){{ {} }}",
                                                                    parameters.join(","), block.to_string()),
            _ => panic!("Invalid object {}", self),
        }
    }
}