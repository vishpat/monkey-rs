use std::any::Any;
use crate::object::{Object, ObjectType, Error};
use crate::ast::{Node, AstNode, Integer, Boolean, Identifier, Program, ExpressionStatement, Expression};
use std::borrow::Borrow;
use std::ops::Deref;

pub fn eval(node: &dyn Node) -> Box<dyn Object> {

    println!("Evaluating {:?}", node);

    match node.ast_node_type() {
        AstNode::ExpressionStatement => {
            match node.as_any().downcast_ref::<ExpressionStatement>() {
                Some(es) => eval_expression(es.expr.as_ref()),
                _ => panic!("Eval: Invalid expression statement {:?}", node)
            }
        }

        AstNode::Program => {
            match node.as_any().downcast_ref::<Program>() {
                Some(p) => eval_program(p),
                _ => panic!("Eval: Invalid boolean expression {:?}", node)
            }
        }

        _ => panic!("Unrecognized AST node {:?}", node)
    }
}

pub fn eval_expression(expr: &dyn Expression) -> Box<dyn Object> {
    let mut result: Box<dyn Object> = Error::new(String::from("Expression"));

    match expr.ast_node_type() {
        AstNode::IntegerExpression => {
            result = match expr.as_any().downcast_ref::<Integer>() {
                Some(i) => Integer::new(i.value),
                _ => panic!("Eval: Invalid integer expression {:?}", expr)
            }
        },
        _ => unimplemented!("Unable to evaluate expression {}", expr)
    }
    result
}

pub fn eval_program(program: &Program) -> Box<dyn Object> {
    let mut result: Box<dyn Object> = Error::new(String::from("Program start"));
    for stmt in &program.statements {
        match stmt.ast_node_type() {
            AstNode::ExpressionStatement => {
                result = match stmt.as_any().downcast_ref::<ExpressionStatement>() {
                    Some(expr_stmt) => eval(expr_stmt),
                    _ => panic!("Eval: Invalid expression statement {:?}", stmt)
                }
            }
            _ => unimplemented!("Unimplemented eval for {:?}", stmt)
        }
    }
    result
}


#[cfg(test)]
mod tests {
    use crate::ast::Statement;
    use crate::lexer::Lexer;
    use crate::parser::Parser;
    use crate::evaluator::{eval, Object, ObjectType};

    fn test_eval_program(input: &str) -> Box<dyn Object> {
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program().unwrap();
        eval(program.as_ref())
    }


    #[test]
    fn test_eval_integer_expression() {
        struct IntTestStruct {
            int_str: String,
            int_val: usize,
        }

        impl IntTestStruct {
            fn new(int_str: String, int_val: usize) -> IntTestStruct {
                IntTestStruct { int_str, int_val }
            }
        }

        let mut test_cases: Vec<IntTestStruct> = vec![];
        test_cases.push(IntTestStruct::new(String::from("1"), 1));
        test_cases.push(IntTestStruct::new(String::from("3"), 3));

        for tc in test_cases {
            let int_obj = test_eval_program(tc.int_str.as_str());
            assert_eq!(int_obj.obj_type(), ObjectType::Integer);
            assert_eq!(int_obj.to_string(), tc.int_str);
        }
    }
}