use std::any::Any;
use crate::object::{Object, ObjectType, Error};
use crate::ast::{Node, AstNode, Integer, Boolean, Identifier, Program, ExpressionStatement, Expression, InfixExpression, PrefixExpression, Statement};
use std::borrow::Borrow;
use std::ops::Deref;
use crate::lexer::Token;

pub fn eval(node: &dyn Node) -> Box<dyn Object> {

    println!("Evaluating {:?}", node);

    match node.ast_node_type() {

        AstNode::IntegerExpression => {
            match node.as_any().downcast_ref::<Integer>() {
                Some(i) => Integer::new(i.value),
                _ => panic!("Eval: Invalid integer expression {:?}", node)
            }
        },

        AstNode::BooleanExpression => {
            match node.as_any().downcast_ref::<Boolean>() {
                Some(b) => Boolean::new(b.value),
                _ => panic!("Eval: Invalid boolean expression {:?}", node)
            }
        },

        AstNode::PrefixExpression => {
            match node.as_any().downcast_ref::<PrefixExpression>() {
                Some(prefix_expr) => eval_prefix_expression(&prefix_expr.op,
                                                            prefix_expr.expr.node()),
                _ => panic!("Eval: Invalid boolean expression {:?}", node)
            }
        }

        AstNode::ExpressionStatement => {
            match node.as_any().downcast_ref::<ExpressionStatement>() {
                Some(expr_stmt) => eval(expr_stmt.expr.node()),
                _ => panic!("Eval: Invalid boolean expression {:?}", node)
            }
        },

        AstNode::Program => {
            match node.as_any().downcast_ref::<Program>() {
                Some(p) => eval_program(p),
                _ => panic!("Eval: Invalid Program {:?}", node)
            }
        }

        _ => panic!("Unrecognized AST node {:?}", node)
    }
}

pub fn eval_prefix_expression(op: &Token, expr: &dyn Node) -> Box<dyn Object> {
    match op {
        Token::Bang => {
            match expr.as_any().downcast_ref::<Boolean>() {
                Some(b) => {
                    Boolean::new(!b.value)
                },
                _ => panic!("Invalid prefix expression type {:?}, expected bool", expr.ast_node_type())
            }
        },
        Token::Minus => {
            match expr.as_any().downcast_ref::<Integer>() {
                Some(i) => {
                    Integer::new(i.value*-1)
                },
                _ => panic!("Invalid prefix expression type {:?}, expected int", expr.ast_node_type())
            }
        },
        _ => panic!("Invalid prefix operator {}", op)

    }
}

pub fn eval_program(program: &Program) -> Box<dyn Object> {
    let mut result: Box<dyn Object> = Error::new(String::from("Program start"));
    for stmt in &program.statements {
        result = match stmt.ast_node_type() {
            AstNode::ExpressionStatement => eval(stmt.node()),
            _ => unimplemented!("Unimplemented eval for {:?}", stmt)
        }
    }
    result
}


#[cfg(test)]
mod tests {
    use crate::ast::{Statement, Boolean};
    use crate::lexer::Lexer;
    use crate::parser::Parser;
    use crate::evaluator::{eval, Object, ObjectType};

    fn test_eval_program(input: &str) -> Box<dyn Object> {
        println!("Test: Evaluating {}", input);
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program().unwrap();
        eval(program.as_ref())
    }


    #[test]
    fn test_eval_integer_expression() {
        struct IntTestStruct {
            int_str: String,
            int_val: i64,
        }

        impl IntTestStruct {
            fn new(int_str: String, int_val: i64) -> IntTestStruct {
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

    #[test]
    fn test_eval_boolean_expression() {
        struct BoolTestStruct {
            bool_str: String,
            bool_val: bool,
        }

        impl BoolTestStruct {
            fn new(bool_str: String, bool_val: bool) -> BoolTestStruct {
                BoolTestStruct { bool_str, bool_val }
            }
        }

        let mut test_cases: Vec<BoolTestStruct> = vec![];
        test_cases.push(BoolTestStruct::new(String::from("true"), true));
        test_cases.push(BoolTestStruct::new(String::from("false"), false));

        for tc in test_cases {
            let bool_obj = test_eval_program(tc.bool_str.as_str());
            assert_eq!(bool_obj.obj_type(), ObjectType::Boolean);
            assert_eq!(bool_obj.to_string(), tc.bool_str);
        }
    }

    #[test]
    fn test_eval_prefix_bool_expression() {
        struct PrefixTestStruct {
            bool_str: String,
            bool_val: bool,
        }

        impl PrefixTestStruct {
            fn new(bool_str: String, bool_val: bool) -> PrefixTestStruct {
                PrefixTestStruct { bool_str, bool_val }
            }
        }

        let mut test_cases: Vec<PrefixTestStruct> = vec![];
        test_cases.push(PrefixTestStruct::new(String::from("!true"), false));
        test_cases.push(PrefixTestStruct::new(String::from("!false"), true));

        for tc in test_cases {
            let bool_obj = test_eval_program(tc.bool_str.as_str());

            assert_eq!(bool_obj.obj_type(), ObjectType::Boolean);
            match bool_obj.as_any().downcast_ref::<Boolean>() {
                Some(i) => {
                    assert_eq!(i.value, tc.bool_val);
                },
                _ => panic!("Invalid type expected Boolean")
            }
        }
    }
}