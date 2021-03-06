use std::any::Any;
use crate::object::{Object};
use crate::ast::{Node, AstNode, Integer, Boolean, Identifier, Program};

pub fn eval(node: Box<dyn Node>) -> Box<dyn Object> {
    match node.ast_node_type() {
        AstNode::IntegerExpression => {
            match node.as_any().downcast_ref::<Integer>() {
                Some(i) => Integer::new(i.value),
                _ => panic!("Eval: Invalid integer expression {:?}", node)
            }
        }

        AstNode::BooleanExpression => {
            match node.as_any().downcast_ref::<Boolean>() {
                Some(b) => Boolean::new(b.value),
                _ => panic!("Eval: Invalid boolean expression {:?}", node)
            }
        }

        _ => panic!("Unrecognized AST node {:?}", node)
    }
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
        eval(program)
    }

    #[test]
    fn test_eval_integer_expression() {
        struct IntTestStruct<'a> {
            int_str: &'a str,
            int_val: usize,
        }

        impl IntTestStruct {
            fn new(int_str: &str, int_val: usize) -> IntTestStruct {
                IntTestStruct { int_str, int_val }
            }
        }

        let mut test_cases: Vec<IntTestStruct> = vec![];
        test_cases.push(IntTestStruct::new("1", 1));
        test_cases.push(IntTestStruct::new("3", 3));

        for tc in test_cases {
            let int_obj = test_eval_program(tc.int_str);
            assert_eq!(int_obj.obj_type(), ObjectType::Integer);
            assert_eq!(int_obj.to_string(), tc.int_str);
        }
    }
}