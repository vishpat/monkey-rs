use std::any::Any;
use crate::object::{Object, ObjectType, Error, Nil};
use crate::ast::{Node, AstNode, Integer, Boolean, Identifier, Program, ExpressionStatement, Expression, InfixExpression, PrefixExpression, Statement, IfExpression};
use std::borrow::Borrow;
use std::ops::Deref;
use crate::lexer::Token;

pub fn eval(node: &dyn Node) -> Box<dyn Object> {
    println!("Evaluating {:?}", node);

    match node.ast_node_type() {
        AstNode::IntegerExpression => eval_int_expr(node),
        AstNode::BooleanExpression => eval_bool_expr(node),
        AstNode::ExpressionStatement => eval_expr_stmt(node),
        AstNode::PrefixExpression => eval_prefix_expression(node),
        AstNode::InfixExpression => eval_infix_expression(node),
        AstNode::IfExpression => eval_infix_expression(node),
        AstNode::BlockStatement => eval_block_statement(node),
        AstNode::Program => eval_program(node),
        _ => panic!("Unrecognized AST node {:?}", node)
    }
}

pub fn eval_bool_expr(node: &dyn Node) -> Box<dyn Object> {
    match node.ast_node_type() {
        AstNode::BooleanExpression =>
            Boolean::new(node.as_any().downcast_ref::<Boolean>().unwrap().value),
        _ => panic!("Eval: Invalid boolean expression {:?}", node)
    }
}

pub fn eval_int_expr(node: &dyn Node) -> Box<dyn Object> {
    match node.ast_node_type() {
        AstNode::IntegerExpression =>
            Integer::new(node.as_any().downcast_ref::<Integer>().unwrap().value),
        _ => panic!("Eval: Invalid integer expression {:?}", node)
    }
}

pub fn eval_expr_stmt(node: &dyn Node) -> Box<dyn Object> {
    match node.ast_node_type() {
        AstNode::ExpressionStatement =>
            eval(node.as_any().downcast_ref::<ExpressionStatement>().unwrap().expr.node()),
        _ => panic!("Eval: Invalid boolean expression {:?}", node)
    }
}

pub fn eval_prefix_expression(node: &dyn Node) -> Box<dyn Object> {

    let prefix_expr: &PrefixExpression = match node.ast_node_type() {
        AstNode::PrefixExpression => node.as_any().downcast_ref::<PrefixExpression>().unwrap(),
        _ => panic!("Eval: Invalid boolean expression {:?}", node)
    };

    let op = prefix_expr.op.as_ref();
    let mut expr = prefix_expr.expr.as_ref();
    let expr_evaluated = eval(expr.node());

    match op {
        Token::Bang => {
            match expr_evaluated.obj_type() {
                ObjectType::Boolean =>
                    Boolean::new(!expr_evaluated.as_any().downcast_ref::<Boolean>().unwrap().value),
                _ => panic!("Invalid prefix expression type {:?}, expected bool", expr.ast_node_type())
            }
        }
        Token::Minus => {
            match expr_evaluated.obj_type() {
                ObjectType::Integer => {
                    Integer::new(expr_evaluated.as_any().downcast_ref::<Integer>().unwrap().value*-1)
                }
                _ => panic!("Invalid prefix expression type {:?}, expected int", expr.ast_node_type())
            }
        }
        _ => panic!("Invalid prefix operator {}", op)
    }
}

pub fn eval_infix_expression(node: &dyn Node) -> Box<dyn Object> {
    let infix_expr: &InfixExpression = match node.as_any().downcast_ref::<InfixExpression>() {
        Some(infix_expr) => infix_expr,
        _ => panic!("Eval: Invalid boolean expression {:?}", node)
    };

    let op = infix_expr.op.as_ref();
    let left = eval(infix_expr.left.node());
    let right = eval(infix_expr.right.node());

    match op {
        Token::Plus | Token::Minus | Token::Asterik | Token::Slash |
        Token::Lt | Token::Gt | Token::Eq | Token::NotEq => {
            let left_val = match left.obj_type() {
                ObjectType::Integer => left.as_any().downcast_ref::<Integer>().unwrap().value ,
                _ => panic!("Invalid left val in {:?}, expected Integer", left.obj_type())
            };
            let right_val = match right.obj_type() {
                ObjectType::Integer => right.as_any().downcast_ref::<Integer>().unwrap().value,
                _ => panic!("Invalid right val in {:?}, expected Integer", right.obj_type())
            };
            match op {
                Token::Plus => Integer::new(left_val + right_val),
                Token::Minus => Integer::new(left_val - right_val),
                Token::Slash => Integer::new(left_val / right_val),
                Token::Asterik => Integer::new(left_val * right_val),
                Token::Lt => Boolean::new(left_val < right_val),
                Token::Gt => Boolean::new(left_val > right_val),
                Token::Eq => Boolean::new(left_val == right_val),
                Token::NotEq => Boolean::new(left_val != right_val),
                _ => panic!("Invalid op {}", op)
            }
        },
        _ => panic!("Invalid infix operator {}", op)
    }
}

pub fn eval_if_expression(node: &dyn Node) -> Box<dyn Object> {

    let if_expr: &IfExpression = match node.as_any().downcast_ref::<IfExpression>() {
        Some(if_expr) => if_expr,
        _ => panic!("Eval: Invalid boolean expression {:?}", node)
    };

    let cond= eval(&if_expr.cond).as_any().downcast_ref::<Boolean>().unwrap().value;
    if cond {
        eval(if_expr.true_block.as_ref())
    } else {
        if if_expr.false_block.is_some() {
            eval(if_expr.false_block.unwrap().as_ref())
        } else {
            Nil::new()
        }
    }
}

pub fn eval_program(node: &dyn Node) -> Box<dyn Object> {
    let program = match node.as_any().downcast_ref::<Program>() {
        Some(p) => p,
        _ => panic!("Eval: Invalid Program {:?}", node)
    };

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
    use crate::ast::{Statement, Boolean, Integer};
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
        test_cases.push(PrefixTestStruct::new(String::from("!!false"), false));
        test_cases.push(PrefixTestStruct::new(String::from("!!!false"), true));
        test_cases.push(PrefixTestStruct::new(String::from("!!!(4 > 2)"), false));
        test_cases.push(PrefixTestStruct::new(String::from("!!!(2 + 3 > 2)"), false));

        for tc in test_cases {
            let bool_obj = test_eval_program(tc.bool_str.as_str());

            assert_eq!(bool_obj.obj_type(), ObjectType::Boolean);
            match bool_obj.as_any().downcast_ref::<Boolean>() {
                Some(i) => {
                    assert_eq!(i.value, tc.bool_val);
                }
                _ => panic!("Invalid type expected Boolean")
            }
        }
    }

    #[test]
    fn test_eval_prefix_int_expression() {
        struct PrefixTestStruct {
            int_str: String,
            int_val: i64,
        }

        impl PrefixTestStruct {
            fn new(int_str: String, int_val: i64) -> PrefixTestStruct {
                PrefixTestStruct { int_str, int_val }
            }
        }

        let mut test_cases: Vec<PrefixTestStruct> = vec![];
        test_cases.push(PrefixTestStruct::new(String::from("-1"), -1));
        test_cases.push(PrefixTestStruct::new(String::from("-2"), -2));
        test_cases.push(PrefixTestStruct::new(String::from("-(2*3 + 2) + 2"), -6));

        for tc in test_cases {
            let int_obj = test_eval_program(tc.int_str.as_str());

            assert_eq!(int_obj.obj_type(), ObjectType::Integer);
            match int_obj.as_any().downcast_ref::<Integer>() {
                Some(i) => {
                    assert_eq!(i.value, tc.int_val);
                }
                _ => panic!("Invalid type expected Integet")
            }
        }
    }

    #[test]
    fn test_eval_infix_bool_expression() {
        struct InfixTestStruct {
            bool_str: String,
            bool_val: bool,
        }

        impl InfixTestStruct {
            fn new(bool_str: String, bool_val: bool) -> InfixTestStruct {
                InfixTestStruct { bool_str, bool_val }
            }
        }

        let mut test_cases: Vec<InfixTestStruct> = vec![];
        test_cases.push(InfixTestStruct::new(String::from("5 > 3"), true));
        test_cases.push(InfixTestStruct::new(String::from("4 < 2"), false));
        test_cases.push(InfixTestStruct::new(String::from("5 == 3"), false));
        test_cases.push(InfixTestStruct::new(String::from("4 != 2"), true));
        test_cases.push(InfixTestStruct::new(String::from("(2*2 + 1) != 5"), false));
        test_cases.push(InfixTestStruct::new(String::from("5 == 5"), true));
        test_cases.push(InfixTestStruct::new(String::from("(2 + 3) == 5"), true));


        for tc in test_cases {
            let bool_obj = test_eval_program(tc.bool_str.as_str());

            assert_eq!(bool_obj.obj_type(), ObjectType::Boolean);
            match bool_obj.as_any().downcast_ref::<Boolean>() {
                Some(i) => {
                    assert_eq!(i.value, tc.bool_val);
                }
                _ => panic!("Invalid type expected Boolean")
            }
        }
    }

    #[test]
    fn test_eval_infix_int_expression() {
        struct InfixTestStruct {
            int_str: String,
            int_val: i64,
        }

        impl InfixTestStruct {
            fn new(int_str: String, int_val: i64) -> InfixTestStruct {
                InfixTestStruct { int_str, int_val }
            }
        }

        let mut test_cases: Vec<InfixTestStruct> = vec![];
        test_cases.push(InfixTestStruct::new(String::from("-1"), -1));
        test_cases.push(InfixTestStruct::new(String::from("-2"), -2));

        for tc in test_cases {
            let int_obj = test_eval_program(tc.int_str.as_str());

            assert_eq!(int_obj.obj_type(), ObjectType::Integer);
            match int_obj.as_any().downcast_ref::<Integer>() {
                Some(i) => {
                    assert_eq!(i.value, tc.int_val);
                }
                _ => panic!("Invalid type expected Integet")
            }
        }
    }

}