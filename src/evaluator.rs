use crate::ast::*;
use crate::object::Object;

pub fn eval_integer(int_literal: &Expression) -> Object
{
    match int_literal {
        Expression::IntegerLiteral(i) => Object::Integer(*i),
        _ => panic!("Expected integer literal"),
    }
}

pub fn eval_identifier(identifier: &Expression) -> Object
{
    match identifier {
        Expression::Identifier(i) => Object::Identifier(i.to_string()),
        _ => panic!("Expected identifier")
    }
}

pub fn eval_prefix_expression(prefix: &Prefix, expression: &Expression) -> Object {
    let expr_val = eval_expression(expression);
    match prefix {
        Prefix::Minus => {
            match expr_val {
                Object::Integer(i) => Object::Integer(-1 * i),
                _ => panic!("Invalid expression {} in prefix expression, expected integer", expr_val)
            }
        }
        Prefix::Bang => {
            match expr_val {
                Object::Boolean(b) => Object::Boolean(!b),
                _ => panic!("Invalid expression {} in prefix expression, expected boolean", expr_val)
            }
        }
    }
}

pub fn eval_infix_expression(infix: &Infix, left: &Expression, right: &Expression) -> Object {
    let left_obj = eval_expression(left);
    let right_obj = eval_expression(right);

    let left_val = match left_obj {
        Object::Integer(i) => i,
        _ => panic!("Invalid value in expression {}, expected int", left_obj),
    };
    let right_val = match right_obj {
        Object::Integer(i) => i,
        _ => panic!("Invalid value in expression {}, expected int", right_obj),
    };

    match infix {
        Infix::Plus => Object::Integer(left_val + right_val),
        Infix::Minus => Object::Integer(left_val - right_val),
        Infix::Asterisk => Object::Integer(left_val * right_val),
        Infix::Slash => Object::Integer(left_val / right_val),
        Infix::NotEq => Object::Boolean(left_val != right_val),
        Infix::Eq => Object::Boolean(left_val == right_val),
        Infix::Gt => Object::Boolean(left_val > right_val),
        Infix::Lt => Object::Boolean(left_val < right_val),
        _ => panic!("Invalid op {}", infix)
    }
}

pub fn eval_block_statement(block: &BlockStatement) -> Object {
    let mut val = Object::Nil;
    for stmt in &block.stmts {
        val = match stmt {
            Statement::Let(x, expr) => eval_let_statement(x.to_string(), &*expr),
            Statement::Return(Some(x)) => {
                return eval_return_statement(&*x);
            }
            Statement::Return(None) => {
                return Object::Nil;
            }
            Statement::Expression(expr) => eval_expression(&*expr),
        }
    }
    val
}

pub fn eval_if_expression(expr: &Expression, true_block: &BlockStatement, false_block: &Option<Box<BlockStatement>>) -> Object {
    let expr_obj = eval_expression(expr);
    let expr_val = match expr_obj {
        Object::Boolean(v) => v,
        _ => panic!("Expected boolean expression in if statement, found {}", expr_obj)
    };

    if expr_val {
        eval_block_statement(true_block)
    } else if false_block.is_some() {
        eval_block_statement(false_block.as_ref().unwrap().as_ref())
    } else {
        Object::Nil
    }
}


pub fn eval_expression(expr: &Expression) -> Object {
    match expr {
        Expression::IntegerLiteral(i) => Object::Integer(*i),
        Expression::Identifier(s) => Object::Identifier(s.to_string()),
        Expression::Boolean(b) => Object::Boolean(*b),
        Expression::Prefix(prefix, expr) =>
            eval_prefix_expression(prefix, expr),
        Expression::Infix(infix, left, right) =>
            eval_infix_expression(infix, left, right),
        Expression::If(expr, true_block, false_block) =>
            eval_if_expression(expr, true_block, false_block),
        Expression::FunctionLiteral(params, block) =>
            Object::FunctionLiteral(params.clone(), *block.clone()),
        _ => Object::Nil
    }
}

pub fn eval_let_statement(identifier: String, expr: &Expression) -> Object {
    let expr_val = eval_expression(expr);
    Object::Nil
}

pub fn eval_return_statement(expr: &Expression) -> Object {
    eval_expression(expr)
}

pub fn eval_program(program: &Program) -> Object
{
    let mut val = Object::Nil;
    for stmt in &program.stmts {
        val = match stmt {
            Statement::Let(id, expr) => eval_let_statement(id.to_string(), &*expr),
            Statement::Return(Some(expr)) => { return eval_return_statement(&*expr); }
            Statement::Return(None) => { return Object::Nil; }
            Statement::Expression(expr) => eval_expression(&*expr),
        };
    }
    return val;
}

#[cfg(test)]
mod tests {
    use crate::lexer::{Lexer, Token};
    use crate::parser::Parser;
    use std::any::Any;
    use crate::object::Object;
    use crate::evaluator::*;
    use std::process::id;

    fn test_eval_program(input: &str) -> Object {
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program().unwrap();
        eval_program(program.as_ref())
    }

    struct TestCase<'a> {
        test_str: &'a str,
        val: Object,
    }

    fn check_test_cases(test_cases: Vec<TestCase>) {
        for test_case in test_cases {
            assert_eq!(test_eval_program(test_case.test_str), test_case.val);
        }
    }

    #[test]
    fn test_eval_integer() {
        let test_cases = vec![TestCase { test_str: "10", val: Object::Integer(10) }];
        check_test_cases(test_cases);
    }

    #[test]
    fn test_eval_boolean() {
        let test_cases = vec![
            TestCase { test_str: "true", val: Object::Boolean(true) },
            TestCase { test_str: "false", val: Object::Boolean(false) },
        ];
        check_test_cases(test_cases);
    }

    #[test]
    fn test_eval_return() {
        let test_cases = vec![
            TestCase { test_str: "return 0;", val: Object::Integer(0) },
            TestCase { test_str: "return;", val: Object::Nil },
        ];

        check_test_cases(test_cases);
    }

    #[test]
    fn test_eval_prefix() {
        let test_cases = vec![
            TestCase { test_str: "!true", val: Object::Boolean(false) },
            TestCase { test_str: "!false", val: Object::Boolean(true) },
            TestCase { test_str: "-1", val: Object::Integer(-1) }
        ];

        check_test_cases(test_cases);
    }

    #[test]
    fn test_eval_infix() {
        let test_cases = vec![
            TestCase { test_str: "10 > 20", val: Object::Boolean(false) },
            TestCase { test_str: "-1 + 0", val: Object::Integer(-1) },
            TestCase { test_str: "5 > 3", val: Object::Boolean(true) },
            TestCase { test_str: "4 < 2", val: Object::Boolean(false) },
            TestCase { test_str: "5 == 3", val: Object::Boolean(false) },
            TestCase { test_str: "4 != 2", val: Object::Boolean(true) },
            TestCase { test_str: "(2*2 + 1) == 5", val: Object::Boolean(true) },
            TestCase { test_str: "(2 + 3)*2 == 10", val: Object::Boolean(true) },
        ];

        check_test_cases(test_cases);
    }

    #[test]
    fn test_eval_if_expr() {
        let test_cases = vec![
            TestCase { test_str: "if (10 > 20) {20} else {10}", val: Object::Integer(10) },
            TestCase { test_str: "if (21 > 20) {20} else {10}", val: Object::Integer(20) },
            TestCase { test_str: "if (21 > 20) {20} ", val: Object::Integer(20) },
            TestCase { test_str: "if (21 < 20) {20} ", val: Object::Nil },
            TestCase { test_str: "if (21 > 20) {let x = 30; 20} ", val: Object::Integer(20) },
        ];

        check_test_cases(test_cases);
    }

}