use crate::ast::*;
use crate::object::Object;
use crate::environment::Environment;
use std::cell::RefCell;
use std::rc::Rc;

pub fn eval_identifier(identifier: &Expression, env: &Rc<RefCell<Environment>>) -> Object
{
    match identifier {
        Expression::Identifier(i) => {
            let id = env.borrow_mut().get(i.as_str());
            if id.is_some() {
                id.unwrap()
            } else {
                panic!("Did not find the identifer {}", i)
            }
        }
        _ => panic!("Expected identifier")
    }
}

pub fn eval_prefix_expression(prefix: &Prefix, expression: &Expression, env: &mut Rc<RefCell<Environment>>) -> Object {
    let expr_val = eval_expression(expression, env);
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

pub fn eval_infix_expression(infix: &Infix, left: &Expression, right: &Expression, env: &mut Rc<RefCell<Environment>>) -> Object {
    let left_obj = eval_expression(left, env);
    let right_obj = eval_expression(right, env);

    match left_obj {
        Object::Integer(i) => {
            let left_int = i;
            let mut right_int;
            match right_obj {
                Object::Integer(i) => {
                    right_int = i;
                    match infix {
                        Infix::Plus => Object::Integer(left_int + right_int),
                        Infix::Minus => Object::Integer(left_int - right_int),
                        Infix::Asterisk => Object::Integer(left_int * right_int),
                        Infix::Slash => Object::Integer(left_int / right_int),
                        Infix::NotEq => Object::Boolean(left_int != right_int),
                        Infix::Eq => Object::Boolean(left_int == right_int),
                        Infix::Gt => Object::Boolean(left_int > right_int),
                        Infix::Lt => Object::Boolean(left_int < right_int),
                        _ => panic!("Inintid op {}", infix)
                    }
                }
                _ => panic!("Expected integer {}", right_obj),
            }
        },
        Object::String(s) => {
            let left_str = s;
            let mut right_str;
            match right_obj {
                Object::String(s) => {
                    right_str = s;
                    match infix {
                        Infix::Plus => Object::String(left_str + &*right_str),
                        _ => panic!("Invalid op {} for strings", infix)
                    }
                }
                _ => panic!("Expected String{}", right_obj),
            }
        },
        _ => panic!("Invalid value in expression {}, expected int", left_obj),
    }
}

pub fn eval_block_statement(block: &BlockStatement, env: &mut Rc<RefCell<Environment>>) -> Object {
    let mut val = Object::Nil;
    for stmt in &block.stmts {
        val = match stmt {
            Statement::Let(x, expr) => eval_let_statement(x.to_string(), &*expr, env),
            Statement::Return(Some(x)) => {
                return eval_return_statement(&*x, env);
            }
            Statement::Return(None) => {
                return Object::Nil;
            }
            Statement::Expression(expr) => eval_expression(&*expr, env),
        }
    }
    val
}

pub fn eval_if_expression(expr: &Expression, true_block: &BlockStatement,
                          false_block: &Option<Box<BlockStatement>>, env: &mut Rc<RefCell<Environment>>) -> Object {
    let expr_obj = eval_expression(expr, env);
    let expr_val = match expr_obj {
        Object::Boolean(v) => v,
        _ => panic!("Expected boolean expression in if statement, found {}", expr_obj)
    };

    if expr_val {
        eval_block_statement(true_block, env)
    } else if false_block.is_some() {
        eval_block_statement(false_block.as_ref().unwrap().as_ref(), env)
    } else {
        Object::Nil
    }
}

pub fn eval_function_parameters(params: &Vec<Expression>, env: &mut Rc<RefCell<Environment>>) -> Vec<Object> {
    let mut param_objs = vec![];
    for param in params.iter() {
        let param_obj = eval_expression(param, env);
        if param_obj == Object::Nil {
            panic!("Unable to evaluate parameter {}", param);
        }
        param_objs.push(eval_expression(param, env))
    }
    param_objs
}

pub fn eval_user_defined_function_call(func_params: &Vec<String>, param_objs: &Vec<Object>,
                                       func_block: &BlockStatement,
                                       env: &mut Rc<RefCell<Environment>>) -> Object {

    let mut func_new_env = Rc::new(RefCell::new(Environment::extend(env.clone())));

    let mut idx = 0;
    while idx < param_objs.len() {
        func_new_env.borrow_mut().set(&*func_params[idx], param_objs[idx].clone());
        idx += 1;
    }

    eval_block_statement(&func_block, &mut func_new_env)
}

pub fn eval_inbuilt_function_call() -> Object {
    Object::Nil
}

pub fn eval_function_call(func_expr: &Box<Expression>, parameters: &Vec<Expression>,
                          env: &mut Rc<RefCell<Environment>>) -> Object {
    let mut func_params;
    let mut func_block;
    let mut func_env;

    let func_obj = eval_expression(func_expr, env);

    match func_obj {
        Object::FunctionLiteral(params, block, env) =>
            {
                func_params = params;
                func_block = block;
                func_env = env;
            }
        _ => panic!("Invalid object type {}, expected function object", func_obj)
    };

    let param_objs = eval_function_parameters(parameters, env);
    if param_objs.len() != func_params.len() {
        panic!("Did not find the expected number of arguments for the function");
    }

    eval_user_defined_function_call(&func_params, &param_objs, &func_block, env)
}

pub fn eval_expression(expr: &Expression, env: &mut Rc<RefCell<Environment>>) -> Object {
    match expr {
        Expression::IntegerLiteral(i) => Object::Integer(*i),
        Expression::Identifier(s) => eval_identifier(expr, env),
        Expression::String(s) => Object::String(s.to_string()),
        Expression::Boolean(b) => Object::Boolean(*b),
        Expression::Prefix(prefix, expr) =>
            eval_prefix_expression(prefix, expr, env),
        Expression::Infix(infix, left, right) =>
            eval_infix_expression(infix, left, right, env),
        Expression::If(expr, true_block, false_block) =>
            eval_if_expression(expr, true_block, false_block, env),
        Expression::FunctionLiteral(params, block) =>
            Object::FunctionLiteral(params.clone(), *block.clone(), env.clone()),
        Expression::Call(func, params) => eval_function_call(func, params, env),
        _ => Object::Nil
    }
}

pub fn eval_let_statement(identifier: String, expr: &Expression, env: &mut Rc<RefCell<Environment>>) -> Object {
    let expr_val = eval_expression(expr, env);
    env.borrow_mut().set(identifier.as_str(), expr_val);
    Object::Nil
}

pub fn eval_return_statement(expr: &Expression, env: &mut Rc<RefCell<Environment>>) -> Object {
    eval_expression(expr, env)
}

pub fn eval_program(program: &Program, env: &mut Rc<RefCell<Environment>>) -> Object
{
    let mut val = Object::Nil;
    for stmt in &program.stmts {
        val = match stmt {
            Statement::Let(id, expr) => eval_let_statement(id.to_string(), &*expr, env),
            Statement::Return(Some(expr)) => { return eval_return_statement(&*expr, env); }
            Statement::Return(None) => { return Object::Nil; }
            Statement::Expression(expr) => eval_expression(&*expr, env),
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
    use crate::environment::Environment;
    use crate::evaluator::*;
    use std::process::id;

    fn test_eval_program(input: &str) -> Object {
        let mut env = Rc::new(RefCell::new(Environment::new()));
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program().unwrap();
        eval_program(program.as_ref(), &mut env)
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
            TestCase { test_str: "\"ab\" + \"cd\"", val: Object::String(String::from("abcd")) },
            TestCase { test_str: "\"ab\" + \"cd\" + \"ef\"",
                val: Object::String(String::from("abcdef")) },
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

    #[test]
    fn test_eval_let_statements() {
        let test_cases = vec![
            TestCase { test_str: "let x = 10; if (x > 20) {20} else {10}", val: Object::Integer(10) },
            TestCase { test_str: "let y = 20; if (21 > y) {20} else {10}", val: Object::Integer(20) },
            TestCase { test_str: "let z = 30; z*z; ", val: Object::Integer(900) },
            TestCase { test_str: "let a = 30; let b = 40; a + b", val: Object::Integer(70) },
        ];

        check_test_cases(test_cases);
    }

    #[test]
    fn test_eval_functions() {
        let test_cases = vec![
            TestCase { test_str: "let sum = fn(x, y){ x + y;}; \
                                  sum(10, 20);",
                        val: Object::Integer(30) },

            TestCase { test_str: "let square = fn(x){x*x}; \
                                  square(10)",
                        val: Object::Integer(100) },

            TestCase { test_str: "let gt = fn(x, y){ \
                                                if (!(x > y)) {\
                                                        x*x\
                                                } else {\
                                                        y\
                                                };\
                                           }; \
                                  gt(3, 2)", val: Object::Integer(2) },

            TestCase { test_str: "let gt = fn(x, y){ \
                                                if (x > y) \
                                                    {x*x} \
                                                else {\
                                                     y\
                                                };\
                                            }; \
                                  gt(3, 2)", val: Object::Integer(9)},

            TestCase { test_str: "let fact = fn(x) {\
                                                if (x > 1) {\
                                                    x*fact(x - 1);\
                                                } else {\
                                                    x\
                                                };\
                                             }; \
                                  fact(8);", val: Object::Integer(40320)},

            TestCase { test_str: "let sum = fn(x,y){x + y;};\
                                  let sqr = fn(x){let z = sum(x, x); z*z;};\
                                  let z = sum(2, 3) + sqr(2);\
                                  z;", val: Object::Integer(21)},

            TestCase{test_str: "fn(x, y, z){x + y + z}(1, 2, 3);", val: Object::Integer(6)},
            TestCase{test_str: "let a = \"wx\";\
                                let b = \"yz\";\
                                let z = a + b;\
                                z;", val: Object::String(String::from("wxyz"))},
        ];

        check_test_cases(test_cases);
    }
}