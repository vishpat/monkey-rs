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

pub fn eval_expression(expr: &Expression) -> Object {
    Object::Nil
}

pub fn eval_let_statement(identifier: String, expr: &Expression) -> Object {
    let expr_val = eval_expression(expr);
    Object::Nil
}

pub fn eval_return_statement(expr: &Expression) -> Object {
    eval_expression(expr)
}

pub fn eval_program(program: Program) -> Object
{
    let mut val = Object::Nil;
    for stmt in program.stmts {
        val = match stmt {
            Statement::Let(id, expr) => eval_let_statement(id, &*expr),
            Statement::Return(Some(expr)) => {return eval_return_statement(&*expr)},
            Statement::Return(None) => {return Object::Nil},
            Statement::Expression(expr) => eval_expression(&*expr),
        };
    }
    return val;
}