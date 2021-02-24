use crate::lexer::Token;
use std::ptr::write_bytes;

#[derive(Debug, PartialEq)]
pub enum AstNode {
    LetStatement,
    ReturnStatement,
    ExpressionStatement,
    BlockStatement,

    IdentifierExpression,
    BooleanExpression,
    IntegerExpression,
    PrefixExpression,
    InfixExpression,
    IfExpression,
    FunctionLiteralExpression,
    CallExpression,
}

pub trait Node: std::fmt::Debug {

    fn ast_node_type(&self) -> AstNode;
}

pub trait Statement: Node + std::fmt::Display {}

pub trait Expression: Node + std::fmt::Display {}

pub struct Program {
    pub(crate) statements: Vec<Box<dyn Statement>>
}

// Statements

// Let
#[derive(Debug)]
pub struct LetStatement {
    id: Box<Identifier>,
    expr: Box<dyn Expression>,
}

impl LetStatement {
    pub fn new(id: Box<Identifier>, expr: Box<dyn Expression>) -> Box<LetStatement> {
        Box::new(LetStatement { id, expr })
    }
}

impl std::fmt::Display for LetStatement {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{} = {};", self.id, self.expr)
    }
}

impl Statement for LetStatement {}

impl Node for LetStatement {
    fn ast_node_type(&self) -> AstNode {
        AstNode::LetStatement
    }
}

// Return
#[derive(Debug)]
pub struct ReturnStatement {
    expr: Box<dyn Expression>
}

impl std::fmt::Display for ReturnStatement {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(fmt, "return {};", self.expr)
    }
}

impl Statement for ReturnStatement {}

impl Node for ReturnStatement {
    fn ast_node_type(&self) -> AstNode {
        AstNode::ReturnStatement
    }
}

// Expression
#[derive(Debug)]
pub struct ExpressionStatement {
    expr: Box<dyn Expression>
}

impl std::fmt::Display for ExpressionStatement {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{};", self.expr)
    }
}

impl Statement for ExpressionStatement {}

impl Node for ExpressionStatement {
    fn ast_node_type(&self) -> AstNode {
        AstNode::ExpressionStatement
    }
}


// Block
#[derive(Debug)]
pub struct BlockStatement {
    block: Box<Vec<Box<dyn Statement>>>
}

impl std::fmt::Display for BlockStatement {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(fmt, "{{");
        for x in self.block.iter() {
            write!(fmt, "{}", x);
        }
        write!(fmt, "}}")
    }
}

impl Statement for BlockStatement {}

impl Node for BlockStatement {
    fn ast_node_type(&self) -> AstNode {
        AstNode::BlockStatement
    }
}

// Expressions

// Ident
#[derive(Debug)]
pub struct Identifier {
    value: Box<String>
}

impl Identifier {
    pub fn new(str: Box<String>) -> Box<Identifier> {
        Box::new(Identifier { value: str })
    }
}

impl std::fmt::Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}


impl Expression for Identifier {}

impl Node for Identifier {
    fn ast_node_type(&self) -> AstNode {
        AstNode::IdentifierExpression
    }
}

// Bool
#[derive(Debug)]
pub struct Boolean {
    value: bool
}

impl std::fmt::Display for Boolean {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Expression for Boolean {}

impl Node for Boolean {
    fn ast_node_type(&self) -> AstNode {
        AstNode::BooleanExpression
    }
}

// Int
#[derive(Debug)]
pub struct Integer {
    value: usize
}

impl Integer {
    pub fn new(val: usize) -> Box<Integer> {
        Box::new(Integer { value: val })
    }
}

impl std::fmt::Display for Integer {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Expression for Integer {}

impl Node for Integer {
    fn ast_node_type(&self) -> AstNode {
        AstNode::IntegerExpression
    }
}

// Prefix Expression
#[derive(Debug)]
pub struct PrefixExpression
{
    op: Box<String>,
    expr: Box<dyn Expression>,
}

impl std::fmt::Display for PrefixExpression {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{}{}", self.op, self.expr)
    }
}

impl Expression for PrefixExpression {}

impl Node for PrefixExpression {
    fn ast_node_type(&self) -> AstNode {
        AstNode::PrefixExpression
    }
}

// Infix Expression
#[derive(Debug)]
pub struct InfixExpression
{
    left: Box<dyn Expression>,
    op: Box<String>,
    right: Box<dyn Expression>,
}

impl InfixExpression {
    pub fn new(left: Box<dyn Expression>, op: Box<String>, right: Box<dyn Expression>) -> Box<InfixExpression> {
        Box::new(InfixExpression{left, op, right})
    }
}

impl std::fmt::Display for InfixExpression {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(fmt, "{} {} {}", self.left, self.op, self.right)
    }
}

impl Expression for InfixExpression {}

impl Node for InfixExpression {
    fn ast_node_type(&self) -> AstNode {
        AstNode::InfixExpression
    }
}

// If Expression
#[derive(Debug)]
pub struct IfExpression {
    cond: Box<dyn Expression>,
    true_block: Box<BlockStatement>,
    false_block: Box<BlockStatement>,
}

impl std::fmt::Display for IfExpression {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(fmt, "if ({}) {} else {};", self.cond, self.true_block, self.false_block)
    }
}

impl Expression for IfExpression {}

impl Node for IfExpression {
    fn ast_node_type(&self) -> AstNode {
        AstNode::IfExpression
    }
}


// Function
#[derive(Debug)]
pub struct FunctionLiteral {
    name: Identifier,
    parameters: Box<Vec<Identifier>>,
    block: Box<BlockStatement>,
}

impl std::fmt::Display for FunctionLiteral {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(fmt, "fn {} {}", self.name, self.block)
    }
}

impl Expression for FunctionLiteral {}

impl Node for FunctionLiteral {
    fn ast_node_type(&self) -> AstNode {
        AstNode::FunctionLiteralExpression
    }
}

// Call Expression
#[derive(Debug)]
pub struct CallExpression {
    function: Box<dyn Expression>,
    parameters: Box<Vec<Box<dyn Expression>>>,
}

impl std::fmt::Display for CallExpression {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{}()", self.function);
        for x in self.parameters.iter() {
            write!(fmt, "{}", x);
        }
        write!(fmt, "")
    }
}

impl Expression for CallExpression {}

impl Node for CallExpression {
    fn ast_node_type(&self) -> AstNode {
        AstNode::CallExpression
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{Identifier, InfixExpression, LetStatement, Node, AstNode};

    #[test]
    fn test_infix_expression() {
        let x =
            Box::new(Identifier { value: Box::new(String::from("x")) });
        assert_eq!(x.ast_node_type(), AstNode::IdentifierExpression);

        let y =
            Box::new(Identifier { value: Box::new(String::from("y")) });
        assert_eq!(y.ast_node_type(), AstNode::IdentifierExpression);

        let z =
            Box::new(Identifier { value: Box::new(String::from("z")) });
        assert_eq!(z.ast_node_type(), AstNode::IdentifierExpression);

        let infix_expr = Box::new(InfixExpression { left: x, op: Box::new(String::from("+")), right: y });
        assert_eq!(infix_expr.ast_node_type(), AstNode::InfixExpression);

        let let_expr = Box::new(LetStatement { id: z, expr: infix_expr });
        assert_eq!(let_expr.ast_node_type(), AstNode::LetStatement);

        let let_expr_str = format!("{}", let_expr);
        assert_eq!("z = x + y;", let_expr_str);
    }
}