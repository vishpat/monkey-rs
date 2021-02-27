use crate::lexer::Token;
use std::ptr::write_bytes;
use std::any::Any;

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

    // Required to downcast a Trait to specify structure
    fn as_any(&self) -> &dyn Any;
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
    pub id: Box<Identifier>,
    pub expr: Box<dyn Expression>,
}

impl LetStatement {
    pub fn new(id: Box<Identifier>, expr: Box<dyn Expression>) -> Box<LetStatement> {
        Box::new(LetStatement { id, expr })
    }
}

impl std::fmt::Display for LetStatement {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "let {} = {};", self.id, self.expr)
    }
}

impl Statement for LetStatement {}

impl Node for LetStatement {
    fn ast_node_type(&self) -> AstNode {
        AstNode::LetStatement
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

// Return
#[derive(Debug)]
pub struct ReturnStatement {
    pub expr: Box<dyn Expression>
}

impl ReturnStatement {
    pub fn new(expr: Box<dyn Expression>) -> Box<ReturnStatement> {
        Box::new(ReturnStatement { expr })
    }
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

    fn as_any(&self) -> &dyn Any {
        self
    }
}

// Expression
#[derive(Debug)]
pub struct ExpressionStatement {
    pub expr: Box<dyn Expression>
}

impl ExpressionStatement {
    pub fn new(expr: Box<dyn Expression>) -> Box<ExpressionStatement> {
        Box::new(ExpressionStatement{expr: expr})
    }
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
    fn as_any(&self) -> &dyn Any {
        self
    }
}


// Block
#[derive(Debug)]
pub struct BlockStatement {
    pub block: Box<Vec<Box<dyn Statement>>>
}

impl BlockStatement {
    pub fn new(statements: Box<Vec<Box<dyn Statement>>>) -> Box<BlockStatement> {
        Box::new(BlockStatement{block: statements})
    }
}

impl std::fmt::Display for BlockStatement {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(fmt, "{{");
        for x in self.block.iter() {
            write!(fmt, "{{\n\t {} \n\t}}", x);
        }
        write!(fmt, "}}")
    }
}

impl Statement for BlockStatement {}

impl Node for BlockStatement {
    fn ast_node_type(&self) -> AstNode {
        AstNode::BlockStatement
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
}

// Expressions

// Ident
#[derive(Debug)]
pub struct Identifier {
    pub value: Box<String>
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

    fn as_any(&self) -> &dyn Any {
        self
    }
}

// Bool
#[derive(Debug)]
pub struct Boolean {
    pub value: bool
}

impl Boolean {
    pub fn new(val: bool) -> Box<Boolean> {
        Box::new(Boolean { value: val })
    }
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

    fn as_any(&self) -> &dyn Any {
        self
    }
}

// Int
#[derive(Debug)]
pub struct Integer {
    pub value: usize
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

    fn as_any(&self) -> &dyn Any {
        self
    }
}

// Prefix Expression
#[derive(Debug)]
pub struct PrefixExpression
{
    pub op: Box<Token>,
    pub expr: Box<dyn Expression>,
}

impl PrefixExpression {
    pub fn new(op: Box<Token>, expr: Box<dyn Expression>) -> Box<PrefixExpression> {
        Box::new(PrefixExpression { op, expr })
    }
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

    fn as_any(&self) -> &dyn Any {
        self
    }
}

// Infix Expression
#[derive(Debug)]
pub struct InfixExpression
{
    pub left: Box<dyn Expression>,
    pub op: Box<Token>,
    pub right: Box<dyn Expression>,
}

impl InfixExpression {
    pub fn new(left: Box<dyn Expression>, op: Box<Token>, right: Box<dyn Expression>) -> Box<InfixExpression> {
        Box::new(InfixExpression { left, op, right })
    }
}

impl std::fmt::Display for InfixExpression {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(fmt, "({} {} {})", self.left, self.op, self.right)
    }
}

impl Expression for InfixExpression {}

impl Node for InfixExpression {
    fn ast_node_type(&self) -> AstNode {
        AstNode::InfixExpression
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

// If Expression
#[derive(Debug)]
pub struct IfExpression {
    pub cond: Box<dyn Expression>,
    pub true_block: Box<BlockStatement>,
    pub false_block: Box<BlockStatement>,
}

impl IfExpression {
    pub fn new(cond: Box<dyn Expression>, true_block: Box<BlockStatement>,
               false_block: Box<BlockStatement>) -> Box<IfExpression> {
        Box::new(IfExpression { cond, true_block, false_block })
    }
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

    fn as_any(&self) -> &dyn Any {
        self
    }
}


// Function
#[derive(Debug)]
pub struct FunctionLiteral {
    pub name: Identifier,
    pub parameters: Box<Vec<Identifier>>,
    pub block: Box<BlockStatement>,
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

    fn as_any(&self) -> &dyn Any {
        self
    }
}

// Call Expression
#[derive(Debug)]
pub struct CallExpression {
    pub function: Box<dyn Expression>,
    pub parameters: Box<Vec<Box<dyn Expression>>>,
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

    fn as_any(&self) -> &dyn Any {
        self
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{Identifier, InfixExpression, LetStatement, Node, AstNode};
    use crate::lexer::Token;

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

        let infix_expr = Box::new(InfixExpression { left: x, op: Box::new(Token::Plus), right: y });
        assert_eq!(infix_expr.ast_node_type(), AstNode::InfixExpression);

        let let_expr = Box::new(LetStatement { id: z, expr: infix_expr });
        assert_eq!(let_expr.ast_node_type(), AstNode::LetStatement);

        let let_expr_str = format!("{}", let_expr);
        assert_eq!("let z = (x + y);", let_expr_str);
    }
}