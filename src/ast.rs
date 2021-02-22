use crate::lexer::Token;
use std::ptr::write_bytes;

trait Statement {}

impl std::fmt::Display for dyn Statement {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "")
    }
}

trait Expression {}

impl std::fmt::Display for dyn Expression {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "")
    }
}

struct Program {
    statements: Vec<Box<dyn Statement>>
}

// Statements

// Let
struct LetStatement {
    id: Box<Identifier>,
    expr: Box<dyn Expression>,
}

impl std::fmt::Display for LetStatement {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{} = {};", self.id, self.expr)
    }
}

impl Statement for LetStatement{}

// Return
struct ReturnStatement {
    expr: Box<dyn Expression>
}

impl std::fmt::Display for ReturnStatement {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(fmt, "return {};", self.expr)
    }
}

impl Statement for ReturnStatement{}

// Expression
struct ExpressionStatement {
    expr: Box<dyn Expression>
}

impl std::fmt::Display for ExpressionStatement {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{};", self.expr)
    }
}

impl Statement for ExpressionStatement{}

// Block
struct BlockStatement {
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

impl Statement for BlockStatement{}

// Expressions

// Ident
struct Identifier {
    value: Box<String>
}

impl std::fmt::Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}


impl Expression for Identifier {}

// Bool
struct Boolean {
    value: bool
}

impl std::fmt::Display for Boolean {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Expression for Boolean{}

// Int
struct Integer {
    value: usize
}

impl std::fmt::Display for Integer {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Expression for Integer{}

// Prefix Expression
struct PrefixExpression
{
    op: Box<String>,
    expr: Box<dyn Expression>,
}

impl std::fmt::Display for PrefixExpression {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(fmt, "{}{}", self.op, self.expr)
    }
}

impl Expression for PrefixExpression{}


// Infix Expression
struct InfixExpression
{
    left: Box<dyn Expression>,
    op: Box<String>,
    right: Box<dyn Expression>
}

impl std::fmt::Display for InfixExpression {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(fmt, "{} {} {};", self.left, self.op, self.right)
    }
}

impl Expression for InfixExpression{}

// If Expression
struct IfExpression {
    cond: Box<dyn Expression>,
    true_block: Box<BlockStatement>,
    false_block: Box<BlockStatement>,
}

impl std::fmt::Display for IfExpression {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(fmt, "if ({}) {} else {};", self.cond, self.true_block, self.false_block)
    }
}

impl Expression for IfExpression{}

// Function
struct FunctionLiteral {
    name: Identifier,
    parameters: Box<Vec<Identifier>>,
    block: Box<BlockStatement>
}

impl std::fmt::Display for FunctionLiteral {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(fmt, "fn {} {}", self.name, self.block)
    }
}

impl Expression for FunctionLiteral{}

// Call Expression
struct CallExpression {
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

impl Expression for CallExpression{}