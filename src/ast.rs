use crate::lexer::Token;

trait Statement {}

trait Expression {}

struct Program<'a> {
    statements: Vec<Box<&'a dyn Statement>>
}

// Statements

// Let
struct LetStatement<'a> {
    id: &'a Identifier,
    expr: &'a dyn Expression,
}

impl Statement for LetStatement<'_>{}

// Return
struct ReturnStatement<'a> {
    expr: &'a dyn Expression
}

impl Statement for ReturnStatement<'_>{}

// Expression
struct ExpressionStatement<'a> {
    expr: &'a dyn Expression
}

impl Statement for ExpressionStatement<'_>{}

// Block
struct BlockStatement<'a> {
    block: Vec<Box<&'a dyn Statement>>
}

impl Statement for BlockStatement<'_>{}

// Expressions

// Ident
struct Identifier {
    value: String
}

impl Expression for Identifier {}

// Bool
struct Boolean {
    value: bool
}

impl Expression for Boolean{}

// Int
struct Integer {
    value: usize
}

impl Expression for Integer{}

// Prefix Expression
struct PrefixExpression<'a>
{
    op: String,
    expr: &'a dyn Expression,
}

impl Expression for PrefixExpression<'_>{}

// Infix Expression
struct InfixExpression<'a>
{
    left: &'a dyn Expression,
    op: String,
    right: &'a dyn Expression
}

impl Expression for InfixExpression<'_>{}

// If Expression

struct IfExpression<'a> {
    cond: Box<dyn Expression>,
    true_block: &'a BlockStatement<'a>,
    false_block: &'a BlockStatement<'a>,
}

impl Expression for IfExpression<'_>{}

// Function

struct FunctionLiteral<'a> {
    parameters: Vec<&'a Identifier>,
    block: &'a BlockStatement<'a>
}

impl Expression for FunctionLiteral<'_>{}

// Call Expression

struct CallExpression<'a> {
    function: Box<&'a dyn Expression>,
    parameters: Vec<&'a Box<dyn Expression>>,
}

impl Expression for CallExpression<'_>{}