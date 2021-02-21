use lexer::Token;

trait Statement {}

trait Expression {}

// Statements

// Let
struct LetStatement {
    id: Identifier,
    expr: dyn Expression,
}

impl Statement for LetStatement {}

// Return
struct ReturnStatement {
    expr: dyn Expression
}

impl Statement for ReturnStatement{}

// Expression
struct ExpressionStatement {
    expr: dyn Expression
}

impl Statement for ExpressionStatement{}

// Block
struct BlockStatement {
    block: Vec<dyn Statement>
}

impl Statement for BlockStatement{}

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

impl Expression for Boolean;

// Int
struct Integer {
    value: usize
}

impl Expression for Integer;

// Prefix Expression
struct PrefixExpression
{
    op: String,
    expr: dyn Expression,
}

impl Expression for PrefixExpression;

// Infix Expression
struct InfixExpression
{
    left: dyn Expression,
    op: String,
    right: dyn Expression
}

impl Expression for InfixExpression;

// If Expression

struct IfExpression {
    cond: dyn Expression,
    true_block: BlockStatement,
    false_block: BlockStatement,
}

impl Expression for IfExpression{}

// Function

struct FunctionLiteral {
    parameters: Vec<Identifier>,
    block: BlockStatement
}

impl Expression for FunctionLiteral{}

// Call Expression

struct CallExpression {
    function: dyn Expression,
    parameters: Vec<dyn Expression>,
}

impl Expression for CallExpression{}