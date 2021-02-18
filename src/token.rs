enum TokenType {
    ILLEGAL,
    EOF,

    // Identifiers + Literals
    IDENT(String),
    INT(usize),

    // Operators
    ASSIGN(char),
    PLUS(char),

    // Delimiters
    COMMA(char),
    SEMICOLON(char),

    LPAREN(char),
    RPAREN(char),
    LBRACE(char),
    RBRACE(char),

    // Keywords
    FUNCION(String),
    LET(String)
}


struct Token {
    pub token_type: TokenType,
    pub literal: String,
    pub file: String,
    pub lineno: usize,
}