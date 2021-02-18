pub enum TokenType {
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
    LET(String),
    TRUE(String),
    FALSE(String),
    IF(String),
    ELSE(String),
    RETURN(String),
}

pub struct Token {
    pub token_type: TokenType,
    pub literal: String,
}

impl Token {
    pub fn new(token_type: TokenType, literal: String) -> Token {
        Token {
            token_type,
            literal,
        }
    }
}

pub struct Lexer {
    input: String,
}

impl Lexer {
    pub fn new(input: &str) -> Box<Lexer> {
        Box::new(Lexer {
            input: String::from(input),
        })
    }

    pub fn iter(&self) -> LexerIterator {
        LexerIterator {
            index: 0,
            lexer: &self,
        }
    }
}

pub struct LexerIterator<'a> {
    index: usize,
    lexer: &'a Lexer,
}

impl<'a> Iterator for LexerIterator<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        self.index += 1;
        if self.index <= self.lexer.input.len() {
            Some(&self.lexer.input[self.index - 1..self.index])
        } else {
            None
        }
    }
}

