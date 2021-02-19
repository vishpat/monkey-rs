#[derive(PartialEq)]
pub enum TokenType {
    ILLEGAL,
    EOF,

    // Identifiers + Literals
    IDENT,
    INT,

    // Operators
    ASSIGN,
    PLUS,

    // Delimiters
    COMMA,
    SEMICOLON,

    LPAREN,
    RPAREN,
    LBRACE,
    RBRACE,

    // Keywords
    FUNCTION,
    LET,
    TRUE,
    FALSE,
    IF,
    ELSE,
    RETURN,
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

    fn is_number(input: &str) -> bool {
        false
    }

    fn is_identifier(input: &str) -> bool {
        false
    }

    fn is_operator(input: char) -> bool {
        match input {
            '=' => true,
            ';' => true,
            '(' => true,
            ')' => true,
            ',' => true,
            '+' => true,
            '{' => true,
            '}' => true,
            _ => false,
        }
    }


    pub fn token(&self, input: &str) -> TokenType {
        let ttype = match input {
            "=" => TokenType::ASSIGN,
            ";" => TokenType::SEMICOLON,
            "(" => TokenType::LPAREN,
            ")" => TokenType::RPAREN,
            "," => TokenType::COMMA,
            "+" => TokenType::PLUS,
            "{" => TokenType::LBRACE,
            "}" => TokenType::RBRACE,
            "fn" => TokenType::FUNCTION,
            "let" => TokenType::LET,
            "true" => TokenType::TRUE,
            "false" => TokenType::FALSE,
            "if" => TokenType::IF,
            "else" => TokenType::ELSE,
            "return" => TokenType::RETURN,
            _ => TokenType::ILLEGAL,
        };

        if ttype != TokenType::ILLEGAL {
            return ttype;
        }

        if Lexer::is_identifier(input) {
            return TokenType::IDENT;
        }

        if Lexer::is_number(input) {
            return TokenType::INT;
        }

        return TokenType::ILLEGAL;
    }
}

pub struct LexerIterator<'a> {
    index: usize,
    lexer: &'a Lexer,
}

impl<'a> Iterator for LexerIterator<'a> {
    type Item = &'a str;


    fn next(&mut self) -> Option<&'a str> {
        let input = &self.lexer.input;
        let size = input.len();

        while self.index < size && input.chars().nth(self.index).unwrap().is_ascii_whitespace() {
            self.index += 1;
        }

        if self.index >= size {
            return None;
        }

        let start = self.index;

        // Identifiers and keywords
        if input.chars().nth(self.index).unwrap().is_alphabetic() {
            while self.index < size && (input.chars().nth(self.index).unwrap().is_alphanumeric() ||
                                        input.chars().nth(self.index).unwrap() == '_') {
                self.index += 1;
            }

            if start < self.index {
                return Some(&input[start..self.index])
            }
        }

        // Numbers
        if input.chars().nth(self.index).unwrap().is_ascii_digit() {
            while self.index < size && (input.chars().nth(self.index).unwrap().is_ascii_digit()) {
                self.index += 1;
            }

            if start < self.index {
                return Some(&input[start..self.index])
            }
        }

        self.index += 1;
        return Some(&input[start..self.index]);
    }
}

