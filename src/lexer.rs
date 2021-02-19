#[derive(PartialEq)]
pub enum TokenType {
    Illegal,
    Eof,

    // Identifiers + Literals
    Ident,
    Int,

    // Operators
    Assign,
    Plus,
    Bang,
    Minus,
    Slash,
    Asterik,
    Lt,
    Gt,
    Eq,
    NotEq,

    // Delimiters
    Comma,
    Semicolon,

    LParen,
    RParen,
    LBrace,
    RBrace,

    // Keywords
    Function,
    Let,
    True,
    False,
    If,
    Else,
    Return,
}

pub struct Token {
    pub tipe: TokenType,
    pub literal: String,
}

impl Token {
    pub fn new(token_type: TokenType, literal: String) -> Box<Token> {
        Box::new(Token {
            tipe: token_type,
            literal,
        })
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

    pub fn token_type(&self, input: &str) -> TokenType {
        let ttype = match input {
            "=" => TokenType::Assign,
            ";" => TokenType::Semicolon,
            "(" => TokenType::LParen,
            ")" => TokenType::RParen,
            "," => TokenType::Comma,
            "+" => TokenType::PLUS,
            "{" => TokenType::LBrace,
            "}" => TokenType::RBrace,
            "fn" => TokenType::Function,
            "let" => TokenType::Let,
            "true" => TokenType::True,
            "false" => TokenType::False,
            "if" => TokenType::If,
            "else" => TokenType::Else,
            "return" => TokenType::Return,
            _ => TokenType::ILLEGAL,
        };

        if ttype != TokenType::ILLEGAL {
            return ttype;
        }

        if Lexer::is_identifier(input) {
            return TokenType::Ident;
        }

        if Lexer::is_number(input) {
            return TokenType::Int;
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
                return Some(&input[start..self.index]);
            }
        }

        // Numbers
        if input.chars().nth(self.index).unwrap().is_ascii_digit() {
            while self.index < size && (input.chars().nth(self.index).unwrap().is_ascii_digit()) {
                self.index += 1;
            }

            if start < self.index {
                return Some(&input[start..self.index]);
            }
        }

        // == !=
        if size - start >= 2 &&
            input.chars().nth(self.index + 1).unwrap() == '=' &&
            (input.chars().nth(self.index).unwrap() == '=' ||
                input.chars().nth(self.index).unwrap() == '!') {
            self.index += 2;
            return Some(&input[start..self.index]);
        }

        self.index += 1;
        return Some(&input[start..self.index]);
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::{Lexer, Token, TokenType};

    const TEST_STR: &str = "
    let five = 5;
    let ten = 10;

    let add = fn(x, y) {
      x + y;
    };

    let result = add(five, ten);
    !-/*5;
    5 < 10 > 5;

    if (5 < 10) {
      return true;
    } else {
      return false;
    }

    10 == 10;
    10 != 9;
    34 == 23;
    ";

    const TOKEN_VEC: Vec<Box<Token>> = vec![
        Token::new(TokenType::Int, String::from("1")),
        Token::new(TokenType::Let, String::from("let")),
        Token::new(TokenType::Ident, String::from("five")),
        Token::new(TokenType::Assign, String::from("=")),
        Token::new(TokenType::Int, String::from("5")),
        Token::new(TokenType::Semicolon, String::from(";")),
        Token::new(TokenType::Let, String::from("let")),
        Token::new(TokenType::Ident, String::from("ten")),
        Token::new(TokenType::Assign, String::from("=")),
        Token::new(TokenType::Int, String::from("10")),
        Token::new(TokenType::Semicolon, String::from(";")),
        Token::new(TokenType::Let, String::from("let")),
        Token::new(TokenType::Ident, String::from("add")),
        Token::new(TokenType::Assign, String::from("=")),
        Token::new(TokenType::Function, String::from("fn")),
        Token::new(TokenType::LParen, String::from("(")),
        Token::new(TokenType::Ident, String::from("x")),
        Token::new(TokenType::Comma, String::from(",")),
        Token::new(TokenType::Ident, String::from("y")),
        Token::new(TokenType::RParen, String::from(")")),
        Token::new(TokenType::LBrace, String::from("(")),
        Token::new(TokenType::Ident, String::from("x")),
        Token::new(TokenType::Plus, String::from("+")),
        Token::new(TokenType::Ident, String::from("y")),
        Token::new(TokenType::Semicolon, String::from(";")),
        Token::new(TokenType::RBrace, String::from("))")),
        Token::new(TokenType::Semicolon, String::from(";")),
        Token::new(TokenType::Let, String::from("let")),
        Token::new(TokenType::Ident, String::from("result")),
        Token::new(TokenType::Assign, String::from("=")),
        Token::new(TokenType::Ident, String::from("add")),
        Token::new(TokenType::LParen, String::from("(")),
        Token::new(TokenType::Ident, String::from("five")),
        Token::new(TokenType::Comma, String::from(",")),
        Token::new(TokenType::Ident, String::from("ten")),
        Token::new(TokenType::RParen, String::from(")")),
        Token::new(TokenType::Semicolon, String::from(";")),
        Token::new(TokenType::Bang, String::from("!")),
        Token::new(TokenType::Minus, String::from("-")),
        Token::new(TokenType::Slash, String::from("/")),
        Token::new(TokenType::Asterik, String::from("*")),
        Token::new(TokenType::Int, String::from("5")),
        Token::new(TokenType::Semicolon, String::from(";")),
        Token::new(TokenType::Int, String::from("5")),
        Token::new(TokenType::Lt, String::from("<")),
        Token::new(TokenType::Int, String::from("10")),
        Token::new(TokenType::Gt, String::from(">")),
        Token::new(TokenType::Int, String::from("5")),
        Token::new(TokenType::Semicolon, String::from(";")),
        Token::new(TokenType::If, String::from("if")),
        Token::new(TokenType::LParen, String::from("(")),
        Token::new(TokenType::Int, String::from("5")),
        Token::new(TokenType::Lt, String::from("<")),
        Token::new(TokenType::Int, String::from("10")),
        Token::new(TokenType::RParen, String::from(")")),
        Token::new(TokenType::LBrace, String::from("Token::new(")),
        Token::new(TokenType::Return, String::from("return")),
        Token::new(TokenType::True, String::from("true")),
        Token::new(TokenType::Semicolon, String::from(";")),
        Token::new(TokenType::RBrace, String::from("))")),
        Token::new(TokenType::Else, String::from("else")),
        Token::new(TokenType::LBrace, String::from("Token::new(")),
        Token::new(TokenType::Return, String::from("return")),
        Token::new(TokenType::False, String::from("false")),
        Token::new(TokenType::Semicolon, String::from(";")),
        Token::new(TokenType::RBrace, String::from("))")),
        Token::new(TokenType::Int, String::from("10")),
        Token::new(TokenType::Eq, String::from("==")),
        Token::new(TokenType::Int, String::from("10")),
        Token::new(TokenType::Semicolon, String::from(";")),
        Token::new(TokenType::Int, String::from("10")),
        Token::new(TokenType::NotEq, String::from("!=")),
        Token::new(TokenType::Int, String::from("9")),
        Token::new(TokenType::Semicolon, String::from(";")),
        Token::new(TokenType::Eof, String::from("")),
    ];

    #[test]
    fn test_tokens() {
        let mut lexer = Lexer::new(TEST_STR);
        let mut tokens: Vec<Box<Token>> = lexer.iter().map(|token| Token::new(
            lexer.token_type(token),
            String::from(token))
        ).collect();
        tokens.push(Token::new(TokenType::Eof, String::from("")));

    }
}