#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    Illegal,
    Eof,

    // Identifiers + Literals
    Ident(String),
    Int(usize),

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
    type Item = Token;


    fn next(&mut self) -> Option<Token> {

        let input = &self.lexer.input;
        let size = input.len();

        while self.index < size && input.chars().nth(self.index).unwrap().is_ascii_whitespace() {
            self.index += 1;
        }

        if self.index >= size {
            return None
        }

        let start = self.index;

        let mut token = match input.chars().nth(self.index).unwrap() {
            '=' => Token::Eq,
            ';' => Token::Semicolon,
            '(' => Token::LParen,
            ')' => Token::RParen,
            ',' => Token::Comma,
            '+' => Token::Plus,
            '{' => Token::LBrace,
            '}' => Token::RBrace,
            '>'  => Token::Gt,
            '<'  => Token::Lt,
            '*'  => Token::Asterik,
            '-'  => Token::Minus,
            '/'  => Token::Slash,
            '!'  => Token::Bang,
            _ => Token::Illegal
        };

        if token != Token::Illegal {
            self.index += 1;
            return Some(token);
        }

        // Identifiers and keywords
        if input.chars().nth(self.index).unwrap().is_alphabetic() {
            while self.index < size && (input.chars().nth(self.index).unwrap().is_alphanumeric() ||
                input.chars().nth(self.index).unwrap() == '_') {
                self.index += 1;
            }

            if start < self.index {
                let s = match &input[start..self.index] {
                    "let" => Token::Let,
                    "true" => Token::True,
                    "false" => Token::False,
                    "if" => Token::If,
                    "else" => Token::Else,
                    "return" => Token::Return,
                    "fn" => Token::Function,
                    _ => Token::Ident(input[start..self.index].to_string())
                };
                return Some(s);
            }
        }

        // Numbers
        if input.chars().nth(self.index).unwrap().is_ascii_digit() {
            while self.index < size && (input.chars().nth(self.index).unwrap().is_ascii_digit()) {
                self.index += 1;
            }

            if start < self.index {
                return Some(Token::Int(input[start..self.index].to_string().parse::<usize>().unwrap()))
            }
        }

        // == !=
        if size - start >= 2 &&
            input.chars().nth(self.index + 1).unwrap() == '=' &&
            (input.chars().nth(self.index).unwrap() == '=' ||
                input.chars().nth(self.index).unwrap() == '!') {
            self.index += 2;

            return match &input[start..self.index] {
                "==" => Some(Token::Eq),
                "!=" => Some(Token::NotEq),
                _ => panic!("Invalid string {}", &input[start..self.index])
            }
        }

       panic!("Invalid character found at {} {}", self.lexer.input, self.index);
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
    ";



    #[test]
    fn test_tokens() {

        let test_token_vec: Vec<Box<Token>> = vec![
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
            Token::new(TokenType::LBrace, String::from("{")),
            Token::new(TokenType::Ident, String::from("x")),
            Token::new(TokenType::Plus, String::from("+")),
            Token::new(TokenType::Ident, String::from("y")),
            Token::new(TokenType::Semicolon, String::from(";")),
            Token::new(TokenType::RBrace, String::from("}")),
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
            Token::new(TokenType::LBrace, String::from("{")),
            Token::new(TokenType::Return, String::from("return")),
            Token::new(TokenType::True, String::from("true")),
            Token::new(TokenType::Semicolon, String::from(";")),
            Token::new(TokenType::RBrace, String::from("}")),
            Token::new(TokenType::Else, String::from("else")),
            Token::new(TokenType::LBrace, String::from("{")),
            Token::new(TokenType::Return, String::from("return")),
            Token::new(TokenType::False, String::from("false")),
            Token::new(TokenType::Semicolon, String::from(";")),
            Token::new(TokenType::RBrace, String::from("}")),
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

        let mut lexer = Lexer::new(TEST_STR);
        let mut tokens: Vec<Box<Token>> = lexer.iter().map(|token| Token::new(
            lexer.token_type(token),
            String::from(token))
        ).collect();
        tokens.push(Token::new(TokenType::Eof, String::from("")));

        assert_eq!(tokens.len(), test_token_vec.len());

        for i in 0..tokens.len() {
            let t1 = &tokens[i];
            let t2 = &test_token_vec[i];
            assert_eq!(t1.literal, t2.literal);
            assert_eq!(t1.tipe, t2.tipe);
        }
    }
}