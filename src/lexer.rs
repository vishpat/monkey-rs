use std::fmt;
use std::fmt::{Debug};

#[derive(Debug, PartialEq, Eq, Clone)]
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

fn token_str_repr(token: &Token) -> Box<String> {
    let str_repr= match token {
        Token::Illegal => String::from("Illegal"),
        Token::Eof => String::from("Eof"),

        // Identifiers + Literals
        Token::Ident(s) => s.clone(),
        Token::Int(i) => i.to_string(),

        // Operators
        Token::Assign => String::from("="),
        Token::Plus => String::from("+"),
        Token::Bang => String::from("!"),
        Token::Minus => String::from("-"),
        Token::Slash => String::from("/"),
        Token::Asterik => String::from("*"),
        Token::Lt => String::from("<"),
        Token::Gt => String::from(">"),
        Token::Eq => String::from("=="),
        Token::NotEq => String::from("!="),

        // Delimiters
        Token::Comma => String::from("),"),
        Token::Semicolon => String::from(";"),

        Token::LParen => String::from("("),
        Token::RParen => String::from(")"),
        Token::LBrace => String::from("{"),
        Token::RBrace => String::from("}"),

        // Keywords
        Token::Function => String::from("fn"),
        Token::Let => String::from("let"),
        Token::True => String::from("true"),
        Token::False => String::from("false"),
        Token::If => String::from("if"),
        Token::Else => String::from("else"),
        Token::Return => String::from("return"),
    };
    Box::new(str_repr)
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", token_str_repr(self))
    }
}


pub struct Lexer {
    tokens: Vec<Token>
}

impl Lexer {
    pub fn new(input: &str) -> Box<Lexer> {
        let mut tokens: Vec<Token> = vec![];

        let size = input.len();
        let mut index = 0;

        while index < size {

            while index < size && input.chars().nth(index).unwrap().is_ascii_whitespace() {
                index += 1;
            }

            if index >= size {
                break
            }


            let start = index;

            let mut token = match input.chars().nth(index).unwrap() {
                '=' => {
                    if size - index > 1 {
                        match input.chars().nth(index + 1).unwrap() {
                            '=' => {
                                index += 1;
                                Token::Eq
                            }
                            _ => Token::Assign
                        }
                    } else {
                        Token::Assign
                    }
                }
                ';' => Token::Semicolon,
                '(' => Token::LParen,
                ')' => Token::RParen,
                ',' => Token::Comma,
                '+' => Token::Plus,
                '{' => Token::LBrace,
                '}' => Token::RBrace,
                '>' => Token::Gt,
                '<' => Token::Lt,
                '*' => Token::Asterik,
                '-' => Token::Minus,
                '/' => Token::Slash,
                '!' => {
                    if size - index > 1 {
                        match input.chars().nth(index + 1).unwrap() {
                            '=' => {
                                index += 1;
                                Token::NotEq
                            }
                            _ => Token::Bang
                        }
                    } else {
                        Token::Bang
                    }
                }
                _ => Token::Illegal
            };

            if token != Token::Illegal {
                index += 1;
                tokens.push(token);
                continue;
            }

            // Identifiers and keywords
            if input.chars().nth(index).unwrap().is_alphabetic() {
                while index < size && (input.chars().nth(index).unwrap().is_alphanumeric() ||
                    input.chars().nth(index).unwrap() == '_') {
                    index += 1;
                }

                if start < index {
                    let s = match &input[start..index] {
                        "let" => Token::Let,
                        "true" => Token::True,
                        "false" => Token::False,
                        "if" => Token::If,
                        "else" => Token::Else,
                        "return" => Token::Return,
                        "fn" => Token::Function,
                        _ => Token::Ident(input[start..index].to_string())
                    };
                    tokens.push(s);
                }
            }

            // Numbers
            if input.chars().nth(index).unwrap().is_ascii_digit() {
                while index < size && (input.chars().nth(index).unwrap().is_ascii_digit()) {
                    index += 1;
                }

                if start < index {
                    tokens.push(Token::Int(input[start..index].to_string().parse::<usize>().unwrap()));
                }
            }
        }

        tokens.reverse();

        Box::new(Lexer {
            tokens
        })
    }

    pub fn next(&mut self) -> Token {
        self.tokens.pop().unwrap_or(Token::Eof)
    }

    pub fn peek(&mut self) -> Token {
        self.tokens.last().cloned().unwrap_or(Token::Eof)
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::{Lexer, Token};

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
        let test_token_vec: Vec<Token> = vec![
            Token::Let,
            Token::Ident(String::from("five")),
            Token::Assign,
            Token::Int(5),
            Token::Semicolon,
            Token::Let,
            Token::Ident(String::from("ten")),
            Token::Assign,
            Token::Int(10),
            Token::Semicolon,
            Token::Let,
            Token::Ident(String::from("add")),
            Token::Assign,
            Token::Function,
            Token::LParen,
            Token::Ident(String::from("x")),
            Token::Comma,
            Token::Ident(String::from("y")),
            Token::RParen,
            Token::LBrace,
            Token::Ident(String::from("x")),
            Token::Plus,
            Token::Ident(String::from("y")),
            Token::Semicolon,
            Token::RBrace,
            Token::Semicolon,
            Token::Let,
            Token::Ident(String::from("result")),
            Token::Assign,
            Token::Ident(String::from("add")),
            Token::LParen,
            Token::Ident(String::from("five")),
            Token::Comma,
            Token::Ident(String::from("ten")),
            Token::RParen,
            Token::Semicolon,
            Token::Bang,
            Token::Minus,
            Token::Slash,
            Token::Asterik,
            Token::Int(5),
            Token::Semicolon,
            Token::Int(5),
            Token::Lt,
            Token::Int(10),
            Token::Gt,
            Token::Int(5),
            Token::Semicolon,
            Token::If,
            Token::LParen,
            Token::Int(5),
            Token::Lt,
            Token::Int(10),
            Token::RParen,
            Token::LBrace,
            Token::Return,
            Token::True,
            Token::Semicolon,
            Token::RBrace,
            Token::Else,
            Token::LBrace,
            Token::Return,
            Token::False,
            Token::Semicolon,
            Token::RBrace,
            Token::Int(10),
            Token::Eq,
            Token::Int(10),
            Token::Semicolon,
            Token::Int(10),
            Token::NotEq,
            Token::Int(9),
            Token::Semicolon,
            Token::Eof,
        ];

        let mut lexer = Lexer::new(TEST_STR);
        let mut idx = 1;

        for test_token in test_token_vec.iter() {
            let token = lexer.next();
            assert_eq!(token, *test_token);
        }
    }
}