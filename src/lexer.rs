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