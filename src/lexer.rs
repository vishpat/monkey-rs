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
            '=' => {
                if size - self.index > 1 {
                    match input.chars().nth(self.index + 1).unwrap() {
                        '=' => {
                            self.index += 1;
                            Token::Eq
                        },
                        _ => Token::Assign
                    }
                } else {
                    Token::Assign
                }
            },
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
            '!'  => {
                if size - self.index > 1 {
                    match input.chars().nth(self.index + 1).unwrap() {
                        '=' => {
                            self.index += 1;
                            Token::NotEq
                        },
                        _ => Token::Bang
                    }
                } else {
                    Token::Bang
                }
            },
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

       panic!("Invalid character found at {} {}", self.lexer.input, self.index);
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
        let mut tokens: Vec<Token> = lexer.iter().collect();
        tokens.push(Token::Eof);

        assert_eq!(tokens.len(), test_token_vec.len());

        for i in 0..tokens.len() {
            let t1 = &tokens[i];
            let t2 = &test_token_vec[i];
            println!("{}", i);
            assert_eq!(t1, t2);
        }
    }
}