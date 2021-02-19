use crate::lexer::{Lexer, Token, TokenType};

mod lexer;

const test_str: &str = "
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


fn main() {
    let mut l  = Lexer::new(test_str);
    for s in l.iter() {
        println!("{}", s);
    }
}
