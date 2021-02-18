use crate::lexer::Lexer;

mod lexer;

fn main() {
    let mut l  = Lexer::new("x + y");
    for token in l.iter() {
        println!("{:?}", token);
    }
}
