use crate::lexer::Lexer;

mod lexer;

fn main() {
    let l  = Lexer::new("x+y");
    println!("Lexer {:?}", l);
}
