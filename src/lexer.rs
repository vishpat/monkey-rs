#[derive(Debug)]
pub struct Lexer {
    input: String,
    position: usize,
    read_position: usize,
    ch: u8,
}

impl Lexer {
    pub fn new(input: &str) -> Box<Lexer> {
        Box::new(Lexer{
            input: String::from(input),
            position: 0,
            read_position: 0,
            ch: 0
        })
    }
}