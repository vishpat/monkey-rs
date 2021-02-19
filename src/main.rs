mod lexer;

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

fn main() {
    let mut lexer = lexer::Lexer::new(TEST_STR);
    for t in lexer.iter() {
        println!("{:?}", t);
    }
}
