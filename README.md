# monkey-rs

Another interpreter for the [monkey](https://interpreterbook.com/) programming language in RUST. **Writing An Interpreter In Go** is a phenomenal book to learn on how to write an interpreter for a programming language in **Go**. However instead of using Go I decided to implement the interpreter in RUST. One big advantage of using RUST versus using other grabage collected languages such as Go, Python, Java etc is that the garbage collection of the monkey objects is completely handled by the RUST runtime hence theortically the performance of the Monkey programs is expected to be much better on RUST. 

# Demo
```
cargo build
```


[![asciicast](https://asciinema.org/a/403574.svg)](https://asciinema.org/a/403574)
