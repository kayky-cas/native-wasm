#![allow(unused)]

use std::{
    env, fs,
    io::{stdout, Read, Write},
    num::NonZeroUsize,
    process::exit,
    str,
    vec::IntoIter,
};

use anyhow::Context;

#[derive(Debug, PartialEq)]
enum Token {
    Int(u32),
    Dot,
    Plus,
    Equal,
    If,
    End,
    QuadDots,
    While,
    Then,
    Less,
    Greater,
    Slash,
}

struct Lexer<'a> {
    buf: &'a [u8],
    position: usize,
}

impl<'a> Lexer<'a> {
    fn new(buf: &'a [u8]) -> Self {
        Self { buf, position: 0 }
    }

    fn skip_whitespace(&mut self) {
        while self
            .peak_byte()
            .map(|b| b.is_ascii_whitespace())
            .unwrap_or(false)
        {
            self.next_byte();
        }
    }

    fn next_byte(&mut self) -> Option<u8> {
        let byte = self.peak_byte()?;
        self.position += 1;
        Some(byte)
    }

    fn peak_byte(&self) -> Option<u8> {
        if self.position >= self.buf.len() {
            None
        } else {
            let byte = self.buf[self.position];
            Some(byte)
        }
    }

    fn skip_until_next_line(&mut self) {
        while self.peak_byte().map(|b| b != b'\n').unwrap_or(false) {
            self.next_byte();
        }
        self.next_byte();
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.skip_whitespace();
        let token = match self.peak_byte()? {
            b'.' => Token::Dot,
            b'0'..=b'9' => {
                let start = self.position;

                while self
                    .peak_byte()
                    .map(|b| b.is_ascii_digit())
                    .unwrap_or(false)
                {
                    self.next_byte();
                }

                let integer: u32 = str::from_utf8(&self.buf[start..self.position])
                    .expect("all input should be UTF-8")
                    .parse()
                    .expect("my algorithm is correct!!!");

                Token::Int(integer)
            }
            b'+' => Token::Plus,
            b'=' => Token::Equal,
            b'<' => Token::Less,
            b'>' => Token::Greater,
            b'/' => {
                let _ = self.next_byte();

                if self.peak_byte()? == b'/' {
                    self.skip_until_next_line();
                    self.next()?
                } else {
                    Token::Slash
                }
            }
            b':' => {
                let _ = self.next_byte();

                if self.peak_byte()? != b':' {
                    self.next_byte();
                    return None;
                }

                Token::QuadDots
            }
            b'a'..=b'z' | b'A'..=b'Z' => {
                let start = self.position;

                while self
                    .peak_byte()
                    .map(|b| b.is_ascii_alphabetic())
                    .unwrap_or(false)
                {
                    self.next_byte();
                }

                match str::from_utf8(&self.buf[start..self.position])
                    .expect("all input should be UTF-8")
                {
                    "if" => Token::If,
                    "while" => Token::While,
                    "then" => Token::Then,
                    "end" => Token::End,
                    ident => unreachable!("invalid identifier {ident}"),
                }
            }
            b => unreachable!("invalid token {token}", token = b as char),
        };

        self.next_byte();

        Some(token)
    }
}

#[derive(Debug, PartialEq)]
enum Operation {
    Push(u32),
    Dump,
    Plus,
    Equal,
    If(Option<usize>),
    End(Option<usize>),
    Dup,
    While,
    Then(Option<usize>),
    Less,
    Greater,
    Division,
}

struct Parser<I: Iterator<Item = Token>> {
    tokens: I,
}

impl<I: Iterator<Item = Token>> Parser<I> {
    fn new(tokens: I) -> Self {
        Self { tokens }
    }
}

impl<I> Iterator for Parser<I>
where
    I: Iterator<Item = Token>,
{
    type Item = Operation;

    fn next(&mut self) -> Option<Self::Item> {
        let op = match self.tokens.next()? {
            Token::Int(integer) => Operation::Push(integer),
            Token::Dot => Operation::Dump,
            Token::Plus => Operation::Plus,
            Token::Slash => Operation::Division,
            Token::Equal => Operation::Equal,
            Token::If => Operation::If(None),
            Token::End => Operation::End(None),
            Token::QuadDots => Operation::Dup,
            Token::While => Operation::While,
            Token::Then => Operation::Then(None),
            Token::Less => Operation::Less,
            Token::Greater => Operation::Greater,
        };

        Some(op)
    }
}

struct BlockParser {
    operations: IntoIter<Operation>,
}

impl BlockParser {
    fn new<I: Iterator<Item = Operation>>(tokens: I) -> Self {
        let mut operations: Vec<_> = tokens.collect();

        let mut block_stack = Vec::new();
        let mut while_stack = Vec::new();

        for (idx, operation) in operations.iter_mut().enumerate() {
            match operation {
                Operation::While => {
                    while_stack.push(idx);
                }
                Operation::If(None) | Operation::Then(None) => {
                    block_stack.push(operation);
                }
                Operation::End(back @ None) => match block_stack.pop() {
                    Some(Operation::If(end_pos @ None)) => {
                        *end_pos = Some(idx);
                    }
                    Some(Operation::Then(end_pos @ None)) => {
                        *end_pos = Some(idx);
                        *back = while_stack.pop();
                    }

                    Some(_) => {
                        unreachable!("Invalid block");
                    }
                    None => panic!("ERROR: Unmatched `end`"),
                },
                Operation::End(Some(_)) => unreachable!(),
                _ => {}
            }
        }

        Self {
            operations: operations.into_iter(),
        }
    }
}

impl Iterator for BlockParser {
    type Item = Operation;

    fn next(&mut self) -> Option<Self::Item> {
        self.operations.next()
    }
}

trait Compiler {
    fn compile<I: Iterator<Item = Operation>>(operations: I) -> anyhow::Result<()>;
}

struct Simulator;

impl Compiler for Simulator {
    fn compile<I: Iterator<Item = Operation>>(operations: I) -> anyhow::Result<()> {
        let mut operations: Vec<_> = operations.collect();
        let mut stack: Vec<usize> = Vec::new();

        let mut idx = 0;

        while idx < operations.len() {
            match operations[idx] {
                Operation::Push(integer) => stack.push(integer as usize),
                Operation::Dump => {
                    let x = stack.pop().unwrap();
                    println!("{x}")
                }
                Operation::Plus => {
                    let x = stack.pop().unwrap();
                    let y = stack.pop().unwrap();

                    stack.push(x + y);
                }
                Operation::Division => {
                    let y = stack.pop().unwrap();
                    let x = stack.pop().unwrap();

                    stack.push(x / y);
                    stack.push(x % y);
                }
                Operation::Equal => {
                    let x = stack.pop().unwrap();
                    let y = stack.pop().unwrap();

                    stack.push((x == y) as usize);
                }
                Operation::Less => {
                    let y = stack.pop().unwrap();
                    let x = stack.pop().unwrap();

                    stack.push((x < y) as usize);
                }
                Operation::Greater => {
                    let y = stack.pop().unwrap();
                    let x = stack.pop().unwrap();

                    stack.push((x > y) as usize);
                }
                Operation::Then(None) => unreachable!(),
                Operation::If(None) => unreachable!(),
                Operation::Then(Some(end_pos)) | Operation::If(Some(end_pos)) => {
                    let x = stack.pop().unwrap();

                    if x == 0 {
                        idx = end_pos;
                    }
                }
                Operation::End(None) => {}
                Operation::End(Some(while_idx)) => idx = while_idx,
                Operation::Dup => {
                    let x = stack.pop().unwrap();
                    stack.push(x);
                    stack.push(x);
                }
                Operation::While => {}
            }

            idx += 1;
        }

        Ok(())
    }
}

struct Compiler86x64;

impl Compiler for Compiler86x64 {
    fn compile<I: Iterator<Item = Operation>>(operations: I) -> anyhow::Result<()> {
        let mut operations: Vec<_> = operations.collect();
        let mut file = stdout();

        writeln!(file, "section .data").context("writing on file")?;
        writeln!(file, "dump_buf times 32 db 0").context("writing on file")?;

        writeln!(file, "section .text").context("writing on file")?;
        writeln!(file, "global _start").context("writing on file")?;

        writeln!(file, "dump:").context("writing on file")?;
        writeln!(file, "\tmov rax, rdi").context("writing on file")?;
        writeln!(file, "\tmov rbx, dump_buf").context("writing on file")?;
        writeln!(file, "\tadd rbx, 31").context("writing on file")?;
        writeln!(file, "\tmov byte [rbx], 10 ").context("writing on file")?;
        writeln!(file, "\tmov rcx, 10").context("writing on file")?;
        writeln!(file, "LP_DUMP:").context("writing on file")?;
        writeln!(file, "\tsub rbx, 1").context("writing on file")?;
        writeln!(file, "\txor rdx, rdx  ").context("writing on file")?;
        writeln!(file, "\tdiv rcx").context("writing on file")?;
        writeln!(file, "\tadd rdx, 48").context("writing on file")?;
        writeln!(file, "\tmov byte [rbx], dl ").context("writing on file")?;
        writeln!(file, "\ttest rax, rax").context("writing on file")?;
        writeln!(file, "\tjnz LP_DUMP").context("writing on file")?;
        writeln!(file, "\tmov rax, 1").context("writing on file")?;
        writeln!(file, "\tmov rdi, 1").context("writing on file")?;
        writeln!(file, "\tmov rsi, rbx").context("writing on file")?;
        writeln!(file, "\tsub rbx, dump_buf").context("writing on file")?;
        writeln!(file, "\tmov rdx, rbx").context("writing on file")?;
        writeln!(file, "\tsyscall").context("writing on file")?;
        writeln!(file, "\tret").context("writing on file")?;

        writeln!(file, "_start:").context("writing on file")?;

        let mut idx = 0;

        while idx < operations.len() {
            match operations[idx] {
                Operation::Push(integer) => {
                    writeln!(file, "\t;; PUSH ;;").context("writing on file")?;
                    writeln!(file, "\tpush {integer}").context("writing on file")?;
                }
                Operation::Plus => {
                    writeln!(file, "\t;; PLUS ;;").context("writing on file")?;
                    writeln!(file, "\tpop rax").context("writing on file")?;
                    writeln!(file, "\tpop rbx").context("writing on file")?;
                    writeln!(file, "\tadd rax, rbx").context("writing on file")?;
                    writeln!(file, "\tpush rax").context("writing on file");
                }
                Operation::Division => {
                    writeln!(file, "\t;; DIVISION ;;").context("writing on file")?;
                    writeln!(file, "\tpop rcx").context("writing on file")?;
                    writeln!(file, "\tpop rax").context("writing on file")?;
                    writeln!(file, "\txor rdx, rdx").context("writing on file");
                    writeln!(file, "\tdiv rcx").context("writing on file")?;
                    writeln!(file, "\tpush rax").context("writing on file");
                    writeln!(file, "\tpush rdx").context("writing on file");
                }
                Operation::Equal => {
                    writeln!(file, "\t;; EQUAL ;;").context("writing on file")?;
                    writeln!(file, "\tpop rbx").context("writing on file")?;
                    writeln!(file, "\tpop rax").context("writing on file")?;
                    writeln!(file, "\tcmp rax, rbx").context("writing on file")?;
                    writeln!(file, "\tsete al").context("writing on file")?;
                    writeln!(file, "\tmovzx rax, al").context("writing on file")?;
                    writeln!(file, "\tpush rax").context("writing on file");
                }
                Operation::Less => {
                    writeln!(file, "\t;; Less ;;").context("writing on file")?;
                    writeln!(file, "\tpop rbx").context("writing on file")?;
                    writeln!(file, "\tpop rax").context("writing on file")?;
                    writeln!(file, "\tcmp rax, rbx").context("writing on file")?;
                    writeln!(file, "\tsetl al").context("writing on file")?;
                    writeln!(file, "\tmovzx rax, al").context("writing on file")?;
                    writeln!(file, "\tpush rax").context("writing on file");
                }
                Operation::Greater => {
                    writeln!(file, "\t;; Greater ;;").context("writing on file")?;
                    writeln!(file, "\tpop rbx").context("writing on file")?;
                    writeln!(file, "\tpop rax").context("writing on file")?;
                    writeln!(file, "\tcmp rax, rbx").context("writing on file")?;
                    writeln!(file, "\tsetg al").context("writing on file")?;
                    writeln!(file, "\tmovzx rax, al").context("writing on file")?;
                    writeln!(file, "\tpush rax").context("writing on file");
                }
                Operation::Dump => {
                    writeln!(file, "\t;; DUMP ;;").context("writing on file")?;
                    writeln!(file, "\tpop rdi").context("writing on file")?;
                    writeln!(file, "\tcall dump").context("writing on file")?;
                }
                Operation::If(None) => unreachable!(),
                Operation::If(Some(end_pos)) => {
                    writeln!(file, "\t;; IF ;;").context("writing on file")?;
                    writeln!(file, "\tpop rax").context("writing on file")?;
                    writeln!(file, "\ttest rax, rax").context("writing on file")?;
                    writeln!(file, "\tjz END_{end_pos}").context("writing on file")?;
                }
                Operation::Then(None) => unreachable!(),
                Operation::Then(Some(end_pos)) => {
                    writeln!(file, "\t;; WHILE THEN ;;").context("writing on file")?;
                    writeln!(file, "\tpop rax").context("writing on file")?;
                    writeln!(file, "\ttest rax, rax").context("writing on file")?;
                    writeln!(file, "\tjz END_{end_pos}").context("writing on file")?;
                }
                Operation::End(None) => {
                    writeln!(file, "END_{idx}:").context("writing on file")?;
                }
                Operation::End(Some(while_idx)) => {
                    writeln!(file, "\tjmp L{while_idx}").context("writing on file")?;
                    writeln!(file, "END_{idx}:").context("writing on file")?;
                }
                Operation::Dup => {
                    writeln!(file, "\tpop rax").context("writing on file")?;
                    writeln!(file, "\tpush rax").context("writing on file")?;
                    writeln!(file, "\tpush rax").context("writing on file")?;
                }
                Operation::While => {
                    writeln!(file, "L{idx}:").context("writing on file")?;
                }
            }
            idx += 1;
        }

        writeln!(file, "\tpop rdi").context("writing on file");
        writeln!(file, "\tmov rax, 60").context("writing on file");
        writeln!(file, "\tsyscall").context("writing on file");

        Ok(())
    }
}

fn main() -> anyhow::Result<()> {
    let mut args = env::args();

    let _program_name = args
        .next()
        .expect("the first argument pass to a program must be the executable name");

    let Some(mode) = args.next() else {
        eprintln!("ERROR: Compile mode was not privided");
        exit(1)
    };

    let Some(file_name) = args.next() else {
        eprintln!("ERROR: File name was not provided");
        exit(1)
    };

    let Ok(mut file) = fs::File::open(&file_name) else {
        eprintln!("ERROR: Not possible to load the file {file_name}");
        exit(1)
    };

    let mut input = String::new();

    let Ok(n) = file.read_to_string(&mut input) else {
        eprintln!("ERROR: Not possible to read the file {file_name}");
        exit(1)
    };

    assert_eq!(input.len(), n);

    let lexer = Lexer::new(input.as_bytes());
    let parser = Parser::new(lexer);

    let parser = BlockParser::new(parser);

    match mode.as_str() {
        "sim" => Simulator::compile(parser),
        "com" => Compiler86x64::compile(parser),
        _ => {
            eprintln!("ERROR: Invalid mode {mode}");
            exit(1)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Lexer, Operation, Parser, Token};

    #[test]
    fn test_simple_lexing() {
        let input = "25 10 .";
        let expect = vec![Token::Int(25), Token::Int(10), Token::Dot];

        let lexer = Lexer::new(input.as_bytes());

        assert_eq!(lexer.collect::<Vec<_>>(), expect)
    }

    #[test]
    fn test_simple_parsing() {
        let input = vec![Token::Int(25), Token::Int(10), Token::Dot];
        let expect = vec![Operation::Push(25), Operation::Push(10), Operation::Dump];

        let parser = Parser::new(input.into_iter());

        assert_eq!(parser.collect::<Vec<_>>(), expect)
    }
}
