use std::path::{Path, PathBuf};
use std::convert::TryFrom;

use crate::tokenizer::{Token, TokenStream};
use crate::vm::{Value, Block, Op};
use crate::error::{Error, ErrorKind};

macro_rules! nextable_enum {
    ( $name:ident { $( $thing:ident ),* } ) => {
        #[derive(PartialEq, PartialOrd, Clone, Copy, Debug)]
        enum $name {
            $( $thing, )*
        }

        impl $name {
            pub fn next(&self) -> Self {
                *[$( $name::$thing, )*].iter()
                    .find(|x| { x > &self })
                    .unwrap_or(self)
            }
        }
    };
}

macro_rules! error {
    ($thing:expr, $msg:expr) => {
        $thing.error(ErrorKind::SyntaxError($thing.line(), $thing.peek()), Some(String::from($msg)))
    };
}

macro_rules! expect {
    ($thing:expr, $exp:pat, $msg:expr) => {
        match $thing.peek() {
            $exp => { $thing.eat(); },
            _ => error!($thing, $msg),
        }
    };
}

nextable_enum!(Prec {
    No,
    Assert,
    Bool,
    Comp,
    Term,
    Factor
});

enum Type {
    UnkownType,
    Int,
    Float,
    Bool,
}

impl TryFrom<&str> for Type {
    type Error = ();

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "int" => Ok(Type::Int),
            "float" => Ok(Type::Float),
            "bool" => Ok(Type::Bool),
            _ => Err(()),
        }
    }
}

struct Variable {
    name: String,
    typ: Type,
}

struct Compiler {
    curr: usize,
    tokens: TokenStream,
    current_file: PathBuf,

    stack: Vec<Variable>,

    panic: bool,
    errors: Vec<Error>,
}

impl Compiler {
    pub fn new(current_file: &Path, tokens: TokenStream) -> Self {
        Self {
            curr: 0,
            tokens,
            current_file: PathBuf::from(current_file),

            stack: vec![],

            panic: false,
            errors: vec![],
        }
    }

    fn clear_panic(&mut self) {
        if self.panic {
            self.panic = false;

            while match self.peek() {
                Token::EOF | Token::Newline => false,
                _ => true,
            } {
                self.eat();
            }
            self.eat();
        }
    }

    fn error(&mut self, kind: ErrorKind, message: Option<String>) {
        if self.panic { return }
        self.panic = true;
        self.errors.push(Error {
            kind: kind,
            file: self.current_file.clone(),
            line: self.line(),
            message: message,
        });
    }

    fn peek(&self) -> Token {
        self.peek_at(0)
    }

    fn peek_at(&self, at: usize) -> Token {
        if self.tokens.len() <= self.curr + at {
            crate::tokenizer::Token::EOF
        } else {
            self.tokens[self.curr + at].0.clone()
        }
    }

    fn peek_to<const N: usize>(&self) -> [Token; N] {
        let mut ret = [(); N].map(|_| Token::EOF);
        for (i, t) in ret.iter_mut().enumerate() {
            *t = self.peek_at(i);
        }
        ret
    }

    fn eat(&mut self) -> Token {
        let t = self.peek();
        self.curr += 1;
        t
    }

    fn precedence(&self, token: Token) -> Prec {
        match token {
            Token::Star | Token::Slash => Prec::Factor,

            Token::Minus | Token::Plus => Prec::Term,

            Token::EqualEqual
                | Token::Greater
                | Token::GreaterEqual
                | Token::Less
                | Token::LessEqual
                | Token::NotEqual
                => Prec::Comp,

            Token::And | Token::Or => Prec::Bool,

            Token::AssertEqual => Prec::Assert,

            _ => Prec::No,
        }
    }

    fn line(&self) -> usize {
        if self.curr < self.tokens.len() {
            self.tokens[self.curr].1
        } else {
            self.tokens[self.tokens.len() - 1].1
        }
    }

    fn prefix(&mut self, token: Token, block: &mut Block) -> bool {
        match token {
            Token::Identifier(_) => self.variable_expression(block),
            Token::LeftParen => self.grouping(block),
            Token::Minus => self.unary(block),

            Token::Float(_) => self.value(block),
            Token::Int(_) => self.value(block),
            Token::Bool(_) => self.value(block),

            Token::Not => self.unary(block),

            _ => { return false; },
        }
        return true;
    }


    fn infix(&mut self, token: Token, block: &mut Block) -> bool {
        match token {
            Token::Minus
                | Token::Plus
                | Token::Slash
                | Token::Star
                | Token::AssertEqual
                | Token::EqualEqual
                | Token::Greater
                | Token::GreaterEqual
                | Token::Less
                | Token::LessEqual
                | Token::NotEqual
                => self.binary(block),

            _ => { return false; },
        }
        return true;
    }

    fn value(&mut self, block: &mut Block) {
        let value = match self.eat() {
            Token::Float(f) => { Value::Float(f) },
            Token::Int(i) => { Value::Int(i) }
            Token::Bool(b) => { Value::Bool(b) }
            _ => { error!(self, "Cannot parse value."); Value::Bool(false) }
        };
        block.add(Op::Constant(value), self.line());
    }

    fn grouping(&mut self, block: &mut Block) {
        expect!(self, Token::LeftParen, "Expected '(' around expression.");

        self.expression(block);

        expect!(self, Token::RightParen, "Expected ')' around expression.");
    }

    fn unary(&mut self, block: &mut Block) {
        let op = match self.eat() {
            Token::Minus => Op::Neg,
            Token::Not => Op::Not,
            _ => { error!(self, "Invalid unary operator"); Op::Neg },
        };
        self.parse_precedence(block, Prec::Factor);
        block.add(op, self.line());
    }

    fn binary(&mut self, block: &mut Block) {
        let op = self.eat();

        self.parse_precedence(block, self.precedence(op.clone()).next());

        let op: &[Op] = match op {
            Token::Plus => &[Op::Add],
            Token::Minus => &[Op::Sub],
            Token::Star => &[Op::Mul],
            Token::Slash => &[Op::Div],
            Token::AssertEqual => &[Op::AssertEqual],
            Token::EqualEqual => &[Op::Equal],
            Token::Less => &[Op::Less],
            Token::Greater => &[Op::Greater],
            Token::NotEqual => &[Op::Equal, Op::Not],
            Token::LessEqual => &[Op::Greater, Op::Not],
            Token::GreaterEqual => &[Op::Less, Op::Not],
            _ => { error!(self, "Illegal operator"); &[] }
        };
        block.add_from(op, self.line());
    }

    fn expression(&mut self, block: &mut Block) {
        self.parse_precedence(block, Prec::No);
    }

    fn parse_precedence(&mut self, block: &mut Block, precedence: Prec) {
        if !self.prefix(self.peek(), block) {
            error!(self, "Invalid expression.");
        }

        while precedence <= self.precedence(self.peek()) {
            if !self.infix(self.peek(), block) {
                break;
            }
        }
    }

    fn find_local(&self, name: &str, block: &Block) -> Option<usize> {
        self.stack.iter()
                  .rev()
                  .enumerate()
                  .find_map(|x| if x.1.name == name { Some(x.0) } else { None} )
    }

    fn variable_expression(&mut self, block: &mut Block) {
        let name = match self.eat() {
            Token::Identifier(name) => name,
            _ => unreachable!(),
        };
        if let Some(id) = self.find_local(&name, block) {
            block.add(Op::ReadLocal(id), self.line());
        } else {
            error!(self, format!("Using undefined variable {}.", name));
        }
    }

    fn define_variable(&mut self, name: &str, typ: Type, block: &mut Block) {

        if self.find_local(&name, block).is_some() {
            error!(self, format!("Multiple definitions of {}.", name));
            return;
        }

        self.expression(block);

        self.stack.push(Variable { name: String::from(name), typ });

        // block.add(Op::Assign(self.stack.len() - 1), self.line());
    }

    fn statement(&mut self, block: &mut Block) {
        self.clear_panic();

        if let [Token::Print] = self.peek_to() {
            self.eat();
            self.expression(block);
            block.add(Op::Print, self.line());
        } else if let [
            Token::Identifier(name),
            Token::Identifier(typ),
            Token::ColonEqual
        ] = self.peek_to() {
            self.eat();
            self.eat();
            self.eat();
            if let Ok(typ) = Type::try_from(typ.as_ref()) {
                self.define_variable(&name, typ, block);
            } else {
                error!(self, format!("Failed to parse type '{}'.", typ));
            }
        } else if let [
            Token::Identifier(name),
            Token::ColonEqual
        ] = self.peek_to() {
            self.eat();
            self.eat();
            self.define_variable(&name, Type::UnkownType, block);
        } else {
            self.expression(block);
            block.add(Op::Pop, self.line());
        }
        expect!(self, Token::Newline, "Expect newline after expression.");
    }

    pub fn compile(&mut self, name: &str, file: &Path) -> Result<Block, Vec<Error>> {
        let mut block = Block::new(name, file);

        while self.peek() != Token::EOF {
            self.statement(&mut block);
        }
        block.add(Op::Return, self.line());

        if self.errors.is_empty() {
            Ok(block)
        } else {
            Err(self.errors.clone())
        }
    }
}

pub fn compile(name: &str, file: &Path, tokens: TokenStream) -> Result<Block, Vec<Error>> {
    Compiler::new(file, tokens).compile(name, file)
}
