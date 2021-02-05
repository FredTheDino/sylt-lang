use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt::Debug;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use owo_colors::OwoColorize;

use error::Error;
use tokenizer::TokenStream;

use crate::error::ErrorKind;

pub mod compiler;
pub mod error;
pub mod tokenizer;
pub mod vm;

pub fn run_file(path: &Path, print: bool, functions: Vec<(String, RustFunction)>) -> Result<(), Vec<Error>> {
    run(tokenizer::file_to_tokens(path), path, print, functions)
}

pub fn compile_file(path: &Path,
                    print: bool,
                    functions: Vec<(String, RustFunction)>
    ) -> Result<vm::VM, Vec<Error>> {
    let tokens = tokenizer::file_to_tokens(path);
    match compiler::compile("main", path, tokens, &functions) {
        Ok(prog) => {
            let mut vm = vm::VM::new().print_blocks(print).print_ops(print);
            vm.typecheck(&prog)?;
            vm.init(&prog);
            Ok(vm)
        }
        Err(errors) => Err(errors),
    }
}

pub fn run_string(s: &str, print: bool, functions: Vec<(String, RustFunction)>) -> Result<(), Vec<Error>> {
    run(tokenizer::string_to_tokens(s), Path::new("builtin"), print, functions)
}

pub fn run(tokens: TokenStream, path: &Path, print: bool, functions: Vec<(String, RustFunction)>) -> Result<(), Vec<Error>> {
    match compiler::compile("main", path, tokens, &functions) {
        Ok(prog) => {
            let mut vm = vm::VM::new().print_blocks(print).print_ops(print);
            vm.typecheck(&prog)?;
            vm.init(&prog);
            if let Err(e) = vm.run() {
                Err(vec![e])
            } else {
                Ok(())
            }
        }
        Err(errors) => Err(errors),
    }
}

pub type RustFunction = fn(&[Value], bool) -> Result<Value, ErrorKind>;

#[derive(Debug, Clone)]
pub enum Type {
    Void,
    UnknownType,
    Int,
    Float,
    Bool,
    String,
    Tuple(Vec<Type>),
    Function(Vec<Type>, Box<Type>),
    Blob(usize),
    BlobInstance(usize),
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Void, Type::Void) => true,
            (Type::BlobInstance(a), Type::BlobInstance(b)) => a == b,
            (Type::Blob(a), Type::Blob(b)) => a == b,
            (Type::Int, Type::Int) => true,
            (Type::Float, Type::Float) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::String, Type::String) => true,
            (Type::Tuple(a), Type::Tuple(b)) => {
                a.iter().zip(b.iter()).all(|(a, b)| a == b)
            }
            (Type::Function(a_args, a_ret), Type::Function(b_args, b_ret)) =>
                a_args == b_args && a_ret == b_ret,
            _ => false,
        }
    }
}

impl From<&Value> for Type {
    fn from(value: &Value) -> Type {
        match value {
            Value::BlobInstance(i, _) => Type::BlobInstance(*i),
            Value::Blob(i) => Type::Blob(*i),
            Value::Tuple(v) => {
                Type::Tuple(v.iter().map(|x| Type::from(x)).collect())
            }
            Value::Int(_) => Type::Int,
            Value::Float(_) => Type::Float,
            Value::Bool(_) => Type::Bool,
            Value::String(_) => Type::String,
            Value::Function(_, block) => block.borrow().ty.clone(),
            _ => Type::Void,
        }
    }
}

impl From<Value> for Type {
    fn from(value: Value) -> Type {
        Type::from(&value)
    }
}

impl Type {
    pub fn is_unkown(&self) -> bool {
        match self {
            Type::UnknownType => true,
            _ => false,
        }
    }
}

impl From<&Type> for Value {
    fn from(ty: &Type) -> Self {
        match ty {
            Type::Void => Value::Nil,
            Type::Blob(i) => Value::Blob(*i),
            Type::BlobInstance(i) => Value::BlobInstance(*i, Rc::new(RefCell::new(Vec::new()))),
            Type::Tuple(fields) => {
                Value::Tuple(Rc::new(fields.iter().map(Value::from).collect()))
            }
            Type::UnknownType => Value::Unkown,
            Type::Int => Value::Int(1),
            Type::Float => Value::Float(1.0),
            Type::Bool => Value::Bool(true),
            Type::String => Value::String(Rc::new("".to_string())),
            Type::Function(_, _) => Value::Function(
                Vec::new(),
                Rc::new(RefCell::new(Block::empty_with_type(ty)))),
        }
    }
}

impl From<Type> for Value {
    fn from(ty: Type) -> Self {
        Value::from(&ty)
    }
}


#[derive(Clone)]
pub enum Value {
    Blob(usize),
    BlobInstance(usize, Rc<RefCell<Vec<Value>>>),
    Tuple(Rc<Vec<Value>>),
    Float(f64),
    Int(i64),
    Bool(bool),
    String(Rc<String>),
    Function(Vec<Rc<RefCell<UpValue>>>, Rc<RefCell<Block>>),
    ExternFunction(usize),
    Unkown,
    Nil,
}

impl Debug for Value {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Blob(i) => write!(fmt, "(blob {})", i),
            Value::BlobInstance(i, v) => write!(fmt, "(inst {} {:?})", i, v),
            Value::Float(f) => write!(fmt, "(float {})", f),
            Value::Int(i) => write!(fmt, "(int {})", i),
            Value::Bool(b) => write!(fmt, "(bool {})", b),
            Value::String(s) => write!(fmt, "(string \"{}\")", s),
            Value::Function(_, block) => write!(fmt, "(fn {}: {:?})", block.borrow().name, block.borrow().ty),
            Value::ExternFunction(slot) => write!(fmt, "(extern fn {})", slot),
            Value::Unkown => write!(fmt, "(unkown)"),
            Value::Nil => write!(fmt, "(nil)"),
            Value::Tuple(v) => write!(fmt, "({:?})", v),
        }
    }
}

impl Value {
    fn identity(self) -> Self {
        match self {
            Value::Float(_) => Value::Float(1.0),
            Value::Int(_) => Value::Int(1),
            Value::Bool(_) => Value::Bool(true),
            a => a,
        }
    }

    fn is_nil(&self) -> bool {
        match self {
            Value::Nil => true,
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
pub struct UpValue {
    slot: usize,
    value: Value,
}

impl UpValue {
    fn new(value: usize) -> Self {
        Self {
            slot: value,
            value: Value::Nil,
        }
    }

    fn get(&self, stack: &[Value]) -> Value {
        if self.is_closed() {
            self.value.clone()
        } else {
            stack[self.slot].clone()
        }
    }

    fn set(&mut self, stack: &mut [Value], value: Value) {
        if self.is_closed() {
            self.value = value;
        } else {
            stack[self.slot] = value;
        }
    }


    fn is_closed(&self) -> bool {
        self.slot == 0
    }

    fn close(&mut self, value: Value) {
        self.slot = 0;
        self.value = value;
    }
}

#[derive(Debug, Clone)]
pub struct Blob {
    pub name: String,

    pub name_to_field: HashMap<String, (usize, Type)>,
}

impl Blob {
    pub fn new(name: &str) -> Self {
        Self {
            name: String::from(name),
            name_to_field: HashMap::new(),
        }
    }

    pub fn add_field(&mut self, name: &str, ty: Type) -> Result<(), ()> {
        let size = self.name_to_field.len();
        let entry = self.name_to_field.entry(String::from(name));
        if matches!(entry, Entry::Occupied(_)) {
            Err(())
        } else {
            entry.or_insert((size, ty));
            Ok(())
        }
    }
}

///
/// Operations that the virtual machine carries out when running the
/// "byte-code".
///
#[derive(Debug, Clone)]
pub enum Op {
    /// Should never be run.
    /// Finding it in a program is a critical error.
    Illegal,

    /// Pops one value from the stack.
    ///
    /// {A, B} - Pop - {A}
    Pop,
    /// Assumes the value on the top of the stack has an upvalue, and closes
    /// that upvalue.
    ///
    /// {A, B} - Pop - {A}
    PopUpvalue,
    /// Copies the value on the top of the stack and pushes it to the stack.
    ///
    /// {A, B} - Copy - {A, B, B}
    Copy,
    /// Pushes the given value to the stack. Also links upvalues if the value is
    /// a function.
    ///
    /// {A} - Constant(B) - {A, B}
    Constant(Value),
    /// Creates a new [Value::Tuple] with the given size and pushed it to the
    /// stack.
    ///
    /// {A, B, C} - Tuple(3) - {D(A, B, C)}
    Tuple(usize),

    /// Indexes something indexable (currently only tuples) and pushes that
    /// value to the stack.
    ///
    /// {T, I} - Index - {T[I]}
    Index,
    /// Looks up a field by the given name and replaces the parent with it.
    /// Currently only expects a [Value::Blob].
    ///
    /// {O} - Get(F) - {O.F}
    Get(String),
    /// Looks up a field by the given name and replaces the current value in the
    /// object.
    /// Currently only expects a [Value::Blob].
    ///
    /// {O} - Set(F) - {}
    Set(String),

    /// Adds the two top elements on the stack using the function [op::add].
    ///
    /// {A, B} - Add - {A + B}
    Add,
    /// Subtracts the two top elements on the stack using the function
    /// [op::sub].
    ///
    /// {A, B} - Sub - {A - B}
    Sub,
    /// Multiplies the two top elements on the stack using the function
    /// [op::mul].
    ///
    /// {A, B} - Mul - {A - B}
    Mul,
    /// Divides the two top elements on the stack using the function [op::div].
    ///
    /// {A, B} - Div - {A / B}
    Div,
    /// Negates the top element on the stack.
    ///
    /// {A} - Neg - {-A}
    Neg,

    /// Performs a boolean "and" on the top 2 stack elements using [op::and].
    ///
    /// {A, B} - And - {A && B}
    And,
    /// Performs a boolean or on the top 2 stack elements using [op::or].
    ///
    /// {A, B} - Or - {A || B}
    Or,
    /// Performs a boolean not on the top stack element using [op::not].
    ///
    /// {A} - Not - {!A}
    Not,

    /// Sets the instruction pointer to the given value.
    ///
    /// Does not affect the stack.
    Jmp(usize),
    /// Sets the instruction pointer to the given value if the topmost value is
    /// false. The topmost value is popped.
    ///
    /// {A} - JmpFalse(n) - {}
    JmpFalse(usize),

    /// Compares the top 2 elements on the stack for equality and pushes the
    /// result. Compares using [op::eq].
    ///
    /// {A, B} - Equal - {A == B}
    Equal,
    /// Compares the top 2 elements on the stack for inequality and pushes the
    /// result. Compares using [op::less].
    ///
    /// {A, B} - Less - {A < B}
    Less,
    /// Compares the top 2 elements on the stack for inequality and pushes the
    /// result. Compares using [op::less].
    ///
    /// {A, B} - Greater - {B < A}
    Greater,

    /// Pops the top value on the stack and crashes the program if it is false.
    ///
    /// {A} - Assert - {}
    Assert,
    /// Should not be executed. If it is the program crashes.
    ///
    /// Does not affect the stack.
    Unreachable,

    /// Reads the value counted from the bottom of the stack and pushes it to
    /// the stack.
    ///
    /// {A, B} - ReadLocal(0) - {A, B, A}
    ReadLocal(usize),
    /// Sets the value counted from the bottom of the stack to the top value.
    /// The top value is popped.
    ///
    /// {A, B} - AssignLocal(0) - {B}
    AssignLocal(usize),

    /// Reads an upvalue and pushes it to the stack.
    ///
    /// {} - ReadUpvalue(0) - {A}
    ReadUpvalue(usize),
    /// Sets an upvalue to the top value. The top value is popped.
    ///
    /// {A} - AssignUpvalue(0) - {}
    AssignUpvalue(usize),

    /// A helper instruction for the typechecker that makes sure that the top
    /// value on the stack is of the given type. It signals that the "variable"
    /// is pushed.
    ///
    /// Does not affect the stack.
    Define(Type),

    /// Calls either a [Value::Blob], [Value::Function] or
    /// [Value::ExternFunction] with the given number of arguments. The called
    /// value is replaced with the result.
    ///
    /// {F, A, B} - Call(2) - {F(A, B)}
    Call(usize),

    /// Prints and pops the top value on the stack.
    ///
    /// {A} - Print - {}
    Print,

    /// Pops the current stack frame and replaces the old slot 0 with the top
    /// value. Also pops upvalues.
    ///
    /// {F, A, B} - Return - {..., B}
    Return,

    /// Yields execution to the program invoking the VM.
    ///
    /// Does not affect the stack.
    Yield,
}

///
/// All operators that can be applied to values.
///
pub mod op {
    use super::Value;
    use std::rc::Rc;

    fn tuple_bin_op(a: &Rc<Vec<Value>>, b: &Rc<Vec<Value>>, f: fn (&Value, &Value) -> Value) -> Value {
        Value::Tuple(Rc::new(a.iter().zip(b.iter()).map(|(a, b)| f(a, b)).collect()))
    }

    fn tuple_un_op(a: &Rc<Vec<Value>>, f: fn (&Value) -> Value) -> Value {
        Value::Tuple(Rc::new(a.iter().map(f).collect()))
    }

    pub fn neg(value: &Value) -> Value {
        match value {
            Value::Float(a) => Value::Float(-a),
            Value::Int(a) => Value::Int(-a),
            Value::Tuple(a) => tuple_un_op(a, neg),
            _ => Value::Nil,
        }
    }

    pub fn not(value: &Value) -> Value {
        match value {
            Value::Bool(a) => Value::Bool(!a),
            Value::Tuple(a) => tuple_un_op(a, not),
            _ => Value::Nil,
        }
    }


    pub fn add(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Float(a + b),
            (Value::Int(a), Value::Int(b)) => Value::Int(a + b),
            (Value::String(a), Value::String(b)) => Value::String(Rc::from(format!("{}{}", a, b))),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, add),
            _ => Value::Nil,
        }
    }

    pub fn sub(a: &Value, b: &Value) -> Value {
        add(a, &neg(b))
    }

    pub fn mul(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Float(a * b),
            (Value::Int(a), Value::Int(b)) => Value::Int(a * b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, mul),
            _ => Value::Nil,
        }
    }

    pub fn div(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Float(a / b),
            (Value::Int(a), Value::Int(b)) => Value::Int(a / b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, div),
            _ => Value::Nil,
        }
    }

    pub fn eq(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Bool(a == b),
            (Value::Int(a), Value::Int(b)) => Value::Bool(a == b),
            (Value::String(a), Value::String(b)) => Value::Bool(a == b),
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(a == b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, eq),
            _ => Value::Nil,
        }
    }

    pub fn less(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Float(a), Value::Float(b)) => Value::Bool(a < b),
            (Value::Int(a), Value::Int(b)) => Value::Bool(a < b),
            (Value::String(a), Value::String(b)) => Value::Bool(a < b),
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(a < b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, less),
            _ => Value::Nil,
        }
    }

    pub fn greater(a: &Value, b: &Value) -> Value {
        less(b, a)
    }

    pub fn and(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(*a && *b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, and),
            _ => Value::Nil,
        }
    }

    pub fn or(a: &Value, b: &Value) -> Value {
        match (a, b) {
            (Value::Bool(a), Value::Bool(b)) => Value::Bool(*a || *b),
            (Value::Tuple(a), Value::Tuple(b)) if a.len() == b.len() => tuple_bin_op(a, b, or),
            _ => Value::Nil,
        }
    }
}

#[derive(Debug)]
pub struct Block {
    pub ty: Type,
    pub ups: Vec<(usize, bool, Type)>,

    pub name: String,
    pub file: PathBuf,
    pub ops: Vec<Op>,
    pub last_line_offset: usize,
    pub line_offsets: HashMap<usize, usize>,
    pub line: usize,
}

impl Block {
    pub fn new(name: &str, file: &Path, line: usize) -> Self {
        Self {
            ty: Type::Void,
            ups: Vec::new(),
            name: String::from(name),
            file: file.to_owned(),
            ops: Vec::new(),
            last_line_offset: 0,
            line_offsets: HashMap::new(),
            line,
        }
    }

    pub fn empty_with_type(ty: &Type) -> Self {
        let mut block = Block::new("/empty/", Path::new(""), 0);
        block.ty = ty.clone();
        block
    }

    pub fn args(&self) -> &Vec<Type> {
        if let Type::Function(ref args, _) = self.ty {
            args
        } else {
            unreachable!()
        }
    }

    pub fn ret(&self) -> &Type {
        if let Type::Function(_, ref ret) = self.ty {
            ret
        } else {
            unreachable!()
        }
    }

    pub fn id(&self) -> (PathBuf, usize) {
        (self.file.clone(), self.line)
    }

    pub fn add_line(&mut self, token_position: usize) {
        if token_position != self.last_line_offset {
            self.line_offsets.insert(self.curr(), token_position);
            self.last_line_offset = token_position;
        }
    }

    pub fn line(&self, ip: usize) -> usize {
        for i in (0..=ip).rev() {
            if let Some(line) = self.line_offsets.get(&i) {
                return *line;
            }
        }
        return 0;
    }

    pub fn debug_print(&self) {
        println!("     === {} ===", self.name.blue());
        for (i, s) in self.ops.iter().enumerate() {
            if self.line_offsets.contains_key(&i) {
                print!("{:5} ", self.line_offsets[&i].red());
            } else {
                print!("    {} ", "|".red());
            }
            println!("{:05} {:?}", i.blue(), s);
        }
        println!("");
    }

    pub fn last_instruction(&mut self) -> &Op {
        self.ops.last().unwrap()
    }

    pub fn add(&mut self, op: Op, token_position: usize) -> usize {
        let len = self.curr();
        self.add_line(token_position);
        self.ops.push(op);
        len
    }

    pub fn add_from(&mut self, ops: &[Op], token_position: usize) -> usize {
        let len = self.curr();
        self.add_line(token_position);
        self.ops.extend_from_slice(ops);
        len
    }

    pub fn curr(&self) -> usize {
        self.ops.len()
    }

    pub fn patch(&mut self, op: Op, pos: usize) {
        self.ops[pos] = op;
    }
}

#[derive(Clone)]
pub struct Prog {
    pub blocks: Vec<Rc<RefCell<Block>>>,
    pub blobs: Vec<Rc<Blob>>,
    pub functions: Vec<RustFunction>,
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::error::ErrorKind;

    use super::{run_file, run_string};

    #[macro_export]
    macro_rules! assert_errs {
        ($result:expr, [ $( $kind:pat ),* ]) => {
            eprintln!("{} => {:?}", stringify!($result), $result);
            assert!(matches!(
                $result.unwrap_err().as_slice(),
                &[$($crate::error::Error {
                    kind: $kind,
                    file: _,
                    line: _,
                    message: _,
                },
                )*]
            ))
        };
    }

    #[macro_export]
    macro_rules! test_string {
        ($fn:ident, $prog:literal) => {
            #[test]
            fn $fn() {
                $crate::run_string($prog, true, Vec::new()).unwrap();
            }
        };
        ($fn:ident, $prog:literal, $errs:tt) => {
            #[test]
            fn $fn() {
                $crate::assert_errs!($crate::run_string($prog, true, Vec::new()), $errs);
            }
        }
    }

    #[macro_export]
    macro_rules! test_file {
        ($fn:ident, $path:literal) => {
            #[test]
            fn $fn() {
                let file = Path::new($path);
                run_file(&file, true, Vec::new()).unwrap();
            }
        };
    }

    #[test]
    fn unreachable_token() {
        assert_errs!(run_string("<!>\n", true, Vec::new()), [ErrorKind::Unreachable]);
    }

    macro_rules! test_multiple {
        ($mod:ident, $( $fn:ident : $prog:literal ),+ $( , )? ) => {
            mod $mod {
                $( test_string!($fn, $prog); )+
            }
        }
    }

    test_multiple!(
        order_of_operations,
        terms_and_factors: "1 + 1 * 2 <=> 3
                            1 * 2 + 3 <=> 5",
        in_rhs: "5 <=> 1 * 2 + 3",
        parenthesis: "(1 + 2) * 3 <=> 9",
        negation: "-1 <=> 0 - 1
                   -1 + 2 <=> 1
                   -(1 + 2) <=> -3
                   1 + -1 <=> 0
                   2 * -1 <=> -2",
    );

    test_multiple!(
        variables,
        single_variable: "a := 1
                          a <=> 1",
        two_variables: "a := 1
                        b := 2
                        a <=> 1
                        b <=> 2",
        stack_ordering: "a := 1
                         b := 2
                         b <=> 2
                         a <=> 1",
        assignment: "a := 1
                     b := 2
                     a = b
                     a <=> 2
                     b <=> 2",
    );

    test_multiple!(
        if_,
        compare_constants_equality: "if 1 == 2 {
                                       <!>
                                     }",
        compare_constants_unequality: "if 1 != 1 {
                                         <!>
                                       }",
        compare_variable: "a := 1
                           if a == 0 {
                             <!>
                           }
                           if a != 1 {
                             <!>
                           }",
        else_: "a := 1
                res := 0
                if a == 0 {
                  <!>
                } else {
                  res = 1
                }
                res <=> 1",
        else_if: "a := 1
                  res := 0
                  if a == 0 {
                    <!>
                  } else if a == 1 {
                    res = 1
                  } else {
                    <!>
                  }
                  res <=> 1",
    );

    test_multiple!(
        fun,
        simplest: "f := fn {}
                   f()",
        param_1: "f := fn a: int {}
                  f(1)",
        return_1: "f := fn -> int {
                     ret 1
                   }
                   f() <=> 1",
        param_and_return: "f := fn a: int -> int {
                             ret a * 2
                           }
                           f(1) <=> 2
                           f(5) <=> 10",
        param_2: "add := fn a: int, b: int -> int {
                    ret a + b
                  }
                  add(1, 1) <=> 2
                  add(10, 20) <=> 30",
        calls_inside_calls: "one := fn -> int {
                               ret 1
                             }
                             add := fn a: int, b: int -> int {
                               ret a + b
                             }
                             add(one(), one()) <=> 2
                             add(add(one(), one()), one()) <=> 3
                             add(one(), add(one(), one())) <=> 3",
        passing_functions: "g := fn -> int {
                              ret 1
                            }
                            f := fn inner: fn -> int -> int {
                              ret inner()
                            }
                            f(g) <=> 1",
        passing_functions_mixed: "g := fn a: int -> int {
                                    ret a * 2
                                  }
                                  f := fn inner: fn int -> int, a: int -> int {
                                    ret inner(a)
                                  }
                                  f(g, 2) <=> 4",
        multiple_returns: "f := fn a: int -> int {
                             if a == 1 {
                               ret 2
                             } else {
                               ret 3
                             }
                           }
                           f(0) <=> 3
                           f(1) <=> 2
                           f(2) <=> 3",
        precedence: "f := fn a: int, b: int -> int {
                       ret a + b
                     }
                     1 + f(2, 3) <=> 6
                     2 * f(2, 3) <=> 10
                     f(2, 3) - (2 + 3) <=> 0",
        factorial: "factorial : fn int -> int = fn n: int -> int {
                      if n <= 1 {
                        ret 1
                      }
                      ret n * factorial(n - 1)
                    }
                    factorial(5) <=> 120
                    factorial(6) <=> 720
                    factorial(12) <=> 479001600",

        returning_closures: "
f : fn -> fn -> int = fn -> fn -> int {
    x : int = 0
    f := fn -> int {
        x = x + 1
        ret x
    }
    f() <=> 1
    ret f
}

a := f()
b := f()

a() <=> 2
a() <=> 3

b() <=> 2
b() <=> 3

a() <=> 4
"

        //TODO this tests doesn't terminate in proper time if we print blocks and ops
                    /*
        fibonacci: "fibonacci : fn int -> int = fn n: int -> int {
                      if n == 0 {
                        ret 0
                      } else if n == 1 {
                        ret 1
                      } else if n < 0 {
                        <!>
                      }
                      ret fibonacci(n - 1) + fibonacci(n - 2)
                    }
                    fibonacci(10) <=> 55
                    fibonacci(20) <=> 6765"
                    */
    );

    test_multiple!(
        blob,
        simple: "blob A {}",
        instantiate: "blob A {}
                      a := A()",
        field: "blob A { a: int }",
        field_assign: "blob A { a: int }
                       a := A()
                       a.a = 2",
        field_get: "blob A { a: int }
                       a := A()
                       a.a = 2
                       a.a <=> 2
                       2 <=> a.a",
        multiple_fields: "blob A {
                            a: int
                            b: int
                          }
                          a := A()
                          a.a = 2
                          a.b = 3
                          a.a + a.b <=> 5
                          5 <=> a.a + a.b"
    );

    test_multiple!(tuples,
        add: "(1, 2, 3, 4) + (4, 3, 2, 1) <=> (5, 5, 5, 5)",
        sub: "(1, -2, 3, -4) - (4, 3, -2, -1) <=> (-3, 1, 1, -5)",
        mul: "(0, 1, 2) * (2, 3, 4) <=> (0, 3, 8)",
        types: "a: (int, float, int) = (1, 1., 1)",
        more_types: "a: (str, bool, int) = (\"abc\", true, 1)",
    );

    test_file!(scoping, "progs/tests/scoping.sy");
    test_file!(for_, "progs/tests/for.sy");

    test_multiple!(
        op_assign,
        add: "a := 1\na += 1\na <=> 2",
        sub: "a := 2\na -= 1\na <=> 1",
        mul: "a := 2\na *= 2\na <=> 4",
        div: "a := 2\na /= 2\na <=> 1",
        cluster: "
blob A { a: int }
a := A()
a.a = 0
a.a += 1
a.a <=> 1
a.a *= 2
a.a <=> 2
a.a /= 2
a.a <=> 1
a.a -= 1
a.a <=> 0"
    );
}
