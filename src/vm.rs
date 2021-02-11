use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fmt::Debug;
use std::rc::Rc;
use std::convert::TryInto;

use owo_colors::OwoColorize;

use crate::{Blob, Block, Op, Prog, UpValue, Value, op};
use crate::error::{Error, ErrorKind};
use crate::RustFunction;
use crate::Type;

macro_rules! error {
    ( $thing:expr, $kind:expr) => {
        return Err($thing.error($kind, None));
    };
    ( $thing:expr, $kind:expr, $msg:expr) => {
        return Err($thing.error($kind, Some($msg)));
    };
}

macro_rules! one_op {
    ( $self:expr, $op:expr, $fun:expr ) => {
        let a = $self.pop();
        let b = $fun(&a);
        if b.is_nil() {
            $self.push(b);
            error!($self, ErrorKind::RuntimeTypeError($op, vec![a]));
        }
        $self.push(b);
    };
}

macro_rules! two_op {
    ( $self:expr, $op:expr, $fun:expr ) => {
        let (a, b) = $self.poppop();
        let c = $fun(&a, &b);
        if c.is_nil() {
            $self.push(c);
            error!($self, ErrorKind::RuntimeTypeError($op, vec![a, b]));
        }
        $self.push(c);
    };
}

#[derive(Debug)]
struct Frame {
    stack_offset: usize,
    block: Rc<RefCell<Block>>,
    ip: usize,
}

pub struct VM {
    upvalues: HashMap<usize, Rc<RefCell<UpValue>>>,

    stack: Vec<Value>,
    frames: Vec<Frame>,

    blobs: Vec<Rc<Blob>>,
    constants: Vec<Value>,
    strings: Vec<String>,

    pub print_blocks: bool,
    pub print_ops: bool,
    runtime: bool,


    extern_functions: Vec<RustFunction>,
}

#[derive(Eq, PartialEq)]
pub enum OpResult {
    Yield,
    Done,

    // Will never be returned.
    #[doc(hidden)]
    Continue,
}

impl VM {
    pub(crate) fn new() -> Self {
        Self {
            upvalues: HashMap::new(),

            stack: Vec::new(),
            frames: Vec::new(),

            blobs: Vec::new(),
            constants: Vec::new(),
            strings: Vec::new(),

            print_blocks: false,
            print_ops: false,
            runtime: false,

            extern_functions: Vec::new()
        }
    }

    fn drop_upvalue(&mut self, slot: usize, value: Value) {
        if let Entry::Occupied(entry) = self.upvalues.entry(slot) {
            entry.get().borrow_mut().close(value);
            entry.remove();
        } else {
            unreachable!();
        }
    }

    fn find_upvalue(&mut self, slot: usize) -> &mut Rc<RefCell<UpValue>> {
        self.upvalues.entry(slot).or_insert(
            Rc::new(RefCell::new(UpValue::new(slot))))
    }

    fn push(&mut self, value: Value) {
        self.stack.push(value);
    }

    fn pop(&mut self) -> Value {
        match self.stack.pop() {
            Some(x) => x,
            None => self.crash_and_burn(),
        }
    }

    fn poppop(&mut self) -> (Value, Value) {
        let (a, b) = (self.stack.remove(self.stack.len() - 1),
                      self.stack.remove(self.stack.len() - 1));
        (b, a)  // this matches the order they were on the stack
    }

    fn frame(&self) -> &Frame {
        let last = self.frames.len() - 1;
        &self.frames[last]
    }

    fn frame_mut(&mut self) -> &mut Frame {
        let last = self.frames.len() - 1;
        &mut self.frames[last]
    }

    fn constant(&self, slot: usize) -> &Value {
        &self.constants[slot]
    }

    fn ty(&self, slot: usize) -> &Type {
        match &self.constants[slot] {
            Value::Ty(ty) => ty,
            _ => self.crash_and_burn(),
        }
    }

    fn string(&self, slot: usize) -> &String {
        &self.strings[slot]
    }

    fn op(&mut self) -> Op {
        let ip = self.frame().ip;
        self.frame_mut().ip += 1;
        // Note(ed): This is pretty... Dumb...
        unsafe { std::mem::transmute::<u8, Op>(self.frame().block.borrow().ops[ip]) }
    }

    fn usize(&mut self) -> usize {
        let ip = self.frame().ip;
        self.frame_mut().ip += 8;
        usize::from_be_bytes(self.frame().block.borrow().ops[ip..ip+8]
            .try_into()
            .unwrap_or_else(|_| self.crash_and_burn())
        )
    }

    fn print_stacktrace(&self) {
        if !self.runtime { return; }

        println!("\n<{}>", "STACK".red());
        for (i, frame) in self.frames.iter().enumerate() {
            println!("  {:>3}. {}:{:<4} in {:10}",
                i,
                frame.block.borrow().file.display(),
                frame.block.borrow().line(self.frame().ip),
                frame.block.borrow().name.blue());
        }
        println!("")
    }

    /// Stop the program, violently
    fn crash_and_burn(&self) -> ! {
        self.print_stack();
        println!("\n");
        self.print_stacktrace();
        self.frame().block.borrow().debug_print();
        println!("    ip: {}, line: {}\n",
            self.frame().ip.blue(),
            self.frame().block.borrow().line(self.frame().ip).blue());
        unreachable!();
    }

    fn error(&self, kind: ErrorKind, message: Option<String>) -> Error {
        let frame = self.frames.last().unwrap();
        self.print_stacktrace();
        Error {
            kind,
            file: frame.block.borrow().file.clone(),
            line: frame.block.borrow().line(frame.ip),
            message,
        }
    }

    /// Runs a single operation on the VM
    fn eval_op(&mut self, op: Op) -> Result<OpResult, Error> {
        match op {
            Op::Nop => {}

            Op::Illegal => {
                error!(self, ErrorKind::InvalidProgram);
            }

            Op::Unreachable => {
                error!(self, ErrorKind::Unreachable);
            }

            Op::Pop => {
                self.pop();
            }

            Op::Tuple => {
                let size = self.usize();
                let values = self.stack.split_off(self.stack.len() - size);
                self.stack.push(Value::Tuple(Rc::new(values)));
            }

            Op::PopUpvalue => {
                let value = self.pop();
                let slot = self.stack.len();
                self.drop_upvalue(slot, value);
            }

            Op::Copy => {
                let v = self.pop();
                self.push(v.clone());
                self.push(v);
            }

            Op::Yield => {
                self.frame_mut().ip += 1;
                return Ok(OpResult::Yield);
            }

            Op::Constant => {
                let value = self.usize();
                let offset = self.frame().stack_offset;
                let constant = self.constant(value).clone();
                let value = match constant {
                    Value::Function(_, block) => {
                        let mut ups = Vec::new();
                        for (slot, is_up, _) in block.borrow().upvalues.iter() {
                            let up = if *is_up {
                                if let Value::Function(local_ups, _) = &self.stack[offset] {
                                    Rc::clone(&local_ups[*slot])
                                } else {
                                    unreachable!()
                                }
                            } else {
                                let slot = self.frame().stack_offset + slot;
                                Rc::clone(self.find_upvalue(slot))
                            };
                            ups.push(up);
                        }
                        Value::Function(ups, block)
                    },
                    value => value,
                };
                self.push(value);
            }

            Op::Index => {
                let slot = self.stack.pop().unwrap();
                let val = self.stack.pop().unwrap();
                match (val, slot) {
                    (Value::Tuple(v), Value::Int(slot)) => {
                        let slot = slot as usize;
                        if v.len() < slot {
                            self.stack.push(Value::Nil);
                            let len = v.len();
                            error!(self, ErrorKind::IndexOutOfBounds(Value::Tuple(v), len, slot));
                        }
                        self.stack.push(v[slot].clone());
                    }
                    (val, slot) => {
                        self.stack.push(Value::Nil);
                        error!(self, ErrorKind::RuntimeTypeError(op, vec![val, slot]), String::from("Cannot index type"));
                    }
                }
            }

            Op::Get => {
                let field = self.usize();
                let inst = self.pop();
                let field = self.string(field);
                if let Value::BlobInstance(ty, values) = inst {
                    let slot = self.blobs[ty].fields.get(field).unwrap().0;
                    self.push(values.borrow()[slot].clone());
                } else {
                    error!(self, ErrorKind::RuntimeTypeError(op, vec![inst]));
                }
            }

            Op::Set => {
                let field = self.usize();
                let (inst, value) = self.poppop();
                let field = self.string(field);
                if let Value::BlobInstance(ty, values) = inst {
                    let slot = self.blobs[ty].fields.get(field).unwrap().0;
                    values.borrow_mut()[slot] = value;
                } else {
                    error!(self, ErrorKind::RuntimeTypeError(op, vec![inst]));
                }
            }

            Op::Neg => { one_op!(self, Op::Neg, op::neg); }

            Op::Add => { two_op!(self, Op::Add, op::add); }

            Op::Sub => { two_op!(self, Op::Sub, op::sub); }

            Op::Mul => { two_op!(self, Op::Mul, op::mul); }

            Op::Div => { two_op!(self, Op::Div, op::div); }

            Op::Equal => { two_op!(self, Op::Equal, op::eq); }

            Op::Less => { two_op!(self, Op::Less, op::less); }

            Op::Greater => { two_op!(self, Op::Greater, op::greater); }

            Op::And => { two_op!(self, Op::And, op::and); }

            Op::Or => { two_op!(self, Op::Or, op::or); }

            Op::Not => { one_op!(self, Op::Not, op::not); }

            Op::Jmp => {
                let line = self.usize();
                self.frame_mut().ip = line;
                return Ok(OpResult::Continue);
            }

            Op::JmpFalse => {
                let line = self.usize();
                if matches!(self.pop(), Value::Bool(false)) {
                    self.frame_mut().ip = line;
                    return Ok(OpResult::Continue);
                }
            }

            Op::JmpNPop => {
                let line = self.usize();
                let to_pop = self.usize();
                let hi = self.stack.len();
                let lo = hi - to_pop;
                for slot in lo..hi {
                    if self.upvalues.contains_key(&slot) {
                        let value = self.stack[slot].clone();
                        self.drop_upvalue(slot, value);
                    }
                }
                self.stack.truncate(lo);
                self.frame_mut().ip = line;
                return Ok(OpResult::Continue);
            }

            Op::Assert => {
                if matches!(self.pop(), Value::Bool(false)) {
                    error!(self, ErrorKind::AssertFailed);
                }
                self.push(Value::Bool(true));
            }

            Op::ReadUpvalue => {
                let slot = self.usize();
                let offset = self.frame().stack_offset;
                let value = match &self.stack[offset] {
                    Value::Function(ups, _) => {
                        ups[slot].borrow().get(&self.stack)
                    }
                    _ => unreachable!(),
                };
                self.push(value);
            }

            Op::AssignUpvalue => {
                let slot = self.usize();
                let offset = self.frame().stack_offset;
                let value = self.pop();
                let slot = match &self.stack[offset] {
                    Value::Function(ups, _) => Rc::clone(&ups[slot]),
                    _ => unreachable!(),
                };
                slot.borrow_mut().set(&mut self.stack, value);
            }

            Op::ReadLocal => {
                let slot = self.usize();
                let slot = self.frame().stack_offset + slot;
                self.push(self.stack[slot].clone());
            }

            Op::AssignLocal => {
                let slot = self.usize();
                let slot = self.frame().stack_offset + slot;
                self.stack[slot] = self.pop();
            }

            Op::Define => {}

            Op::Call => {
                let num_args = self.usize();
                let new_base = self.stack.len() - 1 - num_args;
                match self.stack[new_base].clone() {
                    Value::Blob(blob_id) => {
                        let blob = &self.blobs[blob_id];

                        let mut values = Vec::with_capacity(blob.fields.len());
                        for _ in 0..values.capacity() {
                            values.push(Value::Nil);
                        }

                        self.pop();
                        self.push(Value::BlobInstance(blob_id, Rc::new(RefCell::new(values))));
                    }
                    Value::Function(_, block) => {
                        let inner = block.borrow();
                        let args = inner.args();
                        if args.len() != num_args {
                            error!(self,
                                ErrorKind::InvalidProgram,
                                format!("Invalid number of arguments, got {} expected {}.",
                                    num_args, args.len()));
                        }

                        if self.print_blocks {
                            inner.debug_print();
                        }
                        self.frames.push(Frame {
                            stack_offset: new_base,
                            block: Rc::clone(&block),
                            ip: 0,
                        });
                        return Ok(OpResult::Continue);
                    }
                    Value::ExternFunction(slot) => {
                        let extern_func = self.extern_functions[slot];
                        let res = match extern_func(&self.stack[new_base+1..], false) {
                            Ok(value) => value,
                            Err(ek) => error!(self, ek, "Wrong arguments to external function".to_string()),
                        };
                        self.stack.truncate(new_base);
                        self.push(res);
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }

            Op::Print => {
                println!("PRINT: {:?}", self.pop());
            }

            Op::Return => {
                let last = self.frames.pop().unwrap();
                if self.frames.is_empty() {
                    return Ok(OpResult::Done);
                } else {
                    self.stack[last.stack_offset] = self.pop();
                    for slot in last.stack_offset+1..self.stack.len() {
                        if self.upvalues.contains_key(&slot) {
                            let value = self.stack[slot].clone();
                            self.drop_upvalue(slot, value);
                        }
                    }
                    self.stack.truncate(last.stack_offset + 1);
                }
            }
        }
        // self.frame_mut().ip += 1;
        Ok(OpResult::Continue)
    }

    fn print_stack(&self) {
        let start = self.frame().stack_offset;
        print!("    {:3} [", start);
        for (i, s) in self.stack.iter().skip(start).enumerate() {
            if i != 0 {
                print!(" ");
            }
            print!("{:?}", s.green());
        }
        println!("]");

        println!("{:5} {:05} {:?}",
            self.frame().block.borrow().line(self.frame().ip).red(),
            self.frame().ip.blue(),
            self.frame().block.borrow().ops[self.frame().ip]);
    }

    // Initalizes the VM for running. Run cannot be called before this.
    pub(crate) fn init(&mut self, prog: &Prog) {
        let block = Rc::clone(&prog.blocks[0]);
        self.blobs = prog.blobs.clone();
        self.constants = prog.constants.clone();
        self.strings = prog.strings.clone();

        self.extern_functions = prog.functions.clone();
        self.stack.clear();
        self.frames.clear();
        self.runtime = true;

        self.push(Value::Function(Vec::new(), Rc::clone(&block)));

        self.frames.push(Frame {
            stack_offset: 0,
            block,
            ip: 0
        });
    }

    /// Simulates the program.
    pub fn run(&mut self) -> Result<OpResult, Error> {
        if self.print_blocks {
            println!("\n    [[{}]]\n", "RUNNING".red());
            self.frame().block.borrow().debug_print();
        }

        loop {
            if self.print_ops {
                self.print_stack()
            }

            let op = self.op();
            let op = self.eval_op(op)?;
            if matches!(op, OpResult::Done | OpResult::Yield) {
                return Ok(op);
            }
        }
    }

    /// Checks the current operation for type errors.
    fn check_op(&mut self, op: Op) -> Result<(), Error> {
        match op {
            Op::Unreachable => {}

            Op::Jmp => { self.usize(); }

            Op::Yield => {}

            Op::Constant => {
                let value = self.usize();
                match self.constant(value).clone() {
                    Value::Function(_, block) => {
                        self.push(Value::Function(Vec::new(), block.clone()));

                        let mut types = Vec::new();
                        for (slot, is_up, ty) in block.borrow().upvalues.iter() {
                            if *is_up {
                                types.push(ty.clone());
                            } else {
                                types.push(Type::from(&self.stack[*slot]));
                            }
                        }

                        let mut block_mut = block.borrow_mut();
                        for (i, (_, is_up, ty)) in block_mut.upvalues.iter_mut().enumerate() {
                            if *is_up { continue; }

                            let suggestion = &types[i];
                            if matches!(ty, Type::Unknown) {
                                *ty = suggestion.clone();
                            } else {
                                if ty != suggestion {
                                    error!(self,
                                           ErrorKind::TypeError(op,
                                                    vec![ty.clone(), suggestion.clone()]),
                                           "Failed to infer type.".to_string());
                                }
                            }
                        };
                    },
                    value => {
                        self.push(value.clone());
                    }
                }
            }

            Op::Get => {
                let field = self.usize();
                let inst = self.pop();
                let field = self.string(field);
                if let Value::BlobInstance(ty, _) = inst {
                    let value = Value::from(&self.blobs[ty].fields.get(field).unwrap().1);
                    self.push(value);
                } else {
                    self.push(Value::Nil);
                    error!(self, ErrorKind::RuntimeTypeError(op, vec![inst]));
                }
            }

            Op::Set => {
                let field = self.usize();
                let (inst, value) = self.poppop();
                let field = self.string(field);

                if let Value::BlobInstance(ty, _) = inst {
                    let ty = &self.blobs[ty].fields.get(field).unwrap().1;
                    if ty != &Type::from(&value) {
                        error!(self, ErrorKind::RuntimeTypeError(op, vec![inst]));
                    }
                } else {
                    error!(self, ErrorKind::RuntimeTypeError(op, vec![inst]));
                }
            }

            Op::PopUpvalue => {
                self.pop();
            }

            Op::ReadUpvalue => {
                let slot = self.usize();
                let value = Value::from(&self.frame().block.borrow().upvalues[slot].2);
                self.push(value);
            }

            Op::AssignUpvalue => {
                let slot = self.usize();
                let var = self.frame().block.borrow().upvalues[slot].2.clone();
                let up = self.pop().into();
                if var != up {
                    error!(self, ErrorKind::TypeError(op, vec![var, up]),
                                  "Incorrect type for upvalue.".to_string());
                }
            }

            Op::Return => {
                let a = self.pop();
                let inner = self.frame().block.borrow();
                let ret = inner.ret();
                if Type::from(&a) != *ret {
                    error!(self, ErrorKind::TypeError(op, vec![a.into(),
                                                               ret.clone()]),
                                                      "Not matching return type.".to_string());
                }
            }

            Op::Print => {
                self.pop();
            }

            Op::Define => {
                let ty = self.usize();
                let ty = self.ty(ty);
                let top_type = self.stack.last().unwrap().into();
                match (ty, top_type) {
                    (Type::Unknown, top_type)
                        if top_type != Type::Unknown => {}
                    (a, b) if a != &b => {
                        error!(self,
                            ErrorKind::TypeError(
                                op,
                                vec![a.clone(), b.clone()]),
                                format!("Tried to assign a type {:?} to type {:?}.", a, b)
                        );
                    }
                    _ => {}
                }
            }

            Op::Call => {
                let num_args = self.usize();
                let new_base = self.stack.len() - 1 - num_args;
                match self.stack[new_base].clone() {
                    Value::Blob(blob_id) => {
                        let blob = &self.blobs[blob_id];

                        let mut values = Vec::with_capacity(blob.fields.len());
                        for _ in 0..values.capacity() {
                            values.push(Value::Nil);
                        }

                        for (slot, ty) in blob.fields.values() {
                            values[*slot] = ty.into();
                        }

                        self.pop();
                        self.push(Value::BlobInstance(blob_id, Rc::new(RefCell::new(values))));
                    }
                    Value::Function(_, block) => {
                        let inner = block.borrow();
                        let args = inner.args();
                        if args.len() != num_args {
                            error!(self,
                                ErrorKind::InvalidProgram,
                                format!("Invalid number of arguments, got {} expected {}.",
                                    num_args, args.len()));
                        }

                        let stack_args = &self.stack[self.stack.len() - args.len()..];
                        let stack_args: Vec<_> = stack_args.iter().map(|x| x.into()).collect();
                        if args != &stack_args {
                            error!(self,
                                ErrorKind::TypeError(op, vec![]),
                                format!("Expected args of type {:?} but got {:?}.",
                                    args, stack_args));
                        }

                        self.stack[new_base] = block.borrow().ret().into();

                        self.stack.truncate(new_base + 1);
                    }
                    Value::ExternFunction(slot) => {
                        let extern_func = self.extern_functions[slot];
                        let res = match extern_func(&self.stack[new_base+1..], false) {
                            Ok(value) => value,
                            Err(ek) => {
                                self.stack.truncate(new_base);
                                self.push(Value::Nil);
                                error!(self, ek, "Wrong arguments to external function".to_string())
                            }
                        };
                        self.stack.truncate(new_base);
                        self.push(res);
                    }
                    _ => {
                        error!(self,
                            ErrorKind::TypeError(op, vec![Type::from(&self.stack[new_base])]),
                            format!("Tried to call non-function {:?}", self.stack[new_base]));
                    }
                }
            }

            Op::JmpFalse => {
                self.usize();
                match self.pop() {
                    Value::Bool(_) => {},
                    a => { error!(self, ErrorKind::TypeError(op, vec![a.into()])) },
                }
            }

            Op::JmpNPop => {
                self.usize();
                self.usize();
            }

            _ => {
                self.eval_op(op)?;
                return Ok(())
            }
        }
        // self.frame_mut().ip += 1;
        Ok(())
    }

    fn typecheck_block(&mut self, block: Rc<RefCell<Block>>) -> Vec<Error> {
        self.stack.clear();
        self.frames.clear();

        self.push(Value::Function(Vec::new(), Rc::clone(&block)));
        for arg in block.borrow().args() {
            self.push(arg.into());
        }

        self.frames.push(Frame {
            stack_offset: 0,
            block,
            ip: 0
        });

        if self.print_blocks {
            println!("\n    [[{}]]\n", "TYPECHECK".purple());
            self.frame().block.borrow().debug_print();
        }

        let mut errors = Vec::new();
        loop {
            let ip = self.frame().ip;
            if ip >= self.frame().block.borrow().ops.len() {
                // TODO(ed): We don't garantee functions to return the always return the
                // correct type. We don't handle the implicit return case.
                break;
            }

            if self.print_ops {
                self.print_stack()
            }

            let op = self.op();
            if let Err(e) = self.check_op(op) {
                errors.push(e);
                self.frame_mut().ip += 1;
            }

            if !self.stack.is_empty() {
                let ident = self.pop().identity();
                self.push(ident);
            }
        }
        errors
    }

    // Checks the program for type errors.
    pub(crate) fn typecheck(&mut self, prog: &Prog) -> Result<(), Vec<Error>> {
        let mut errors = Vec::new();

        self.blobs = prog.blobs.clone();
        self.constants = prog.constants.clone();
        self.strings = prog.strings.clone();
        self.runtime = false;

        self.extern_functions = prog.functions.clone();
        for block in prog.blocks.iter() {
            errors.append(&mut self.typecheck_block(Rc::clone(block)));
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

#[cfg(test)]
mod tests {
    mod typing {
        use crate::error::ErrorKind;
        use crate::test_string;

        test_string!(uncallable_type, "
                 f := fn i: int {
                     i()
                 }",
                 [ErrorKind::TypeError(_, _)]);

        test_string!(wrong_params, "
                 f : fn -> int = fn a: int -> int {}",
                 [ErrorKind::TypeError(_, _), ErrorKind::TypeError(_, _)]);

        test_string!(wrong_ret, "
                 f : fn -> int = fn {}",
                 [ErrorKind::TypeError(_, _)]);
    }
}
