//! GrumpyVM instruction set.
//!
//! This module contains the types of values and instructions
//! supported by GrumpyVM.
///     README         
///     Cargo Project:  grumpy
///     File:           isa.rs
///     Authors:        Nathaniel Buchanan & Johnny Gilbert    
///     Date:           March 26, 2022
///     Class:          CS 4100, Section 100 - Formal Languages and Compilers
///     Professors:     Dr. Chang Liu, Professor Alex Bagnall
///     Brief:          This is the ISA from PA2                    
///     Repo:           https://github.com/OUCompilers/pa3-gc-JohnGilbert57.git

// Changes from PA2:

// * Add Vforward constructor to Val type (for forward pointers used
//   by the GC).

use self::{Binop::*, Instr::*, PInstr::*, Unop::*, Val::*};
use crate::{ParseError, FromBytes, ToBytes};
use std::fmt::{self, Display};
use std::str::FromStr;
use std::convert::TryInto;

/// Heap addresses.
pub type Address = usize;

/// GrumpyVM values.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Val {
    // Value types that may appear in GrumpyVM programs:
    /// The unit value.
    Vunit,
    /// 32-bit signed integers.
    Vi32(i32),
    /// Booleans.
    Vbool(bool),
    /// Stack or instruction locations.
    Vloc(u32),
    /// The undefined value.
    Vundef,

    // Value types that are used internally by the language
    // implementation, and may not appear in GrumpyVM programs:
    /// Metadata for heap objects that span multiple values.
    Vsize(usize),
    /// Pointers to heap locations.
    Vaddr(Address),
    /// Forward pointers used by GC
    Vforward(Address)
}

/// Val methods.
impl Val {
    /// Try to extract an i32 from a Val.
    pub fn to_i32(&self) -> Option<i32> {
	match self {
	    Vi32(i) => Some(*i),
	    _ => None
	}
    }
    /// Try to extract a bool from a Val.
    pub fn to_bool(&self) -> Option<bool> {
	match self {
	    Vbool(b) => Some(*b),
	    _ => None
	}
    }
    /// Try to extract a loc (u32) from a Val.
    pub fn to_loc(&self) -> Option<u32> {
	match self {
	    Vloc(loc) => Some(*loc),
	    _ => None
	}
    }
    /// Try to extract an address (usize) from a Val.
    pub fn to_address(&self) -> Option<Address> {
	match self {
	    Vaddr(addr) => Some(*addr),
	    _ => None
	}
    }
}

/// GrumpyVM native instructions.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Instr {
    /// Push(v): Push value v onto the stack.
    Push(Val),
    /// Pop a value from the stack, discarding it.
    Pop,
    /// Peek(i): Push onto the stack the ith value from the top.
    Peek(u32),
    /// Unary(u): Apply u to the top value on the stack.
    Unary(Unop),
    /// Binary(b): Apply b to the top two values on the stack,
    /// replacing them with the result.
    Binary(Binop),
    /// Swap the top two values.
    Swap,
    /// Allocate an array on the heap.
    Alloc,
    /// Write to a heap-allocated array.
    Set,
    /// Read from a heap-allocated array.
    Get,
    /// Var(i): Get the value at stack position fp+i.
    Var(u32),
    /// Store(i): Store a value at stack position fp+i.
    Store(u32),
    /// SetFrame(i): Set fp = s.stack.len() - i.
    SetFrame(u32),
    /// Function call.
    Call,
    /// Function return.
    Ret,
    /// Conditional jump.
    Branch,
    /// Halt the machine.
    Halt,
    /// Print the top Value from the Stack
    Print,
    /// Size of the Array at the Top of the Stack
    Size,
}

/// Program labels.
pub type Label = String;

/// Pseudo-instructions, extending native instructions with support
/// for labels. GrumpyVM cannot execute these directly -- they must
/// first be translated by the assembler to native instructions.
#[derive(Debug, Clone, PartialEq)]
pub enum PInstr {
    /// Label the next instruction.
    PLabel(Label),
    /// Push a label onto the stack.
    PPush(Label),
    /// Native machine instruction.
    PI(Instr),
}

/// Unary operators.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Unop {
    /// Boolean negation.
    Neg,
}

/// Binary operators.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Binop {
    /// i32 addition.
    Add,
    /// i32 multiplication.
    Mul,
    /// i32 subtraction.
    Sub,
    /// i32 division (raises an error on divide by zero).
    Div,
    /// Returns true if one i32 is less than another, otherwise false.
    Lt,
    /// Returns true if one i32 is equal another, otherwise false.
    Eq,
}

////////////////////////////////////////////////////////////////////////
// Display trait implementations
////////////////////////////////////////////////////////////////////////

impl Display for Unop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Neg => write!(f, "neg")
        }
    }
}

impl Display for Binop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Add => write!(f, "+"),
            Mul => write!(f, "*"),
            Sub => write!(f, "-"),
            Div => write!(f, "/"),
            Lt  => write!(f, "<"),
            Eq  => write!(f, "=="),
        }
    }
}

impl Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Vunit    => write!(f, "tt"),
            Vi32(i)  => write!(f, "{}", i),
            Vbool(b) => write!(f, "{}", b),
            Vloc(u)  => write!(f, "{}", u),
            Vundef   => write!(f, "undef"),
            _ => Err(fmt::Error)
        }
    }
}

impl Display for Instr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Push(v)     => write!(f, "push {}", v),
            Pop         => write!(f, "pop"),
            Peek(u)     => write!(f, "peek {}", u),
            Unary(u)    => write!(f, "unary {}", u),
            Binary(b)   => write!(f, "binary {}", b),
            Swap        => write!(f, "swap"),
            Alloc       => write!(f, "alloc"),
            Set         => write!(f, "set"),
            Get         => write!(f, "get"),
            Var(u)      => write!(f, "var {}", u),
            Store(u)    => write!(f, "store {}", u),
            SetFrame(u) => write!(f, "setframe {}", u),
            Call        => write!(f, "call"),
            Ret         => write!(f, "ret"),
            Branch      => write!(f, "branch"),
            Halt        => write!(f, "halt"),
            Print       => write!(f, "print"),
            Size        => write!(f, "size"),
        }
    }
}

impl Display for PInstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PLabel(lbl) => write!(f, "{}:", lbl),
            PPush(lbl)  => write!(f, "push {}", lbl),
            PI(instr)   => write!(f, "{}", instr)
        }
    }
}

////////////////////////////////////////////////////////////////////////
// FromStr trait implementations
////////////////////////////////////////////////////////////////////////

impl FromStr for Unop {
    type Err = ParseError;
    
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            // boolean negation
            "neg" => Ok(Neg),
            _     => Err(ParseError("Error: FromStr for Unop - Not a Valid Unop".to_string()))
        }
    }
}

impl FromStr for Binop {
    type Err = ParseError;
    
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            // i32 addition.
            "+"  => Ok(Add),
            // i32 subtraction.
            "-"  => Ok(Sub),
            // i32 multiplication.
            "*"  => Ok(Mul),
            // i32 division.
            "/"  => Ok(Div),
            // i32 less than operator.
            "<"  => Ok(Lt),
            // i32 equality operator.
            "==" => Ok(Eq),
            _ => Err(ParseError("Error: FromStr for Binop - Not a Valid Binop".to_string()))
        }
    }
}

impl FromStr for Val {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "tt"        => Ok(Vunit),
            "undef"     => Ok(Vundef),
            "true"      => Ok(Vbool(true)),
            "false"     => Ok(Vbool(false)),
            _           => Ok(Vi32(i32::from_str(s)?))
        } 
    }
}

impl FromStr for Instr {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let items: Vec<&str> = s.split_whitespace().collect();
        match items[0] {
            "swap"      => {
                if items.len() == 1 {
                    Ok(Swap)
                } else {
                    Err(ParseError("Error: FromStr for Instr - swap".to_string()))
                }
            }
            "alloc"     => {
                if items.len() == 1 {
                    Ok(Alloc)
                } else {
                    Err(ParseError("Error: FromStr for Instr - alloc".to_string()))
                }
            }
            "set"       => {
                if items.len() == 1 {
                    Ok(Set)
                } else {
                    Err(ParseError("Error: FromStr for Instr - set".to_string()))
                }
            }
            "get"       => {
                if items.len() == 1 {
                    Ok(Get)
                } else {
                    Err(ParseError("Error: FromStr for Instr - get".to_string()))
                }
            }
            "pop"       => {
                if items.len() == 1 {
                    Ok(Pop)
                } else {
                    Err(ParseError("Error: FromStr for Instr - pop".to_string()))
                }
            }
            "call"      => {
                if items.len() == 1 {
                    Ok(Call)
                } else {
                    Err(ParseError("Error: FromStr for Instr - call".to_string()))
                }
            }
            "ret"       => {
                if items.len() == 1 {
                    Ok(Ret)
                } else {
                    Err(ParseError("Error: FromStr for Instr - ret".to_string()))
                }
            }
            "branch"    => {
                if items.len() == 1 {
                    Ok(Branch)
                } else {
                    Err(ParseError("Error: FromStr for Instr - branch".to_string()))
                }
            }
            "halt"      => {
                if items.len() == 1 {
                    Ok(Halt)
                } else {
                    Err(ParseError("Error: FromStr for Instr - halt".to_string()))
                }
            }
            "push"      => {
                if items.len() == 2 {
                    Ok(Push(Val::from_str(items[1])?))
                } else {
                    Err(ParseError("Error: FromStr for Instr - push".to_string()))
                }
            }
            "peek"      => {
                if items.len() == 2 {
                    Ok(Peek(u32::from_str(items[1])?))
                } else {
                    Err(ParseError("Error: FromStr for Instr - peek".to_string()))
                }
            }
            "unary"     => { 
                if items.len() == 2 {
                    Ok(Unary(Unop::from_str(items[1])?))
                } else {
                    Err(ParseError("Error: FromStr for Instr - unary".to_string()))
                }
            }
            "binary"    => { 
                if items.len() == 2 {
                    Ok(Binary(Binop::from_str(items[1])?))
                } else {
                    Err(ParseError("Error: FromStr for Instr - binary".to_string()))
                }
            }
            "var"       => { 
                if items.len() == 2 {
                    Ok(Var(u32::from_str(items[1])?))
                } else {
                    Err(ParseError("Error: FromStr for Instr - var".to_string()))
                }
            }
            "store"     => { 
                if items.len() == 2 {
                    Ok(Store(u32::from_str(items[1])?))
                } else {
                    Err(ParseError("Error: FromStr for Instr - store".to_string()))
                }
            }
            "setframe"  => {  
                if items.len() == 2 {
                    Ok(SetFrame(u32::from_str(items[1])?))
                } else {
                    Err(ParseError("Error: FromStr for Instr - setframe".to_string()))
                }
            }
            "print" => {
                if items.len() == 1 {
                    Ok(Print)
                } else {
                    Err(ParseError("Error: FromStr for Instr - print".to_string()))
                }
            }
            "size" => {
                if items.len() == 1 {
                    Ok(Size)
                } else {
                    Err(ParseError("Error: FromStr for Instr - size".to_string()))
                }
            }
            _           => Err(ParseError("Error: FromStr for Instr - default - Not an Instruction".to_string()))
        }
    }
}

fn parse_label(s: &str) -> Result<Label, ParseError> {
    // Create a vec of chars that can be used to check at specific locations
    let temp_str:Vec<char> = s.chars().collect();

    match temp_str[0] {
        'L' => {
            // iterate over all of the values and see if they are a letter in the alphabet or a number
            if temp_str[1..].iter().all(|&ch| ch.is_alphanumeric()) {
                return Ok(Label::from(s));
            } else {
                // Meaning that the label is incorrectly named
                return Err(ParseError("Error: parse_label function. Else case for 'L'. Incorrectly named label".to_string()));
            }
        }
        '_' => {
            match temp_str[1] {
                'L' => {
                    // iterate over all of the values and see if they are a letter in the alphabet or a number
                    if temp_str[2..].iter().all(|&ch| ch.is_alphanumeric()) {
                        return Ok(Label::from(s));
                    } else {
                        return Err(ParseError("Error: parse_label function. Else case for '_L'.".to_string()));
                    }
                }
                // Meaning that the label is incorrectly named
                _   => Err(ParseError("Error: parse_label function. Match2. Incorrectly named label".to_string()))
            }
        }
        _   => Err(ParseError("Error: parse_label function. Default match. Bottom.".to_string()))
    }
}

impl FromStr for PInstr {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let words: Vec<&str> = s.split_whitespace().collect();
        
        match words[0] {
            "push"  => { 
                if words.len() != 2 {
                    Err(ParseError("Error: FromStr for PInstr - push".to_string()))
                } else {
                    match parse_label(words[1]) {
                        // If it is a label, PPush that label
                        Ok(temp_label)  => Ok(PPush(temp_label)),
                        // If it is not a label, check it to be another regular instruction (regular push)
                        Err(_)          => Ok(PI(Instr::from_str(s)?))       
                    }
                }
            } 
            _       =>  { 
                match Instr::from_str(s) {
                    // If legal, pass it as a legal instruction
                    Ok(temp_instr)      => Ok(PI(temp_instr)),
                    Err(_)     => {
                        // Check for a : and remove it if one is found (checking if it is a label or not)
                        if &s[s.len() - 1 ..] == ":" {
                            match parse_label(&s[.. s.len() - 1]) {
                                // Check if it is a label if so it is a legal move
                                Ok(temp_label)  => Ok(PLabel(temp_label)),
                                // If a : appears, it will be an error since it should not occur
                                Err(_)          => Err(ParseError("Error: FromStr for PInstr - inclosed match".to_string()))
                            }
                        } else {
                            Err(ParseError("Error: FromStr for PInstr - bottom match".to_string()))
                        }
                    }
                }
            }
        }
    }
}

/// Parse an assembly program from a string.
pub fn parse_prog(s: &str) -> Result<Vec<PInstr>, ParseError> {
    s.lines().map(|l| l.parse()).collect()
}

/// Test to_string and from_string implementations (to_string comes
/// for free from Display).
#[test]
fn test_isa_parse() -> Result<(), ParseError> {
    assert_eq!(PLabel("Ltest".into()), PLabel("Ltest".into()).to_string().parse()?);
    assert_eq!(PPush("Ltest".into()), PPush("Ltest".into()).to_string().parse()?);
    let pinstrs: Vec<PInstr> = vec![Push(Vi32(123)), Pop, Peek(45), Unary(Neg),
				    Binary(Lt), Swap, Alloc, Set, Get, Var(65),
				    Store(5), Call, Ret, Branch, Halt]
	.into_iter().map(PI).collect();
    for pinstr in pinstrs {
	assert_eq!(pinstr, pinstr.to_string().parse()?);
    }
    Ok(())
}


////////////////////////////////////////////////////////////////////////
// ToBytes trait implementations
////////////////////////////////////////////////////////////////////////

impl ToBytes for u32 {
    fn to_bytes(&self) -> Vec<u8> {
        self.to_be_bytes().to_vec()
    }
}

impl ToBytes for i32 {
    fn to_bytes(&self) -> Vec<u8> {
        self.to_be_bytes().to_vec()
    }
}

impl ToBytes for Unop {
    fn to_bytes(&self) -> Vec<u8> {
        match self {
            Neg => vec![0b00000000],
        }
    }
}

impl ToBytes for Binop {
    fn to_bytes(&self) -> Vec<u8> {
        match self {
            Add =>  vec![0b00000000],
            Mul =>  vec![0b00000001],
            Sub =>  vec![0b00000010],
            Div =>  vec![0b00000011],
            Lt  =>  vec![0b00000100],
            Eq  =>  vec![0b00000101],
        }   
    }
}

impl ToBytes for Val {
    fn to_bytes(&self) -> Vec<u8> {
        let mut vector: Vec<u8> = vec![];
        match self {
            Vunit           => vec![0b00000000],
            Vi32(i)         => { 
                vector.push(0b00000001);
                vector.append(&mut i32::to_bytes(i));
                vector
            }
            Vbool(true)     => vec![0b00000010],
            Vbool(false)    => vec![0b00000011],
            Vloc(u)         => { 
                vector.push(0b00000100);
                vector.append(&mut u32::to_bytes(u));
                vector
            }
            Vundef          => vec![0b00000101],
            _               => panic!("Error in ToBytes for Val")
        }
    }
}

impl ToBytes for Instr {
    fn to_bytes(&self) -> Vec<u8> {
        let mut vector: Vec<u8> = vec![];
        match self {
            Push(v)         => { 
                vector.push(0b00000000);
                vector.append(&mut Val::to_bytes(v));
                vector
            },
            Pop             => vec![0b00000001],
            Peek(v)         => { 
                vector.push(0b00000010);
                vector.append(&mut u32::to_bytes(v));
                vector
            },
            Unary(u)        => { 
                vector.push(0b00000011);
                vector.append(&mut Unop::to_bytes(u));
                vector
            },
            Binary(b)       => { 
                vector.push(0b00000100);
                vector.append(&mut Binop::to_bytes(b));
                vector
            },
            Swap            => vec![0b00000101],
            Alloc           => vec![0b00000110],
            Set             => vec![0b00000111],
            Get             => vec![0b00001000],
            Var(u)          => { 
                vector.push(0b00001001);
                vector.append(&mut u32::to_bytes(u));
                vector
            },
            Store(u)        => { 
                vector.push(0b00001010);
                vector.append(&mut u32::to_bytes(u));
                vector
            },
            SetFrame(u)     => { 
                vector.push(0b00001011);
                vector.append(&mut u32::to_bytes(u));
                vector
            },
            Call            => vec![0b00001100],
            Ret             => vec![0b00001101],
            Branch          => vec![0b00001110],
            Halt            => vec![0b00001111],
            Print           => vec![0b00010000],
            Size            => vec![0b00010001],
        }
    }
}

////////////////////////////////////////////////////////////////////////
// FromBytes trait implementations
////////////////////////////////////////////////////////////////////////

impl FromBytes for u32 {
    type Err = ParseError;
    fn from_bytes<T: Iterator<Item=u8>>(bytes: &mut T) -> Result<u32, ParseError> {
        let vec: Vec<u8> = bytes.take(4).collect();
        if vec.len() == 4 {
            Ok(u32::from_be_bytes(vec.try_into().unwrap()))
        }
        else {
            Err(ParseError("Error: from_bytes u32".to_string()))
        }
    }
}

impl FromBytes for i32 {
    type Err = ParseError;
    fn from_bytes<T: Iterator<Item=u8>>(bytes: &mut T) -> Result<i32, ParseError> {
        let vec: Vec<u8> = bytes.take(4).collect();
        if vec.len() == 4 {
            Ok(i32::from_be_bytes(vec.try_into().unwrap()))
        }
        else {
            Err(ParseError("Error: from_bytes i32".to_string()))
        }
    }
}

impl FromBytes for Unop {
    type Err = ParseError;
    fn from_bytes<T: Iterator<Item=u8>>(bytes: &mut T) -> Result<Unop, ParseError> {
        let item;
        match bytes.next() {
            Some(i) => item = i,
            None => return Err(ParseError("Error: from_bytes() For Unop - None".to_string())),
        };
        match item {
            0b00000000 => Ok(Neg),
            _ => Err(ParseError("Error: from_bytes() For Unop - Neg".to_string()))
        }
    }
}

impl FromBytes for Binop {
    type Err = ParseError;
    fn from_bytes<T: Iterator<Item=u8>>(bytes: &mut T) -> Result<Binop, ParseError> {
        let item;
        match bytes.next() {
            Some(i) => item = i,
            None => return Err(ParseError("Error: from_bytes() For Binop - None".to_string())),
        };
        match item {
            0b00000000 => Ok(Add),
            0b00000001 => Ok(Mul),
            0b00000010 => Ok(Sub),
            0b00000011 => Ok(Div),
            0b00000100 => Ok(Lt),
            0b00000101 => Ok(Eq),
            _ => Err(ParseError("Error: from_bytes() For Binop - Operator not supported".to_string())),
        }
    }
}

impl FromBytes for Val {
    type Err = ParseError;
    fn from_bytes<T: Iterator<Item=u8>>(bytes: &mut T) -> Result<Val, ParseError> {
        let item;
        match bytes.next() {
            Some(i) => item = i,
            None => return Err(ParseError("Error: from_bytes() For Val - None".to_string())),
        };
        match item {
            0b00000000 => Ok(Vunit),
            0b00000101 => Ok(Vundef),
            0b00000010 => Ok(Vbool(true)),
            0b00000011 => Ok(Vbool(false)),
            0b00000001 => Ok(Vi32(i32::from_bytes(bytes)?)),
            0b00000100 => Ok(Vloc(u32::from_bytes(bytes)?)),
            _          => Err(ParseError("Error: from_bytes() For Val - Not a valid bytecode".to_string())) 
        }
    }
}

impl FromBytes for Instr {
    type Err = ParseError;
    fn from_bytes<T: Iterator<Item=u8>>(bytes: &mut T) -> Result<Instr, ParseError> {
        let item;
        match bytes.next() {
            Some(i) => item = i,
            None => return Err(ParseError("Error: from_bytes() For Instr - None".to_string())),
        };
        match item {
            0b00000001 => Ok(Pop),
            0b00000101 => Ok(Swap),
            0b00000110 => Ok(Alloc),
            0b00000111 => Ok(Set),
            0b00001000 => Ok(Get),
            0b00001100 => Ok(Call),
            0b00001101 => Ok(Ret),
            0b00001110 => Ok(Branch),
            0b00001111 => Ok(Halt),
            0b00010000 => Ok(Print),
            0b00010001 => Ok(Size),
            0b00000000 => Ok(Push(Val::from_bytes(bytes)?)),
            0b00000010 => Ok(Peek(u32::from_bytes(bytes)?)),
            0b00000011 => Ok(Unary(Unop::from_bytes(bytes)?)),
            0b00001001 => Ok(Var(u32::from_bytes(bytes)?)),
            0b00001010 => Ok(Store(u32::from_bytes(bytes)?)),
            0b00000100 => Ok(Binary(Binop::from_bytes(bytes)?)),
            0b00001011 => Ok(SetFrame(u32::from_bytes(bytes)?)),
            _          => Err(ParseError("Error: from_bytes() For Instr - Not a Valid Instruction".to_string())),
        }
    }
}

impl FromBytes for Vec<Instr> {
    type Err = ParseError;
    fn from_bytes<T: Iterator<Item=u8>>(bytes: &mut T) -> Result<Vec<Instr>, ParseError> {
        let mut instructions: Vec<Instr> = vec![];
        // get instruction counter
        let instr_count = u32::from_bytes(bytes)?;
        //println!("{}", instr_count);
        // read n instructions
        for _ in 0..instr_count {
            instructions.push(Instr::from_bytes(bytes)?);
        }
        Ok(instructions)
    }
}

/// Test to_bytes and from_bytes implementations.
#[test]
fn test_isa_serialize() -> Result<(), ParseError> {
    let instrs: Vec<Instr> = vec![Push(Vi32(123)), Pop, Peek(45), Unary(Neg),
    				  Binary(Lt), Swap, Alloc, Set, Get, Var(65),
    				  Store(5), Call, Ret, Branch, Halt];
    for instr in instrs {
	assert_eq!(instr, Instr::from_bytes(&mut instr.to_bytes().into_iter())?);
    }
    Ok(())
}

// Put all your test cases in this module.
#[cfg(test)]
mod tests {
    use super::*;

    // Example test case.
    #[test]
    fn test_1_example_test() {
        assert_eq!(Instr::from_str("push 123").unwrap(), Push(Vi32(123)));
        assert_eq!(PInstr::from_str("Labc123:").unwrap(),
		   PInstr::PLabel(String::from("Labc123"))
        );
    }
    #[test]
    // Checks Binops, Unop, and Val
    fn test_2_binops_unop_val() {
        assert_eq!(Binop::from_str("+").unwrap(), Add);
        assert_eq!(Binop::from_str("-").unwrap(), Sub);
        assert_eq!(Binop::from_str("*").unwrap(), Mul);
        assert_eq!(Binop::from_str("/").unwrap(), Div);
        assert_eq!(Binop::from_str("==").unwrap(), Eq);
        assert_eq!(Binop::from_str("<").unwrap(), Lt);
        assert_eq!(Unop::from_str("neg").unwrap(), Neg);
        assert_eq!(Val::from_str("tt").unwrap(), Vunit);
        assert_eq!(Val::from_str("undef").unwrap(), Vundef);
        assert_eq!(Val::from_str("true").unwrap(), Vbool(true));
        assert_eq!(Val::from_str("false").unwrap(), Vbool(false));
    }
    #[test]
    // Checks Instructions
    fn test_3_instr() {
        assert_eq!(Instr::from_str("swap").unwrap(), Swap);
        assert_eq!(Instr::from_str("alloc").unwrap(), Alloc);
        assert_eq!(Instr::from_str("set").unwrap(), Set);
        assert_eq!(Instr::from_str("get").unwrap(), Get);
        assert_eq!(Instr::from_str("pop").unwrap(), Pop);
        assert_eq!(Instr::from_str("call").unwrap(), Call);
        assert_eq!(Instr::from_str("ret").unwrap(), Ret);
        assert_eq!(Instr::from_str("branch").unwrap(), Branch);
        assert_eq!(Instr::from_str("halt").unwrap(), Halt);
        assert_eq!(Instr::from_str("push 5").unwrap(), Push(Vi32(5)));
        assert_eq!(Instr::from_str("push 000").unwrap(), Push(Vi32(0)));
        assert_eq!(Instr::from_str("push -15").unwrap(), Push(Vi32(-15)));
        assert_eq!(Instr::from_str("peek 5").unwrap(), Peek(5));
        assert_eq!(Instr::from_str("peek 000").unwrap(), Peek(0));
        assert_eq!(Instr::from_str("push undef").unwrap(), Push(Vundef));
        assert_eq!(Instr::from_str("push tt").unwrap(), Push(Vunit));
        assert_eq!(Instr::from_str("var 4").unwrap(), Var(4 as u32));
        assert_eq!(Instr::from_str("store 3").unwrap(), Store(3 as u32));
        assert_eq!(Instr::from_str("setframe 40").unwrap(), SetFrame(40 as u32));
        assert_eq!(Instr::from_str("peek 3").unwrap(), Peek(3 as u32));
    }
    #[test]
    // Checks for ParseErrors
    fn test_4_parse_errors() {
        assert!(matches!(PInstr::from_str("push Label:"), Err(ParseError(_)))); 
        assert!(matches!(Instr::from_str("set get"), Err(ParseError(_))));
        assert!(matches!(Instr::from_str("get set"), Err(ParseError(_))));
        assert!(matches!(Instr::from_str("push set"), Err(ParseError(_))));
        assert!(matches!(Instr::from_str("peek push"), Err(ParseError(_))));
        assert!(matches!(Instr::from_str("peek tt"), Err(ParseError(_))));
        assert!(matches!(Val::from_str("tt 5"), Err(ParseError(_))));
        assert!(matches!(Instr::from_str("push f"), Err(ParseError(_))));
        assert!(matches!(Instr::from_str("peek"), Err(ParseError(_))));
        assert!(matches!(Instr::from_str("peek -1"), Err(ParseError(_))));
        assert!(matches!(Instr::from_str("push"), Err(ParseError(_))));
        assert!(matches!(Instr::from_str("binary &"), Err(ParseError(_))));
        assert!(matches!(Instr::from_str("binary !"), Err(ParseError(_))));
        assert!(matches!(Instr::from_str("binary <="), Err(ParseError(_))));
        assert!(matches!(Instr::from_str("binary >="), Err(ParseError(_))));
        assert!(matches!(Instr::from_str("binary ||"), Err(ParseError(_))));
        assert!(matches!(Instr::from_str("binary &&"), Err(ParseError(_))));
    }
    #[test]
    // Checks Instructions for Unary and Binary
    fn test_5_unary_binary() {
        assert_eq!(Instr::from_str("unary neg").unwrap(), Unary(Neg));
        assert_eq!(Instr::from_str("binary +").unwrap(), Binary(Add));
        assert_eq!(Instr::from_str("binary -").unwrap(), Binary(Sub));
        assert_eq!(Instr::from_str("binary *").unwrap(), Binary(Mul));
        assert_eq!(Instr::from_str("binary /").unwrap(), Binary(Div));
        assert_eq!(Instr::from_str("binary ==").unwrap(), Binary(Eq));
        assert_eq!(Instr::from_str("binary <").unwrap(), Binary(Lt));
    }
    #[test]
    // Checks Bytecode 
    fn test_6_bytecode() {
        assert_eq!(vec![0b00000011, 0b00000000], Instr::to_bytes(&Unary(Neg)));
        assert_eq!(vec![0b00000100, 0b00000000], Instr::to_bytes(&Binary(Add)));
        assert_eq!(vec![0b00000100, 0b00000001], Instr::to_bytes(&Binary(Mul)));
        assert_eq!(vec![0b00000100, 0b00000010], Instr::to_bytes(&Binary(Sub)));
        assert_eq!(vec![0b00000100, 0b00000011], Instr::to_bytes(&Binary(Div)));
        assert_eq!(vec![0b00000100, 0b00000100], Instr::to_bytes(&Binary(Lt)));
        assert_eq!(vec![0b00000100, 0b00000101], Instr::to_bytes(&Binary(Eq)));
        assert_eq!(Val::to_bytes(&Vunit), vec![0b00000000 as u8]);
        assert_eq!(Val::to_bytes(&Vbool(true)), vec![0b00000010 as u8]);
        assert_eq!(Val::to_bytes(&Vbool(false)), vec![0b00000011 as u8]);
        assert_eq!(Val::to_bytes(&Vi32(1000 as i32)), vec![0b00000001 as u8, 0, 0, 3, 232]);
        assert_eq!(Val::to_bytes(&Vi32(-1000 as i32)), vec![0b00000001 as u8, 255, 255, 252, 24]);
        assert_eq!(Val::to_bytes(&Vundef), vec![0b00000101 as u8]);
        assert_eq!(Binop::to_bytes(&Add), vec![0b00000000 as u8]);
        assert_eq!(Binop::to_bytes(&Mul), vec![0b00000001 as u8]);
        assert_eq!(Binop::to_bytes(&Sub), vec![0b00000010 as u8]);
        assert_eq!(Binop::to_bytes(&Div), vec![0b00000011 as u8]);
        assert_eq!(Binop::to_bytes(&Lt), vec![0b00000100 as u8]);
        assert_eq!(Binop::to_bytes(&Eq), vec![0b00000101 as u8]);
        assert_eq!(Unop::to_bytes(&Neg), vec![0b00000000 as u8]);
        assert_eq!(Instr::to_bytes(&Pop), vec![0b00000001 as u8]);
        assert_eq!(Instr::to_bytes(&Swap), vec![0b00000101 as u8]);
        assert_eq!(Instr::to_bytes(&Alloc), vec![0b00000110 as u8]);
        assert_eq!(Instr::to_bytes(&Set), vec![0b00000111 as u8]);
        assert_eq!(Instr::to_bytes(&Get), vec![0b00001000 as u8]);
        assert_eq!(Instr::to_bytes(&Call), vec![0b00001100 as u8]);
        assert_eq!(Instr::to_bytes(&Ret), vec![0b00001101 as u8]);
        assert_eq!(Instr::to_bytes(&Branch), vec![0b00001110 as u8]);
        assert_eq!(Instr::to_bytes(&Halt), vec![0b00001111 as u8]);
        assert_eq!(Instr::to_bytes(&Unary(Neg)), vec![0b00000011 as u8, 0b00000000 as u8]);
        assert_eq!(Instr::to_bytes(&Push(Vundef)), vec![0b00000000 as u8, 0b00000101 as u8]);
        assert_eq!(Instr::to_bytes(&Peek(1000 as u32)), vec![0b00000010 as u8, 0 as u8, 0 as u8, 3 as u8, 232 as u8]);
        assert_eq!(Instr::to_bytes(&Peek(1000 as u32)), vec![2 as u8, 0b00000000 as u8, 0b00000000 as u8, 0b00000011 as u8, 0b11101000 as u8]);
        assert_eq!(Instr::to_bytes(&Binary(Div)), vec![0b00000100 as u8, 0b00000011 as u8]);
        assert_eq!(Instr::to_bytes(&Var(50 as u32)), vec![0b00001001 as u8, 0 as u8, 0 as u8, 0 as u8, 50 as u8]);
        assert_eq!(Instr::to_bytes(&Store(256 as u32)), vec![0b00001010 as u8, 0 as u8, 0 as u8, 1 as u8, 0 as u8]);
        assert_eq!(Instr::to_bytes(&SetFrame(20 as u32)), vec![0b00001011 as u8, 0 as u8, 0 as u8, 0 as u8, 20 as u8]);
        assert_eq!(Val::to_bytes(&Vloc(257 as u32)), vec![0b00000100 as u8, 0 as u8, 0 as u8, 1 as u8, 1 as u8]);
    }
    // Tests Labels
    #[test]
    fn test_7_labels() {
        assert_eq!(PInstr::from_str("Lmain:").unwrap(),
            PLabel(String::from("Lmain"))
        );
        assert_eq!(PInstr::from_str("La:").unwrap(),
            PLabel(String::from("La"))
        );
        assert_eq!(PInstr::from_str("_La:").unwrap(),
            PLabel(String::from("_La"))
        );
        assert_eq!(PInstr::from_str("push Label").unwrap(), PPush(String::from("Label")));
    }
    // Test instruction from bytecode Instructions
    #[test]
    fn test_8_instr_from_bytes() {
        assert_eq!(Instr::from_bytes(&mut Pop.to_bytes().into_iter()).unwrap(), Pop);
        assert_eq!(Instr::from_bytes(&mut Swap.to_bytes().into_iter()).unwrap(), Swap);
        assert_eq!(Instr::from_bytes(&mut Alloc.to_bytes().into_iter()).unwrap(), Alloc);
        assert_eq!(Instr::from_bytes(&mut Set.to_bytes().into_iter()).unwrap(), Set);
        assert_eq!(Instr::from_bytes(&mut Get.to_bytes().into_iter()).unwrap(), Get);
        assert_eq!(Instr::from_bytes(&mut Call.to_bytes().into_iter()).unwrap(), Call);
        assert_eq!(Instr::from_bytes(&mut Ret.to_bytes().into_iter()).unwrap(), Ret);
        assert_eq!(Instr::from_bytes(&mut Branch.to_bytes().into_iter()).unwrap(), Branch);
        assert_eq!(Instr::from_bytes(&mut Halt.to_bytes().into_iter()).unwrap(), Halt);
        assert_eq!(Instr::from_bytes(&mut Push(Vunit).to_bytes().into_iter()).unwrap(), Push(Vunit));
        assert_eq!(Instr::from_bytes(&mut Peek(1000 as u32).to_bytes().into_iter()).unwrap(), Peek(1000 as u32));
        assert_eq!(Instr::from_bytes(&mut Unary(Neg).to_bytes().into_iter()).unwrap(), Unary(Neg));
        assert_eq!(Instr::from_bytes(&mut Var(13).to_bytes().into_iter()).unwrap(), Var(13));
        assert_eq!(Instr::from_bytes(&mut Store(100).to_bytes().into_iter()).unwrap(), Store(100));
        assert_eq!(Instr::from_bytes(&mut Binary(Mul).to_bytes().into_iter()).unwrap(), Binary(Mul));
    }
    #[test]
    fn test_9_binop_val_from_bytes() {
        assert_eq!(Binop::from_bytes(&mut Add.to_bytes().into_iter()).unwrap(), Add);
        assert_eq!(Binop::from_bytes(&mut Mul.to_bytes().into_iter()).unwrap(), Mul);
        assert_eq!(Binop::from_bytes(&mut Sub.to_bytes().into_iter()).unwrap(), Sub);
        assert_eq!(Binop::from_bytes(&mut Div.to_bytes().into_iter()).unwrap(), Div);
        assert_eq!(Binop::from_bytes(&mut Lt.to_bytes().into_iter()).unwrap(), Lt);
        assert_eq!(Binop::from_bytes(&mut Eq.to_bytes().into_iter()).unwrap(), Eq);
        assert_eq!(Val::from_bytes(&mut Vundef.to_bytes().into_iter()).unwrap(), Vundef);
        assert_eq!(Val::from_bytes(&mut Vbool(true).to_bytes().into_iter()).unwrap(), Vbool(true));
        assert_eq!(Val::from_bytes(&mut Vbool(false).to_bytes().into_iter()).unwrap(), Vbool(false));
        assert_eq!(Val::from_bytes(&mut Vi32(-10).to_bytes().into_iter()).unwrap(), Vi32(-10));
        assert_eq!(Val::from_bytes(&mut Vloc(23).to_bytes().into_iter()).unwrap(), Vloc(23));
    }
}