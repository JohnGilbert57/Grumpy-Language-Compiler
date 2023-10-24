//! The Grumpy compiler.

// Changes from PA3:
// * Declare new modules `ir` and `compile`.
// * New type `CompileError` for compile errors.

#![warn(clippy::all)]
use std::{error, fmt, io, num};

// Declare modules in the grumpy crate.
pub mod assemble;
pub mod compile;
pub mod ir;
pub mod isa;
pub mod vm;

/// Trait for types that can be serialized to a binary representation.
pub trait ToBytes {
    fn to_bytes(&self) -> Vec<u8>;
}

/// Trait for types that can be deserialized from a binary representation.
pub trait FromBytes : Sized {
    type Err;
    fn from_bytes<T: Iterator<Item=u8>>(v: &mut T) -> Result<Self, Self::Err>;
}

/// A type for parse errors.
#[derive(Debug)]
pub struct ParseError(String);

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl error::Error for ParseError {}
impl From<num::ParseIntError> for ParseError {
    fn from(err: num::ParseIntError) -> Self {
        ParseError(format!("{}", err))
    }
}
impl From<&str> for ParseError {
    fn from(s: &str) -> Self {
	ParseError(s.into())
    }
}
impl From<String> for ParseError {
    fn from(s: String) -> Self {
	ParseError(s)
    }
}
impl From<Box<sexp::Error>> for ParseError {
    fn from(err: Box<sexp::Error>) -> Self {
	ParseError(format!("{}", err))
    }
}
impl From<ParseError> for io::Error {
    fn from(err: ParseError) -> Self {
        io::Error::new(io::ErrorKind::Other, format!("{:?}", err))
    }
}

/// A type for VM errors.
#[derive(Debug)]
pub struct VMError(String);

impl fmt::Display for VMError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl error::Error for VMError {}

impl From<&str> for VMError {
    fn from(s: &str) -> Self {
	VMError(s.into())
    }
}

/// A type for compilation errors.
#[derive(Debug, PartialEq)]
pub struct CompileError(String);

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl std::error::Error for CompileError {}
impl From<&str> for CompileError {
    fn from(s: &str) -> Self {
	CompileError(s.into())
    }
}
impl From<CompileError> for std::io::Error {
    fn from(err: CompileError) -> Self {
	std::io::Error::new(std::io::ErrorKind::Other, format!("{:?}", err))
    }
}
