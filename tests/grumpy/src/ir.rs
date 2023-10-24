//! Grumpy intermediate representation.
//!
//! This module contains the types of values, expressions, etc. for
//! GrumpyIR programs.

use std::collections::HashSet;
use std::convert::{TryFrom, TryInto};
use std::str::FromStr;
use sexp::{Atom, Atom::*, Sexp, Sexp::*};
use crate::{ParseError};
use crate::isa::{self, Binop, Binop::*, Unop, Unop::*};

/// GrumpyIR values.
#[derive(Debug, Clone, PartialEq)]
pub enum Val {
    /// 32-bit signed integers
    Num(i32),
    /// Boolean values
    Bool(bool),
    /// The unit value
    Unit
}

/// Type synonym for names appearing in GrumpyIR programs.
pub type Name = String;

/// GrumpyIR expressions.
#[derive(Debug, Clone, PartialEq)]
pub enum Exp {
    /// Values.
    Val(Val),
    /// Variables.
    Var(Name),
    /// Unary operation u applied to expression e.
    Unary(Unop, Box<Exp>),
    /// Binary operation b applied to expressions e1 and e2.
    Binary(Binop, Box<Exp>, Box<Exp>),
    /// Let x equal the result of e1 in e2 (in which x may appear free).
    Let(Name, Box<Exp>, Box<Exp>),
    /// Sequential composition (do e1 then e2).
    Seq(Box<Exp>, Box<Exp>),
    /// Allocate an array of size esize, initialized at each index to einit.
    Alloc(Box<Exp>, Box<Exp>),
    /// Update array earr at index eix to the value of e.
    Set(Box<Exp>, Box<Exp>, Box<Exp>),
    /// Get the value at index eix of array earr.
    Get(Box<Exp>, Box<Exp>),
    /// If econd evaluates to true then e1, else e2.
    Cond(Box<Exp>, Box<Exp>, Box<Exp>),
    /// A pointer to function f.
    Funptr(Name),
    /// Call function pointer e with arguments.
    Call(Box<Exp>, Vec<Exp>),
    While(Box<Exp>, Box<Exp>),
    Print(Box<Exp>),
    Size(Box<Exp>),
}

/// Create a singleton HashSet.
fn single<T: std::cmp::Eq + core::hash::Hash>(x: T) -> HashSet<T> {
    let mut s = HashSet::new();
    s.insert(x);
    s
}

/// Big union of HashSets.
fn union<T: std::cmp::Eq + core::hash::Hash>(sets: Vec<HashSet<T>>) -> HashSet<T> {
    sets.into_iter().fold(HashSet::new(), |mut acc, s| {
        acc.extend(s); acc
    })
}

impl Exp {
    /// Compute the set of variables bound (by let expressions) within
    /// an expression.
    pub fn bound_vars(&self) -> HashSet<Name> {
	use Exp::*;
	match self {
	    Unary(_, e) => e.bound_vars(),
	    Binary(_, e1, e2) =>
                union(vec![e1.bound_vars(), e2.bound_vars()]),
	    Let(x, e1, e2) =>
                union(vec![e1.bound_vars(), e2.bound_vars(), single(x.clone())]),
	    Seq(e1, e2) =>
		e1.bound_vars().union(&e2.bound_vars()).cloned().collect(),
	    Alloc(e1, e2) =>
		e1.bound_vars().union(&e2.bound_vars()).cloned().collect(),
	    Set(e1, e2, e3) =>
                union(vec![e1.bound_vars(), e2.bound_vars(), e3.bound_vars()]),
	    Get(e1, e2) =>
		e1.bound_vars().union(&e2.bound_vars()).cloned().collect(),
	    Cond(e1, e2, e3) =>
                union(vec![e1.bound_vars(), e2.bound_vars(), e3.bound_vars()]),
	    Call(f, args) =>
                union(vec![f.bound_vars(),
                           union(args.into_iter().map(|arg| arg.bound_vars()).collect())]),
        While(cond, body) => union(vec![cond.bound_vars(), body.bound_vars()]),
        Print(e) => e.bound_vars(),
        Size(e) => e.bound_vars(),
	    _ => HashSet::new()
	}
    }
}

/// GrumpyIR types.
#[derive(Debug, Clone)]
pub enum Type {
    /// 32-bit integers.
    I32,
    /// Booleans.
    Bool,
    /// The unit type.
    Unit,
    /// Arrays of values of type ty.
    Array(Box<Type>)
}

/// A parameter is a (name, type) pair.
#[derive(Debug, Clone)]
pub struct Param(pub Name, pub Type);

/// GrumpyIR functions.
#[derive(Debug, Clone)]
pub struct Fun {
    /// Name of the function.
    pub name: Name,
    /// Formal parameters of the function.
    pub params: Vec<Param>,
    /// Return type of the function.
    pub ret_ty: Type,
    /// Body of the function.
    pub body: Exp
}

impl Fun {
    pub fn new(name: Name, params: Vec<Param>, ret_ty: Type, body: Exp) -> Fun {
	Fun { name: name, params: params, ret_ty: ret_ty, body: body }
    }
}

/// GrumpyIR programs.
#[derive(Debug)]
pub struct Prog {
    /// Functions defined in the program.
    pub funs: Vec<Fun>,
    /// The "main" expression to be evaluated.
    pub main: Exp
}


////////////////////////////////////////////////////////////////////////
// IR Parsing
////////////////////////////////////////////////////////////////////////

// Sexp helpers

fn as_atom(s: &Sexp) -> Result<&Atom, String> {
    match s {
	Atom(a) => Ok(a),
	_ => Err(format!("expected atom, got {}", s).into())
    }
}

fn as_list(s: &Sexp) -> Result<&Vec<Sexp>, String> {
    match s {
	List(l) => Ok(l),
	_ => Err(format!("expected list, got {}", s).into())
    }
}

fn as_listn(s: &Sexp, n: usize) -> Result<&Vec<Sexp>, String> {
    match s {
	List(l) if l.len() == n => Ok(l),
	_ => Err(format!("expected list of length {}, got {}", n, s).into())
    }
}

fn as_sym(s: &Sexp) -> Result<&str, String> {
    match s {
	Atom(S(s)) => Ok(s),
	_ => Err("expected S atom".into())
    }
}

fn assert_sym(s: &Sexp, sym: &str) -> Result<(), String> {
    match s {
	Atom(S(s)) if s == sym => Ok(()),
	_ => Err(format!("expected symbol {}, got {}", sym, s).into())
    }
}

// Parsing values

impl TryFrom<Sexp> for Val {
    type Error = ParseError;
    fn try_from(sexp: Sexp) -> Result<Self, Self::Error> {
	use Val::*;
	match as_atom(&sexp)? {
	    S(s) => match &s[..] {
		"true" => Ok(Bool(true)),
		"false" => Ok(Bool(false)),
		"tt" => Ok(Unit),
		_ => Err(format!("invalid atom: {}", s).into())
	    }
	    I(i) => Ok(Num(*i as i32)),
	    _ => Err(format!("invalid sexp: {}", sexp).into())
	}
    }
}

// Parsing expressions

/// Parse a value expression.
fn parse_val(sexp: &Sexp) -> Result<Exp, ParseError> {
    Ok(Exp::Val(Val::try_from(sexp.clone())?))
}

/// Parse a variable expression.
fn parse_var(sexp: &Sexp) -> Result<Exp, ParseError> {
    Ok(Exp::Var(as_sym(sexp)?.into()))
}

/// Parse a unary expression.
fn parse_unary(sexp: &Sexp) -> Result<Exp, ParseError> {
    let l = as_listn(sexp, 2)?;
    let e = Box::new(l[1].clone().try_into()?);
    match as_sym(&l[0])? {
	"neg" => Ok(Exp::Unary(Neg, e)),
	_ => Err("".into())
    }
}

/// Parse a binary expression.
fn parse_binary(sexp: &Sexp) -> Result<Exp, ParseError> {
    let l = as_listn(sexp, 3)?;
    let e1 = Box::new(l[1].clone().try_into()?);
    let e2 = Box::new(l[2].clone().try_into()?);
    Ok(Exp::Binary(match as_sym(&l[0])? {
	"+"  => Add,
	"*"  => Mul,
	"-"  => Sub,
	"/"  => Div,
	"<"  => Lt,
	"==" => Eq,
	b => return Err(format!("unknown binop: {}", b).into())
    }, e1, e2))
}

/// Parse a let expression.
fn parse_let(sexp: &Sexp) -> Result<Exp, ParseError> {
    let l = as_listn(sexp, 4)?;
    assert_sym(&l[0], "let")?;
    let x = as_sym(&l[1])?.into();
    let e1 = Box::new(l[2].clone().try_into()?);
    let e2 = Box::new(l[3].clone().try_into()?);
    Ok(Exp::Let(x, e1, e2))
}

/// Parse a sequence expression.
fn parse_seq(sexp: &Sexp) -> Result<Exp, ParseError> {
    let l = as_listn(sexp, 3)?;
    assert_sym(&l[0], "seq")?;
    let e1 = Box::new(l[1].clone().try_into()?);
    let e2 = Box::new(l[2].clone().try_into()?);
    Ok(Exp::Seq(e1, e2))
}

/// Parse an alloc expression.
fn parse_alloc(sexp: &Sexp) -> Result<Exp, ParseError> {
    let l = as_listn(sexp, 3)?;
    assert_sym(&l[0], "alloc")?;
    let e1 = Box::new(l[1].clone().try_into()?);
    let e2 = Box::new(l[2].clone().try_into()?);
    Ok(Exp::Alloc(e1, e2))
}

/// Parse a set expression.
fn parse_set(sexp: &Sexp) -> Result<Exp, ParseError> {
    let l = as_listn(sexp, 4)?;
    assert_sym(&l[0], "set")?;
    let e1 = Box::new(l[1].clone().try_into()?);
    let e2 = Box::new(l[2].clone().try_into()?);
    let e3 = Box::new(l[3].clone().try_into()?);
    Ok(Exp::Set(e1, e2, e3))
}

/// Parse a get expression.
fn parse_get(sexp: &Sexp) -> Result<Exp, ParseError> {
    let l = as_listn(sexp, 3)?;
    assert_sym(&l[0], "get")?;
    let e1 = Box::new(l[1].clone().try_into()?);
    let e2 = Box::new(l[2].clone().try_into()?);
    Ok(Exp::Get(e1, e2))
}

/// Parse a conditional expression.
fn parse_cond(sexp: &Sexp) -> Result<Exp, ParseError> {
    let l = as_listn(sexp, 4)?;
    assert_sym(&l[0], "cond")?;
    let e1 = Box::new(l[1].clone().try_into()?);
    let e2 = Box::new(l[2].clone().try_into()?);
    let e3 = Box::new(l[3].clone().try_into()?);
    Ok(Exp::Cond(e1, e2, e3))
}

/// Parse a function pointer expression.
fn parse_funptr(sexp: &Sexp) -> Result<Exp, ParseError> {
    let l = as_listn(sexp, 2)?;
    assert_sym(&l[0], "funptr")?;
    let f = as_sym(&l[1])?.into();
    Ok(Exp::Funptr(f))
}

/// Parse a call expression.
fn parse_call(sexp: &Sexp) -> Result<Exp, ParseError> {
    let l = as_list(sexp)?;
    if l.len() < 2 {
	Err("expected at least two sexps".into())
    } else {
	assert_sym(&l[0], "call")?;
	let f = Box::new(l[1].clone().try_into()?);
	let args = l[2..].iter().map(|s| s.clone().try_into())
	    .collect::<Result<_, _>>()?;
	Ok(Exp::Call(f, args))
    }
}

/// Parse a call expression via the alternative syntax (sugar).
fn parse_call_sugar(sexp: &Sexp) -> Result<Exp, ParseError> {
    let l = as_list(sexp)?;
    if l.is_empty() {
	Err("empty list".into())
    } else {
	let f = as_sym(&l[0])?.into();
	let args = l[1..].iter().map(|s| s.clone().try_into())
	    .collect::<Result<_, _>>()?;
	Ok(Exp::Call(Box::new(Exp::Funptr(f)), args))
    }
}

/// Parse a while loop.
fn parse_while(sexp: &Sexp) -> Result<Exp, ParseError> {
    let l = as_listn(sexp, 3)?;
    assert_sym(&l[0], "while")?;
    let e1 = Box::new(l[1].clone().try_into()?);
    let e2 = Box::new(l[2].clone().try_into()?);
    Ok(Exp::While(e1, e2))
}

/// Parse the Print
fn parse_print(sexp: &Sexp) -> Result<Exp, ParseError> {
    let l = as_listn(sexp, 2)?;
    assert_sym(&l[0], "print")?;
    let e1 = Box::new(l[1].clone().try_into()?);
    Ok(Exp::Print(e1))
}

/// Parse the Size
fn parse_size(sexp: &Sexp) -> Result<Exp, ParseError> {
    let l = as_listn(sexp, 2)?;
    assert_sym(&l[0], "size")?;
    let e1 = Box::new(l[1].clone().try_into()?);
    Ok(Exp::Size(e1))
}

/// Result type helper (big disjunction).
fn choice<T, R, E, F>(x: &T, e: E, fs: &[F]) -> Result<R, E>
    where F: Fn(&T) -> Result<R, E> {
    if fs.is_empty() {
	Err(e)
    } else {
	fs[0](x).or_else(|_| choice(x, e, &fs[1..]))
    }
}

impl TryFrom<Sexp> for Exp {
    type Error = ParseError;

    /// Parse a GrumpyIR expression from an s-expression.
    fn try_from(sexp: Sexp) -> Result<Self, Self::Error> {
	let choices = [
	    parse_val,
	    parse_var,
	    parse_unary,
	    parse_binary,
	    parse_let,
	    parse_seq,
	    parse_alloc,
	    parse_set,
	    parse_get,
	    parse_cond,
        parse_while,
        parse_print,
        parse_size,
	    parse_funptr,
	    parse_call,
	    parse_call_sugar,
	];
	choice(&sexp,
	       format!("exp: all choices failed when trying to parse {}", sexp).into(),
	       &choices)
    }
}

// Parsing types

fn parse_i32_ty(sexp: &Sexp) -> Result<Type, ParseError> {
    assert_sym(sexp, "i32")?;
    Ok(Type::I32)
}

fn parse_bool_ty(sexp: &Sexp) -> Result<Type, ParseError> {
    assert_sym(sexp, "bool")?;
    Ok(Type::Bool)
}

fn parse_unit_ty(sexp: &Sexp) -> Result<Type, ParseError> {
    assert_sym(sexp, "unit")?;
    Ok(Type::Unit)
}

fn parse_array_ty(sexp: &Sexp) -> Result<Type, ParseError> {
    let l = as_listn(sexp, 2)?;
    assert_sym(&l[0], "array")?;
    Ok(Type::Array(Box::new(l[1].clone().try_into()?)))
}

impl TryFrom<Sexp> for Type {
    type Error = ParseError;
    
    /// Parse a GrumpyIR type from an s-expression.
    fn try_from(sexp: Sexp) -> Result<Self, Self::Error> {
	let choices = [
	    parse_i32_ty,
	    parse_bool_ty,
	    parse_unit_ty,
	    parse_array_ty
	];
	choice(&sexp,
	       format!("type: all choices failed when trying to parse {}", sexp).into(),
	       &choices)
    }
}

// Parsing functions

impl TryFrom<Sexp> for Param {
    type Error = ParseError;
    fn try_from(sexp: Sexp) -> Result<Self, Self::Error> {
	let l = as_listn(&sexp, 2)?;
	let nm = as_sym(&l[0])?.into();
	let ty = l[1].clone().try_into()?;
	Ok(Param(nm, ty))
    }
}

impl TryFrom<Sexp> for Fun {
    type Error = ParseError;

    /// Parse a GrumpyIR function from an s-expression.
    fn try_from(s: Sexp) -> Result<Self, Self::Error> {
	let l = as_list(&s)?;
	if l.len() < 5 {
	    Err("expected list of length 5 or more".into())
	} else {
	    assert_sym(&l[0], "fun")?;
	    let f_nm = as_sym(&l[1])?.into();
	    let mut params = Vec::new();
	    for (i, s) in l[2..].iter().enumerate() {
		match s {
		    Atom(S(x)) if x == "->" => {
			if i == l.len()-5 {
			    return Ok(Fun::new(f_nm, params,
					       l[l.len()-2].clone().try_into()?,
					       l[l.len()-1].clone().try_into()?))
			} else {
			    return Err("expected type and body after '->'".into())
			}
		    }
		    _ => params.push(s.clone().try_into()?)
		}
	    }
	    Err("expected '->' symbol".into())
	}
    }
}

// Parsing programs

impl FromStr for Prog {
    type Err = ParseError;

    /// Parse a GrumpyIR program from a string slice. The strategy is
    /// to first parse the string to an s-expression (by wrapping it
    /// in parentheses so the whole thing can be parsed as a list
    /// s-expression), and then parse the program from that.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
	match sexp::parse(&(String::from("(") + s + ")"))? {
	    List(v) => {
		let mut funs: Vec<Fun> = Vec::new();
		for (i, sexp) in v.iter().enumerate() {
		    match sexp {
			Atom(S(s)) => match &s[..] {
			    "%" => {
				if i == v.len()-2 {
				    return Ok(Prog { funs: funs,
				    		     main: v[i+1].clone().try_into()? })
				} else {
				    return Err(format!(
					"expected exactly one expression after '%'").into())
				}
			    }
			    _ => return Err(format!("invalid atom: {}", s).into())
			}
			_ => funs.push(sexp.clone().try_into()?)
		    }
		}
		Err("expected '%'".into())
	    }
	    _ => Err("expected list".into())
	}
    }
}
