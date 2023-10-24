//! GrumpyIR compiler.
//!
//! This module contains the compiler from GrumpyIR to GrumpyVM
//! assembly code. Compilation is performed by `compile` methods on
//! GrumpyIR types.
//! 
//! Repo: https://github.com/OUCompilers/pa4-codegen-JohnGilbert57.git

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use crate::CompileError;
use crate::isa::{Instr, Label, PInstr, PInstr::*, Val::*, Binop, Unop};
use crate::ir::*;
use crate::ir::Val::*;

/// Global gensym counter for generating fresh names.
fn gensym() -> usize {
    static GENSYM: AtomicUsize = AtomicUsize::new(0);
    GENSYM.fetch_add(1, Ordering::SeqCst);
    GENSYM.load(Ordering::SeqCst)
}

/// Generate a fresh label using gensym.
fn fresh_label() -> Label {
    format!("_L{}", gensym())
}

/// The type of compilation environments.
struct Env {
    locals: HashMap<String, u32>
}

impl Env {
    fn mk(locals: HashMap<String, u32>) -> Env {
	Env { locals: locals }
    }
}

impl Val {
    /// Compile a value to a vector of pseudo-instructions (assembly code).
    fn compile(&self) -> Result<Vec<PInstr>, CompileError> {
        match self {
            Num(x) => Ok(vec![PI(Instr::Push(Vi32(*x)))]),
            Bool(b) => Ok(vec![PI(Instr::Push(Vbool(*b)))]),
            Unit => Ok(vec![PI(Instr::Push(Vunit))]),
           // _ => Err(CompileError("Error: compile() for val not a val".to_string())),
        }
    }
}

impl Exp {
    /// Compile an expression to a vector of pseudo-instructions (assembly code).
    fn compile(&self, rho: &Env) -> Result<Vec<PInstr>, CompileError> {
	use Exp::*;
        match self {
            Val(v) => Ok(self::Val::compile(v)?),
            Var(n) => {
                match rho.locals.get(n) {
                    Some(j) => Ok(vec![PI(Instr::Var(*j))]),
                    None => {return Err(CompileError("Compiler Error Var could not find in hashmap".to_string()));},
                }
            }
            Unary(u, e) => Ok(vec![e.compile(rho)?, vec![PI(Instr::Unary(*u))]].into_iter().flatten().collect::<Vec<PInstr>>()),
            Binary(b, v1, v2) => Ok(vec![v2.compile(rho)?, v1.compile(rho)?, vec![PI(Instr::Binary(*b))]].into_iter().flatten().collect::<Vec<PInstr>>()),
            Let(n, e1, e2) => {
                let instr_one = e1.compile(rho)?;
                let instr_two = e2.compile(rho)?;
                match rho.locals.get(n) {
                    Some(j) => Ok(vec![instr_one, vec![PI(Instr::Store(*j))], instr_two].into_iter().flatten().collect::<Vec<PInstr>>()),
                    None => {return Err(CompileError("Compiler Error let could not find in hashmap".to_string()));},
                }
            },
            Seq(e1, e2) => Ok(vec![e1.compile(rho)?, vec![PI(Instr::Pop)], e2.compile(rho)?].into_iter().flatten().collect::<Vec<PInstr>>()),
            Alloc(e1, e2) => Ok(vec![e1.compile(rho)?, e2.compile(rho)?, vec![PI(Instr::Alloc)]].into_iter().flatten().collect::<Vec<PInstr>>()),
            Set(e1, e2, e3) => Ok(vec![e1.compile(rho)?, e2.compile(rho)?, e3.compile(rho)?, vec![PI(Instr::Set), PI(Instr::Push(Vunit))]].into_iter().flatten().collect::<Vec<PInstr>>()),
            Get(e1, e2) => Ok(vec![e1.compile(rho)?, e2.compile(rho)?, vec![PI(Instr::Get)]].into_iter().flatten().collect::<Vec<PInstr>>()),
            Cond(e1, e2, e3) => {
                let mut econd = e1.compile(rho)?;
                let mut instr_one = e2.compile(rho)?;
                let mut instr_two = e3.compile(rho)?;
                let lab_one = fresh_label();
                let lab_two = fresh_label();
                econd.push(PPush(lab_one.clone()));
                econd.push(PI(Instr::Branch));
                econd.append(&mut instr_two);
                econd.push(PI(Instr::Push(Vbool(true))));
                econd.push(PPush(lab_two.clone()));
                econd.push(PI(Instr::Branch));
                econd.push(PLabel(lab_one));
                econd.append(&mut instr_one);
                econd.push(PLabel(lab_two));
                Ok(econd)
            },
            Funptr(n) => {
                let mut label = "L".to_string();
                label.push_str(&n.to_string());
                Ok(vec![PPush(label)])
            },
            Call(e, v) => {
                let n = v.len() as u32;
                let mut compiled_instr: Vec<PInstr> = Vec::new();
                for i in v.into_iter() {
                    compiled_instr.append(&mut i.compile(rho)?);
                }
                compiled_instr.append(&mut e.compile(rho)?);
                compiled_instr.append(&mut vec![PI(Instr::SetFrame(n+1)), PI(Instr::Swap), PI(Instr::Call)]);
                Ok(compiled_instr) 
            },
            While(cond, body) => {
                let label_1 = fresh_label();
                let label_2 = fresh_label();
                Ok(vec![vec![PI(Instr::Push(Vunit))], vec![PLabel(label_1.clone())], cond.compile(rho)?, vec![PI(Instr::Unary(Unop::Neg))], vec![PPush(label_2.clone())], vec![PI(Instr::Branch)], body.compile(rho)?, vec![PI(Instr::Pop)], vec![PI(Instr::Push(Vbool(true)))], vec![PPush(label_1.clone())], vec![PI(Instr::Branch)], vec![PLabel(label_2.clone())]].into_iter().flatten().collect::<Vec<PInstr>>()) 
            },
            Print(e) => Ok(vec![e.compile(rho)?, vec![PI(Instr::Print)], vec![PI(Instr::Push(Vunit))]].into_iter().flatten().collect::<Vec<PInstr>>()),
            Size(e) => Ok(vec![e.compile(rho)?, vec![PI(Instr::Size)]].into_iter().flatten().collect::<Vec<PInstr>>()),
            //_ => Err(CompileError("Error: compile() for exp not a exp".to_string()))
        }
    }
}

impl Fun {
    /// Compile a function to a vector of pseudo-instructions (assembly code).
    fn compile(&self) -> Result<Vec<PInstr>, CompileError> {
        // Compile the body of the function (create a blank environment)
        let mut rho = Env::mk(HashMap::new());
        let mut instr = vec![PLabel(format!("L{}",self.name))];
        // all the variables were defining from within the function (the local variables)
        let bound_vars = self.body.bound_vars();
        // allocates the variables the stack
        for (index, element) in bound_vars.iter().enumerate() {
            instr.push(PI(Instr::Push(Vundef)));
            // insert a pair in the environment to map the current element to the offset from the frame pointer
            // The first thing that is inserted is just the element, the second is the index + the offset (the # of the parameters) and then add 2
            // The 2 represents the caller's FP and PC
            rho.locals.insert(element.clone(), (index + self.params.len() + 2) as u32);
        }
        // initialized the variables into the environment (given parameters to the function)
        for (index, element) in self.params.iter().enumerate() {
            // element.0 just gets the name
            rho.locals.insert(element.0.clone(), index as u32);
        }
        // Append the instructions from the body
        instr.append(&mut self.body.compile(&rho)?);
        // conditional statement to put vret in the correct location [delete all of the bound vars that are unneeded now]
        if bound_vars.len() > 0 {
            // Store the ret at the correct location, right after the defined vars, the fp, and pc (before the bound vars)
            instr.push(PI(Instr::Store((self.params.len() + 2) as u32)));
            // Pop off all of the bounded variables
            for _ in 1..bound_vars.len() {
                instr.push(PI(Instr::Pop));
            }

        }
        instr.push(PI(Instr::Ret));
        Ok(instr)
    }
}

impl Prog {
    /// Compile a program to a vector of pseudo-instructions (assembly code).
    pub fn compile(&self) -> Result<Vec<PInstr>, CompileError> {
	let main = Fun::new("main".into(), vec![], Type::I32, self.main.clone());
	Ok([vec![PI(Instr::SetFrame(0)),
		 PPush("Lmain".into()),
		 PI(Instr::Call),
		 PI(Instr::Halt)],
	    main.compile()?,
	    self.funs.iter().map(|f| f.compile()).collect::<Result<Vec<_>, _>>()?.concat()
	].concat())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    // Example test case.
    #[test]
    fn test_1_compile_vals() {
        assert_eq!(Val::compile(&Num(123 as i32)).unwrap(), vec![PI(Instr::Push(Vi32(123 as i32)))]);
        assert_eq!(Val::compile(&Num(-123 as i32)).unwrap(), vec![PI(Instr::Push(Vi32(-123 as i32)))]);
        assert_eq!(Val::compile(&Bool(true)).unwrap(), vec![PI(Instr::Push(Vbool(true)))]);
        assert_eq!(Val::compile(&Bool(false)).unwrap(), vec![PI(Instr::Push(Vbool(false)))]);
        assert_eq!(Val::compile(&Unit).unwrap(), vec![PI(Instr::Push(Vunit))]);
    }
    #[test]
    fn test_2_compile_exps() {
        let locals: HashMap<String, u32> = HashMap::new();
        assert_eq!(Exp::compile(&Exp::Val(Num(123 as i32)), &Env::mk(locals)).unwrap(), vec![PI(Instr::Push(Vi32(123 as i32)))]);
        let locals1: HashMap<String, u32> = HashMap::new();
        assert_eq!(Exp::compile(&Exp::Val(Num(-123 as i32)), &Env::mk(locals1)).unwrap(), vec![PI(Instr::Push(Vi32(-123 as i32)))]);
        let locals2: HashMap<String, u32> = HashMap::new();
        assert_eq!(Exp::compile(&Exp::Val(Bool(true)), &Env::mk(locals2)).unwrap(), vec![PI(Instr::Push(Vbool(true)))]);
        let locals3: HashMap<String, u32> = HashMap::new();
        assert_eq!(Exp::compile(&Exp::Val(Bool(false)), &Env::mk(locals3)).unwrap(), vec![PI(Instr::Push(Vbool(false)))]);
        let locals4: HashMap<String, u32> = HashMap::new();
        assert_eq!(Exp::compile(&Exp::Val(Unit), &Env::mk(locals4)).unwrap(), vec![PI(Instr::Push(Vunit))]);
        let locals5: HashMap<String, u32> = HashMap::new();
        assert_eq!(Exp::compile(&Exp::Binary(Binop::Mul,  Box::new(Exp::Val(Num(3))),  Box::new(Exp::Val(Num(4)))), &Env::mk(locals5)).unwrap(), vec![PI(Instr::Push(Vi32(4))), PI(Instr::Push(Vi32(3))), PI(Instr::Binary(Binop::Mul))]);
        let locals6: HashMap<String, u32> = HashMap::new();
        assert_eq!(Exp::compile(&Exp::Binary(Binop::Add,  Box::new(Exp::Val(Num(3))),  Box::new(Exp::Val(Num(4)))), &Env::mk(locals6)).unwrap(), vec![PI(Instr::Push(Vi32(4))), PI(Instr::Push(Vi32(3))), PI(Instr::Binary(Binop::Add))]);
        let locals7: HashMap<String, u32> = HashMap::new();
        assert_eq!(Exp::compile(&Exp::Binary(Binop::Sub,  Box::new(Exp::Val(Num(-3))),  Box::new(Exp::Val(Num(4)))), &Env::mk(locals7)).unwrap(), vec![PI(Instr::Push(Vi32(4))), PI(Instr::Push(Vi32(-3))), PI(Instr::Binary(Binop::Sub))]);
        let locals8: HashMap<String, u32> = HashMap::new();
        assert_eq!(Exp::compile(&Exp::Binary(Binop::Div,  Box::new(Exp::Val(Num(3))),  Box::new(Exp::Val(Num(4)))), &Env::mk(locals8)).unwrap(), vec![PI(Instr::Push(Vi32(4))), PI(Instr::Push(Vi32(3))), PI(Instr::Binary(Binop::Div))]);
        let locals9: HashMap<String, u32> = HashMap::new();
        assert_eq!(Exp::compile(&Exp::Seq(Box::new(Exp::Val(Num(3))), Box::new(Exp::Val(Num(4)))), &Env::mk(locals9)).unwrap(), vec![PI(Instr::Push(Vi32(3))), PI(Instr::Pop), PI(Instr::Push(Vi32(4)))]);
        let locals10: HashMap<String, u32> = HashMap::new();
        assert_eq!(Exp::compile(&Exp::Unary(Unop::Neg, Box::new(Exp::Val(Bool(true)))), &Env::mk(locals10)).unwrap(), vec![PI(Instr::Push(Vbool(true))), PI(Instr::Unary(Unop::Neg))]);
        let locals11: HashMap<String, u32> = HashMap::new();
        assert_eq!(Exp::compile(&Exp::Alloc(Box::new(Exp::Val(Num(100))), Box::new(Exp::Val(Bool(false)))), &Env::mk(locals11)).unwrap(), vec![PI(Instr::Push(Vi32(100))), PI(Instr::Push(Vbool(false))), PI(Instr::Alloc)]);
        let locals12: HashMap<String, u32> = HashMap::new();
        assert_eq!(Exp::compile(&Exp::Set(Box::new(Exp::Val(Num(100))), Box::new(Exp::Val(Num(5))), Box::new(Exp::Val(Bool(true)))), &Env::mk(locals12)).unwrap(), vec![PI(Instr::Push(Vi32(100))), PI(Instr::Push(Vi32(5))), PI(Instr::Push(Vbool(true))), PI(Instr::Set), PI(Instr::Push(Vunit))]);
        let locals13: HashMap<String, u32> = HashMap::new();
        assert_eq!(Exp::compile(&Exp::Get(Box::new(Exp::Val(Num(100))), Box::new(Exp::Val(Num(5)))), &Env::mk(locals13)).unwrap(), vec![PI(Instr::Push(Vi32(100))), PI(Instr::Push(Vi32(5))), PI(Instr::Get)]);
    }
}
