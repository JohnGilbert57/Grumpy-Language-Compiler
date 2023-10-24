//! Grumpy virtual machine.
//!
//! This module contains the Grumpy virtual machine.
///     README         
///     Cargo Project:  grumpy
///     File:           vm.rs
///     Authors:        Nathaniel Buchanan & Johnny Gilbert    
///     Date:           March 26, 2022
///     Class:          CS 4100, Section 100 - Formal Languages and Compilers
///     Professors:     Dr. Chang Liu, Professor Alex Bagnall
///     Brief:          This is the Virtual Machine from PA2 with the additional
///                     code (a few functions) for the garbage collection.                
///     Repo:           https://github.com/OUCompilers/pa3-gc-JohnGilbert57.git


use std::fmt::{self, Display};
use crate::VMError;
use super::isa::{*, Binop::*, Instr::*, Val::*, Unop::*};

static STK_SIZE: usize = 1024;
static HEAP_SIZE: usize = 1024;

/// GrumpyVM state.
#[derive(Debug)]
struct State {
    /// Program counter.
    pc: u32,
    /// Frame pointer.
    fp: u32,
    /// The stack, with maximum size STK_SIZE.
    stk: Vec<Val>,
    /// The heap, with maximum size HEAP_SIZE.
    heap: Vec<Val>,
    /// The program being executed, a vector of instructions.
    prog: Vec<Instr>
}

/// Display implementation for State (modify as you wish).
impl Display for State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
	write!(f, "pc: {}\ninstr: {:?}\nfp: {}\nstk: {:?}\nheap: {:?}",
	       self.pc, self.prog[self.pc as usize], self.fp, self.stk, self.heap)?;
	write!(f, "\nheap size: {}", self.heap.len())
    }
}

/// Debug enum (whether to print debug information during execution or not).
#[derive(Clone, Copy)]
pub enum Debug {
    DEBUG,
    NODEBUG
}

/// State methods.
impl State {
    /// Create initial state for given program.
    fn init(prog: Vec<Instr>) -> State {
	State {
	    pc: 0, 
	    fp: 0,
	    stk: Vec::with_capacity(STK_SIZE),
	    heap: Vec::with_capacity(HEAP_SIZE),
	    prog: prog
	}
    }

    /// Push a Val to the stack, checking for overflow.
    fn push(&mut self, v: Val) -> Result<(), VMError> {
	assert(self.stk.len() < STK_SIZE, "out of stack space")?;
	Ok(self.stk.push(v))
    }

    /// Push a Val to the heap, checking for overflow.
    fn push_heap(&mut self, v: Val) -> Result<(), VMError> {
        assert(self.heap.len() < HEAP_SIZE, "out of heap space")?;
        Ok(self.heap.push(v))
    }

    /// Pop a Val from the stack, checking for underflow.
    fn pop(&mut self) -> Result<Val, VMError> {
    	self.stk.pop().ok_or("attempt to pop empty stack".into())
    }

    // Alloc space for an array for the heap MODIFIED FROM PA2 DUE TO GARBAGE COLLECTIOn
    fn alloc(&mut self) -> Result<(), VMError> {
        // val pushed on heap
        let vinit = State::pop(self)?;
        // how many vinits are being pushed
        let val_size = State::pop(self)?;
        // size as u32 extracted from Vi32()
        let size: usize;
        match val_size {
            Vi32(u) => size = u as usize,
            _       => {return Err(VMError("Error: Alloc - Missing size".to_string())); }
        }
        //*********************************************************************************************************//
        //*****************************************PA3 Update******************************************************//
        //*********************************************************************************************************//
        // Check the allocate size of the heap to see if it is larger than the largest Heap Size
        if self.heap.len() + size >= HEAP_SIZE {
            // Match the state and check if it is okay or not
            match run_gc(self) {
                // Means that it successfully took out the trash
                Ok(_)    => {
                    // If the heap is still larger than the Max Heap size, then throw an error
                    if self.heap.len() + size >= HEAP_SIZE {
                        return Err(VMError("out of heap space".to_string()));
                    } 
                },
                // Unsuccessful in taking out the trash
                Err(e)   => {return Err(VMError(e));}
            }
        }
        //*********************************************************************************************************//
        //*************************************End of Changes******************************************************//
        //*********************************************************************************************************//
        // push Vsize onto the heap
        State::push_heap(self, Vsize(size))?;
        // push Vaddr of heap beginning array : the top of the stack is the address of the beginning size. that size
        // determines how many elements of vinit were pushed
        match State::push(self, Vaddr(self.heap.len() - 1)){
            Ok(_)  => (),
            Err(e) => {return Err(e);}
        }
        // push size elements onto heap
        for _ in 0..size {
            State::push_heap(self, vinit)?;
        }
        Ok(())
    }

    /// Set a value in an array (int the heap)
    fn set(&mut self) -> Result<(), VMError> {
        let value = State::pop(self)?;
        let idx_val = State::pop(self)?;
        let base_val =State::pop(self)?;
        let idx: usize;
        let base: usize;
        // Extract and get the index (Vi32 originally)
        match idx_val {
            Vi32(i) => idx = i as usize,
            _       => {return Err(VMError("Error Set: Could not find index".to_string()))}
        }
        // Extract and get the base value (Vaddr originally)
        match base_val {
            Vaddr(b) => base = b,
            _        => {return Err(VMError("Error Set: Could not find base".to_string()))}
        }
        let heap_val = self.heap[base];
        let heap_arr_size;
        match heap_val {
            Vsize(s) => heap_arr_size = s,
            _ => {return Err(VMError("Error Set: could not find base size in heap".to_string()));}
        }
        // Checks to see if the heap address is out of scope
        if idx > heap_arr_size {
            return Err(VMError("Error Set: Heap Address is out of range".to_string()));
        } 
        // That location on the heap is now that value (that was extracted from the beginning)
        self.heap[idx + base + 1] = value;
        Ok(())
    }

    // Everything is the same in get as set except the final line. It is a push instead of an = value
    fn get(&mut self) -> Result<(), VMError> {
        let idx_val = State::pop(self)?;
        let base_val = State::pop(self)?;
        let idx: usize;
        let base: usize;
        match idx_val {
            Vi32(i) => idx = i as usize,
            _       => {return Err(VMError("Error Get: Could not find index".to_string()))}
        }
        match base_val {
            Vaddr(b) => base = b,
            _        => {return Err(VMError("Error Get: Could not find base".to_string()))}
        }
        let heap_val = self.heap[base];
        let heap_arr_size;
        match heap_val {
            Vsize(s) => heap_arr_size = s,
            _ => {return Err(VMError("Error Get: could not find base size in heap".to_string()));}
        }
        if idx > heap_arr_size  {
            return Err(VMError("Error Get: Heap Address is out of range".to_string()));
        } 
        // Push that location on heap to the top of the stack
        State::push(self, self.heap[idx + base + 1])?;
        Ok(())
    }

    /// The var instruction
    fn var(&mut self, u: u32) -> Result<(), VMError> {
        let index: usize = (self.fp + u) as usize;
        if index > self.stk.len() - 1 {
            return Err(VMError("Error: Var index is out of range".to_string()));
        }
        State::push(self, self.stk[index])?;
        Ok(())
    }

    /// The store instruction
    fn store(&mut self, u: u32) -> Result<(), VMError> {
        let value: Val = State::pop(self)?;
        let index: usize = (self.fp + u) as usize;
        if index > self.stk.len() - 1 {
            return Err(VMError("Error: Var index is out of range".to_string()));
        }
        self.stk[index] = value;
        Ok(())
    }

    /// Set the frame pointer (in the stack) to a value
    fn set_frame(&mut self, u: u32) -> Result<(), VMError> {
        // Set the initial frame and push that value onto the stack. Based upon the frame pointer
        State::push(self, Vloc(self.fp))?;
        self.fp = self.stk.len() as u32 - (u + 1);
        Ok(())
    }

    /// Function for the NEW Print function!
    fn print(&mut self) -> Result<(), VMError> {
        let result = State::pop(self)?;
        println!("{:?}", result);
        Ok(())
    }

    /// Function for the NEW Size function
    fn size(&mut self) -> Result<(), VMError> {
        let base = State::pop(self)?;
        let mut result;
        match base {
            Vaddr(x) => result = self.heap[x],
            _        => {return Err(VMError("Error: Exec() - Size failed not a Vaddr".to_string()));}
        }
        match result {
            Vsize(v) => State::push(self, Vi32(v as i32)),
            _        => {return Err(VMError("Error: Exec() - Size failed not a Vsize".to_string()));}
        };
        Ok(())
    }

    /// Call a function
    fn call(&mut self) -> Result<(), VMError> {
        // Pop the target address (which should be a Vloc)
        let target = State::pop(self)?;
        match target {
            Vloc(u) => {
                // Push the caller_pc onto the stack; then set the program counter to the target
                State::push(self, Vloc(self.pc))?;
                self.pc = u;
            },
            _       => {return Err(VMError("Error: Exec() - Call failed not a Vloc for Call".to_string()));}
        }
        Ok(())
    }

    /// Branch instruction
    fn branch(&mut self) -> Result<(), VMError> {
        // take Vloc(?)
        let target_val: Val = State::pop(self)?;
        // get branch decision
        let bool_val: Val = State::pop(self)?;
        let target;
        // extract target from Vloc
        match target_val {
            Vloc(t) => {target = t;}
            _       => {return Err(VMError("Error: Branch Target Not found".to_string()))}
        }
        // Check to see if target is out of bounds
        if self.prog.len() - 1 < target as usize {
            return Err(VMError("Error: Branch Target is out of bounds".to_string()));
        }
        // branch or don't branch decision
        match bool_val {
            Vbool(true)  => {self.pc = target;}
            Vbool(false) => (),
            _            => {return Err(VMError("Error: Branch not a valid boolean value".to_string()));}
        }
        Ok(())
    }

    /// Return to a prior label
    fn ret(&mut self) -> Result<(), VMError> {
        let vret: Val = State::pop(self)?;
        let caller_pc: Val = State::pop(self)?;
        let caller_fp: Val = State::pop(self)?;
        // The new program counter location is from the Program counter
        match caller_pc {
            Vloc(p_c) => {self.pc = p_c;}
            _ => {return Err(VMError("Error: Ret Caller PC not found".to_string()));}
        }
        // Take the frame pointer and then go through and loop through all of the extra values and pop those off
        // Then, set that frame pointer equal to the value of the frame pointer from the Vlocation (from the stack)
        match caller_fp {
            Vloc(f_p) => {
                // get rid of everything After the frame pointer
                for _ in 0..(self.stk.len() - self.fp as usize) {
                    State::pop(self)?;
                }
                self.fp = f_p;
            }
            _ => {return Err(VMError("Error: Ret Caller FP not found".to_string()));}
        }
        // Push the return value onto the stack
        State::push(self, vret)?;
        Ok(())
    }
    
}

/// May be useful for checking error conditions (in combination with
/// the '?'  operator). Note that there is a conversion trait
/// (From<&str> for VMError) defined in lib.rs so `.into()` can be
/// used to convert a string slice into a VMError.
fn assert(e: bool, msg: &str) -> Result<(), VMError> {
    if e { Ok(()) } else { Err(msg.into()) }
}

/// Evaluate a unary operation on a value.
fn unop(u: Unop, v: Val) -> Result<Val, VMError> {
    match u {
        Neg => {
            match v {
                Vbool(false) => Ok(Vbool(true)),
                Vbool(true)  => Ok(Vbool(false)),
                _ => Err(VMError("Unop Error - Not a boolean value".to_string())),
            }
        }
    }
}

/// Perform the binary operations from the binop function
fn perform_binary_operation(operation: &str, v1: Val, v2: Val) -> Result<Val, VMError> {
    match v1 {
        Vi32(x) => {
            match v2 {
                Vi32(y) => {
                    match operation {
                        "+" => Ok(Vi32(x + y)),
                        "-" => Ok(Vi32(x - y)),
                        "*" => Ok(Vi32(x * y)),
                        "/" => {
                            if y == 0 {
                                return Err(VMError("Error perform_binary_operation - Division by zero".to_string()));
                            };
                            Ok(Vi32(x / y))
                        }
                        "==" => Ok(Vbool(x == y)),
                        "<" => Ok(Vbool(x < y)),
                        _ => Err(VMError("Error perform_binary_operation - Not a valid operation".to_string())),
                    }
                }
                _ => Err(VMError("Error perform_binary_operation - v2 not Vi32".to_string())),
            } 
        }
        _ => Err(VMError("Error perform_binary_operation - v1 not Vi32".to_string())),
    }
}

/// Evaluate a binary operation on two argument values.
fn binop(b: Binop, v1: Val, v2: Val) -> Result<Val, VMError> {
    match b {
        Add => Ok(perform_binary_operation("+", v1, v2)?),
        Sub => Ok(perform_binary_operation("-", v1, v2)?),
        Mul => Ok(perform_binary_operation("*", v1, v2)?),
        Div => Ok(perform_binary_operation("/", v1, v2)?),
        Eq  => Ok(perform_binary_operation("==", v1, v2)?),
        Lt  => Ok(perform_binary_operation("<", v1, v2)?),
    }
}

// Function used to push a Val
fn push_val(v: Val) -> Result<Val, VMError>{
    match v {
        Vunit           => Ok(Vunit),
        Vi32(i)         => Ok(Vi32(i)),
        Vbool(true)     => Ok(Vbool(true)),
        Vbool(false)    => Ok(Vbool(false)),
        Vundef          => Ok(Vundef),
        Vloc(x)         => Ok(Vloc(x)),           
        _               => Err(VMError("Error: push_val - Not a valid Val".to_string())),
    }
}

/// Execute from initial state s.
fn exec(d: Debug, s: &mut State) -> Result<(), VMError> {
    // Dispatch loop.
    let mut instr;
    loop {
        // Print state if debug flag is set.
        if let Debug::DEBUG = d {
            println!("{}\n", s)
        }
            
        // Check for pc out of bounds.
        if s.prog.len() <= s.pc as usize {
            return Err(VMError("Program".to_string()));
        }
        // Get next instruction.
        instr = s.prog[s.pc as usize];

        // Increment pc.
        s.pc += 1;
        match instr {
            Push(v)         => {
                match State::push(s, push_val(v)?) {
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                    }
                },
            Pop             => {
                match State::pop(s) {
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }
            },
            Peek(v)         => {
                // Peek from the top of the stack
                match State::push(s, s.stk[s.stk.len() - v as usize]) {
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }
            },
            Unary(u)        => {
                let val = State::pop(s)?;
                match State::push(s, unop(u, val)?) {
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }
            },
            Binary(b)       => {
                let val_one = State::pop(s)?;
                let val_two = State::pop(s)?;
                match State::push(s, binop(b, val_one, val_two)?) {
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }
            },
            Swap            => {
                let val_one = State::pop(s)?;
                let val_two = State::pop(s)?;
                match State::push(s, val_one){
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }
                match State::push(s, val_two) {
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }
            },
            Alloc           => {
                match State::alloc(s) {
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }
            }
            Set             => {
                match State::set(s) {
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }},
            Get             => {
                match State::get(s) {
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }
            },
            Var(u)          => {
                match State::var(s, u) {
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }
            },
            Store(u)        => {
                match State::store(s, u) {
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }
            },
            SetFrame(u)     => {
                match State::set_frame(s, u) {
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }
            },
            Call            => {
                match State::call(s) {
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }
            },
            Ret             =>  {
                match State::ret(s) {
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }
            },
            Branch          => {
                match State::branch(s){
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }
            },
            Halt            => break,
            Print           => {
                match State::print(s) {
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }
            },
            Size           => {
                match State::size(s) {
                    Ok(_)  => (),
                    Err(e) => {return Err(e);},
                }
            },
        } // end match
    } // end loop
    Ok(())
}

/// Entry point of the module. Run a given program in the VM.
pub fn run(d: Debug, prog: &[Instr]) -> Result<Val, VMError> {
    // Create initial state.
    let mut s = State::init(prog.into());

    // Run VM.
    exec(d, &mut s)?;

    // Return the value on top of the stack.
    s.pop()
}

/// Forward an address from 'from' space to 'to' space.
fn forward(from: &mut Vec<Val>, to: &mut Vec<Val>, p: Address) -> Result<Address, VMError> {  
    // Check if the address is out of bounds or not
    if p >= from.len() {
        return Err(VMError("Error: forward - Should Never Occur. P is out of Bounds".to_string()));
    }

    // Match the address value on the original heap
    match from[p] {
        // The array is not yet forwarded and must be in order to be in the new and improved heap
        Vsize(size_of_array) => {
            // Get the new address that you want the array to be
            let new_address = to.len();
            // Push this value onto the new heap
            to.push(from[p]);
            // The new value on the original heap's address is a Vforward of the new address
            from[p] = Vforward(new_address);
            // Go through the elements from the array and push them onto the new heap
            for i in 1..=size_of_array {
                // Push the elements onto the new array
                // p - base address of the array
                // i - index of the current element
                to.push(from[p + i]);
            }
            // The address is the base of the array (in the new heap), [address is a ptr]
            Ok(new_address)
        },

        // If the array that the address is pointing to has already been forwarded,
        // then you are wanting to copy the address of the new array (replace the old ptr)
        Vforward(x)  => Ok(x),
        _            => Err(VMError("Error: forward - Not a valid instruction".to_string())),

    }
}

/// Run the garbage collector. It is a copy collector
fn run_gc(s: &mut State) -> Result<(), String> {
    // The new, copy collected, heap
    let mut new_heap = Vec::with_capacity(HEAP_SIZE);
    // The size of the original heap
    let heap_size = s.heap.len();
    // The size of the new heap
    let new_heap_size;
    // Loop that is important due to the length of the new_heap
    let mut loop_counter = 0;
    // Go through the stack and find all of the pointers (Vaddr)
    for index in 0..s.stk.len() {
        match s.stk[index] {
            // It must be a vaddress, if it isn't do nothing
            Vaddr(current_addr) => {
                // Check the result to see what Result type it was
                match forward(&mut s.heap, &mut new_heap, current_addr) {
                    Ok(new_address)  => {
                        s.stk[index] = Vaddr(new_address);
                    }
                    // Vaddr DOES need to reference an array
                    Err(e) => {return Err(e.to_string());}
                }
            },
            _        => {}
        }
    }
    // Forward all addresses in the new heap (that are still accessible) to prevent 
    // pointers to arrays in the old heap
    // Must make sure to check the length of the heap each time to make sure you
    // are forwarding all of the addresses that are necessary
    while loop_counter < new_heap.len() { 
        match new_heap[loop_counter] {
            // It must be a vaddress, if it isn't do nothing
            Vaddr(current_add) => {
                // Check the result to see what Result type it was
                match forward(&mut s.heap, &mut new_heap, current_add) {
                    Ok(new_address)  => {
                        new_heap[loop_counter] = Vaddr(new_address);
                    }
                    // Vaddr DOES need to reference an array
                    Err(e) => {return Err(e.to_string());}
                }
            },
            _        => {}
        }
        // loop increment
        loop_counter += 1;
    }
    // Set the heap to be the new heap
    s.heap = new_heap;
    // Get the size of the new heap
    new_heap_size = s.heap.len();

    // Print the Heap sizes utilizing Standard Error instead of Standard Out
    eprintln!("GC start: heap_size = {} values", heap_size);
    eprintln!("GC end: heap_size = {} values", new_heap_size);

    // End of function
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    // Example test case.
    #[test]
    fn test_1_operation() {
        assert_eq!(binop(Add, Vi32(5), Vi32(4)).unwrap(), Vi32(9));
        assert_eq!(binop(Sub, Vi32(15), Vi32(10)).unwrap(), Vi32(5));
        assert_eq!(binop(Mul, Vi32(12), Vi32(5)).unwrap(), Vi32(60));
        assert_eq!(binop(Div, Vi32(10), Vi32(2)).unwrap(), Vi32(5));
        assert_eq!(binop(Div, Vi32(5), Vi32(2)).unwrap(), Vi32(2));
        assert_eq!(binop(Div, Vi32(8), Vi32(3)).unwrap(), Vi32(2));
        assert_eq!(binop(Lt, Vi32(10), Vi32(2)).unwrap(), Vbool(false));
        assert_eq!(binop(Lt, Vi32(4), Vi32(5)).unwrap(), Vbool(true));
        assert_eq!(binop(Lt, Vi32(2), Vi32(2)).unwrap(), Vbool(false));
        assert_eq!(binop(Lt, Vi32(-3), Vi32(2)).unwrap(), Vbool(true));
        assert_eq!(binop(Eq, Vi32(-1), Vi32(1)).unwrap(), Vbool(false));
        assert_eq!(binop(Eq, Vi32(1), Vi32(1)).unwrap(), Vbool(true));
        assert_eq!(unop(Neg, Vbool(false)).unwrap(), Vbool(true));
        assert_eq!(unop(Neg, Vbool(true)).unwrap(), Vbool(false));
        
    }
    #[test]
    fn test_2_operation_failure() {
        assert!(matches!(unop(Neg, Vi32(10)), Err(VMError(_))));
        assert!(matches!(binop(Div, Vi32(5), Vi32(0)), Err(VMError(_))));
        assert!(matches!(binop(Div, Vi32(5), Vbool(true)), Err(VMError(_))));
        assert!(matches!(binop(Div, Vundef, Vi32(3)), Err(VMError(_))));
        assert!(matches!(binop(Div, Vi32(5), Vbool(true)), Err(VMError(_))));
        assert!(matches!(binop(Add, Vundef, Vi32(4)), Err(VMError(_))));
        assert!(matches!(binop(Sub, Vi32(3), Vundef), Err(VMError(_))));
        assert!(matches!(unop(Neg, Vundef), Err(VMError(_))));
    }
    /****************************************************
     * 
     * Lines 635-651: 3 Unit tests for
     * 
     */
    // allocate empty heap with > 1024 indices
    #[test]
    fn test_3_allocate_empty_array() {
        let instrs = vec![SetFrame(0), Push(Vloc(4)), Call, Halt, Push(Vi32(1024)), Push(Vi32(1)), Alloc, Pop, Push(Vi32(2)), Ret];
        assert!(matches!(run(Debug::NODEBUG, &instrs), Err(VMError(_))));
    }
    // infinite recursion
    #[test]
    fn test_4_infinite_recursion() {
        let instrs = vec![SetFrame(0), Push(Vloc(4)), Call, Halt, Push(Vi32(10)), Push(Vi32(1)), Alloc, Push(Vloc(4)), Call, Push(Vi32(2)), Ret];
        assert!(matches!(run(Debug::NODEBUG, &instrs), Err(VMError(_))));
    }
    // recycle all objects
    #[test]
    fn test_5_recycle_all_objects() {
        let instrs = vec![SetFrame(0), Push(Vloc(7)), Call, Push(Vi32(10)), Push(Vi32(10)), Alloc, Halt, Push(Vi32(1023)), Push(Vi32(1)), Alloc, Pop, Push(Vi32(2)), Ret];
        assert_eq!(run(Debug::NODEBUG, &instrs).unwrap(), Vaddr(0));
    }
    
}