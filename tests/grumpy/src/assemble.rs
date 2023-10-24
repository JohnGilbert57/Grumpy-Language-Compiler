//! Grumpy assembler.
//!
//! This module contains the assembler that translates
//! pseudo-instruction (assembly) programs into native (bytecode)
//! programs by resolving label addresses.
///     README         
///     Cargo Project:  grumpy
///     File:           assemble.rs
///     Author:         Nathaniel Buchanan [nb333218@ohio.edu] & Johnny Gilbert [jg480318@ohio.edu]
///     Date:           March 26, 2022
///     Class:          CS 4100, Section 100 - Formal Languages and Compilers
///     Professors:     Dr. Chang Liu, Professor Alex Bagnall
///     Brief:          This is the Assembler from PA1. This is from Johnny's version of PA1.
///     Repo:           https://github.com/OUCompilers/pa3-gc-JohnGilbert57.git

use crate::isa::{*, Instr::*, PInstr::*, Val::*};

/// Translate an assembly program to an equivalent bytecode program.
pub fn assemble(pinstrs : &[PInstr]) -> Result<Vec<Instr>, String> {
    let mut instructions: Vec<Instr> = Vec::new();
    let mut labels = Vec::new();
    let mut counter: u32 = 0;
    // First Pass: If you run into a PLabel, make a tuple of that counter (for the location) and the string (name of the Label)
    for i in pinstrs.iter() {
        match i {
            PLabel(lab) => labels.push((counter, lab.to_string())),
            // program counter (label does not count as a counter | aka line offset)
            _ => counter += 1
        }
    }
    // Second Pass
    for i in pinstrs.iter() {
        match i {
            // If it is a PI, then you just push it 
            PI(instruct) => instructions.push(instruct.clone()),
            // If it is a Label
            PPush(label) => {
                let mut is_label_found = false;
                // x is a given label in the label vector
                for x in labels.iter() {
                    // x.1 is the name of the label (the string)
                    if x.1 == label.to_string() {
                        // x.0 is the counter of that label
                        instructions.push(Push(Vloc(x.0)));
                        is_label_found = true;
                        break;
                    }
                }
                if !is_label_found {
                    panic!("{}", "Label not found")
                }
            }
            _ => (),
        }
    }
    return Ok(instructions);
}