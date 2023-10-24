#![warn(clippy::all)]

use std::env;
use std::io::{self};
use std::path::Path;

use grumpy::assemble::*;
use grumpy::isa::*;
use grumpy::vm::*;

use grumpy::ir::Prog;

fn main() -> io::Result<()> {
    // Read input file (command line argument at index 1).
    let path_str = env::args().nth(1).expect("missing file argument");
    let s = std::fs::read_to_string(Path::new(&path_str))?;

    // Parse program from the string.
    let prog: Prog = s.parse()?;
 //   println!("{:?}", prog);
    // Compile program to assembly (pseudo-instructions).
    let pinstrs = prog.compile()?;
    let assembled_instr = assemble(&pinstrs).unwrap();
    let result = run(Debug::NODEBUG, &assembled_instr).unwrap();

    print!("{:?}", result);
    // Print compiled program.
    // for pinstr in pinstrs {
    //     println!("{}", pinstr.to_string())
    // }

    
    Ok(())
}
