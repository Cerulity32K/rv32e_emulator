//! An emulation of an example RISC-V program, which takes a line of text as input and outputs that line of text reversed.
//!
//! The source code for the RISC-V program is held in `reverse.c` in the same folder as this example's source.

use rv32e_emulator::{BasicMemory, ECallHandler, ECallTerminal, RV32E, StepResult};

pub const PROGRAM: &'static [u8] = include_bytes!("reverse.bin");

fn main() -> Result<(), String> {
    let mut hart = RV32E::default();
    let mut ecall_handler = ECallTerminal::new();
    let mut memory = BasicMemory::new(PROGRAM.to_vec());
    loop {
        match hart.step(&mut memory) {
            Ok(step_result) => match step_result {
                StepResult::Unremarkable => {}
                StepResult::ECall => {
                    ecall_handler.handle_ecall(&mut hart);
                }
                StepResult::EBreak => {
                    break;
                }
            },
            Err((error, instruction)) => {
                return Err(format!(
                    "error executing instruction 0x{instruction:08x} at 0x{:08x}: `{error}`",
                    hart.pc.get()
                ));
            }
        }
    }
    Ok(())
}
