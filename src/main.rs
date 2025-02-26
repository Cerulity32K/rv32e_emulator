//! Runs an arbitrary RISC-V program given by a stream of machine code using the [`BasicMemory`] memory type and [`ECallTerminal`] to handle `ECALL`s.

use std::{env::args, fs};

use rv32e_emulator::{BasicMemory, ECallHandler, ECallTerminal, RV32E, StepResult};

fn main() {
    let program = fs::read(args().skip(1).next().expect("no file input")).unwrap();
    let stack_size = 0x10000;
    let stack_base = program.len() as u32 + stack_size;
    let mut mem = BasicMemory::new(program);
    let mut hart = RV32E::default();
    let mut ecall_handler = ECallTerminal::new();
    hart.set_register(2, stack_base);
    loop {
        match hart.step(&mut mem) {
            Ok(result) => match result {
                StepResult::Unremarkable => {}
                StepResult::ECall => {
                    ecall_handler.handle_ecall(&mut hart);
                }
                StepResult::EBreak => {
                    return;
                }
            },
            Err((err, operation)) => panic!(
                "error executing instruction 0x{operation:08x} at 0x{:08x}: `{err}`",
                hart.pc.get()
            ),
        }
    }
}
