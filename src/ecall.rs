use std::io::{stdout, Write};

use getch::Getch;

use crate::RV32E;

/// Allows the handling of `ECALL` instructions.
///
/// The [`ECallTerminal`] handler implements `putchar` and `getchar`-like functions.
pub trait ECallHandler {
    /// Handles an `ECALL`.
    ///
    /// Returns whether or not the configuration at the time of the `ECALL` maps to this handler,
    /// which can allow the compositing of multiple handlers.
    fn handle_ecall(&mut self, hart: &mut RV32E) -> bool;
}
/// An `ECALL` handler for terminal I/O.
///
/// The call type goes in `a5`, the following values for `a5` are mapped as such:
/// 0 (`putchar`): Writes the byte in `a0` to stdout.
/// 1 (`getchar`): Reads a byte from stdin to `a0`.
pub struct ECallTerminal(Getch);
impl ECallTerminal {
    pub fn new() -> Self {
        Self(Getch::new())
    }
}
impl ECallHandler for ECallTerminal {
    fn handle_ecall(&mut self, hart: &mut RV32E) -> bool {
        let code = hart.get_register(15);
        match code {
            0 => {
                stdout().write(&[hart.get_register(10) as u8]).unwrap();
                stdout().flush().unwrap();
            }
            1 => {
                hart.set_register(10, self.0.getch().unwrap() as u32);
            }
            _ => return false,
        }
        true
    }
}
