//! Provides functionality for executing RISC-V (`rv32e` variant) machine code.

#![feature(unbounded_shifts)]

use std::{
    collections::HashMap,
    fmt::Debug,
    io::{Write, stdout},
};

use getch::Getch;
use thiserror::Error;

pub trait Memory {
    /// Stores a [`u8`] into memory at the given address.
    fn store_u8(&mut self, index: u32, value: u8);
    /// Stores a [`u16`] into memory at the given address.
    ///
    /// The default implementation calls upon [`Memory::store_u8`] twice.
    fn store_u16(&mut self, index: u32, value: u16) {
        self.store_u8(index, (value & 0xff) as u8);
        self.store_u8(index.wrapping_add(1), ((value >> 8) & 0xff) as u8);
    }
    /// Stores a [`u32`] into memory at the given address.
    ///
    /// The default implementation calls upon [`Memory::store_u8`] four times.
    fn store_u32(&mut self, index: u32, value: u32) {
        self.store_u8(index, (value & 0xff) as u8);
        self.store_u8(index.wrapping_add(1), ((value >> 8) & 0xff) as u8);
        self.store_u8(index.wrapping_add(2), ((value >> 16) & 0xff) as u8);
        self.store_u8(index.wrapping_add(3), ((value >> 24) & 0xff) as u8);
    }

    /// Loads a [`u8`] from memory at the given address.
    fn load_u8(&self, index: u32) -> u8;
    /// Loads a [`u16`] from memory at the given address.
    ///
    /// The default implementation calls upon [`Memory::load_u8`] twice.
    fn load_u16(&self, index: u32) -> u16 {
        (self.load_u8(index) as u16) | ((self.load_u8(index.wrapping_add(1)) as u16) << 8)
    }
    /// Loads a [`u32`] from memory at the given address.
    ///
    /// The default implementation calls upon [`Memory::load_u8`] four times.
    fn load_u32(&self, index: u32) -> u32 {
        (self.load_u8(index) as u32)
            | ((self.load_u8(index.wrapping_add(1)) as u32) << 8)
            | ((self.load_u8(index.wrapping_add(2)) as u32) << 16)
            | ((self.load_u8(index.wrapping_add(3)) as u32) << 24)
    }
}

/// A general-purpose register.
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Register {
    pub value: u32,
}
impl Register {
    /// Adds the given amount to this register. Useful for things like the program counter.
    pub fn add(&mut self, count: u32) {
        self.value = self.value.wrapping_add(count);
    }
    pub fn get(&self) -> u32 {
        self.value
    }
    pub fn get_signed(&self) -> i32 {
        self.get() as i32
    }
    pub fn set(&mut self, new_value: u32) {
        self.value = new_value;
    }
    pub fn set_signed(&mut self, new_value: i32) {
        self.set(new_value as u32);
    }
}
impl Debug for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{0x{:08x}}}", self.value)
    }
}

/// A RISC-V `rv32e` variant processor.
///
/// All registers are zero-initialised by default.
///
/// ### Execution
/// Execution is done through the [`RV32E::step`] function.
/// When executing, 32-bit instructions are fetched from memory at the program counter.
///
/// Execution requires a [`Memory`] object. [`BasicMemory`] is provided and allows you to load programs.
///
/// [`RV32E::step`] will return a [`StepResult`] or [`ExecutionError`].
/// [`StepResult`]s should be matched against to see if an `ECALL` or `EBREAK` instruction was executed.
/// The [`ECallHandler`] trait allows .
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RV32E {
    registers: [Register; 15], // we only use 15 registers here; x0 is always zero
    pub pc: Register,
}
impl RV32E {
    /// Gets a register's value.
    ///
    /// This should be used instead of indexing directly into `registers`, as
    /// this function will properly manage `x0`.
    pub fn get_register(&self, index: u8) -> u32 {
        let index = (index & 0xf) as usize;
        if index == 0 {
            0
        } else {
            self.registers[index - 1].get()
        }
    }
    /// Sets a register's value.
    ///
    /// This should be used instead of indexing directly into `registers`, as
    /// this function will properly manage `x0`.
    pub fn set_register(&mut self, index: u8, value: u32) {
        let index = (index & 0xf) as usize;
        if index != 0 {
            self.registers[index - 1].set(value);
        }
    }

    /// Gets the signed value of a register.
    ///
    /// This should be used instead of indexing directly into `registers`, as
    /// this function will properly manage `x0`.
    pub fn get_register_signed(&self, index: u8) -> i32 {
        let index = (index & 0xf) as usize;
        if index == 0 {
            0
        } else {
            self.registers[index - 1].get_signed()
        }
    }
    /// Sets a register to a signed value.
    ///
    /// This should be used instead of indexing directly into `registers`, as
    /// this function will properly manage `x0`.
    pub fn set_register_signed(&mut self, index: u8, value: i32) {
        let index = (index & 0xf) as usize;
        if index != 0 {
            self.registers[index - 1].set_signed(value);
        }
    }

    /// Ensures that a given instruction is valid before execution.
    pub fn check_operation(&self, operation: u32) -> Result<(), (ExecutionError, u32)> {
        if !(operation & 0b11 == 0b11 && operation & 0b11100 != 0b11100) {
            return Err((ExecutionError::UnsupportedLength, operation));
        }
        Ok(())
    }
    /// Executes the next instruction.
    pub fn step(&mut self, memory: &mut dyn Memory) -> Result<StepResult, (ExecutionError, u32)> {
        let operation = memory.load_u32(self.pc.get());
        self.check_operation(operation)?;
        let mut increment_pc = true;
        let opcode = bits::extract(operation >> 2, 0, 5);
        // shortcut for unimplemented instructions
        let unimpl = Err((ExecutionError::Unimplemented, operation));
        match opcode {
            0b00000 /* LOAD */ => {
                let decoded = inst::IType::from(operation);
                let destination = decoded.destination();
                let target_address = self.get_register(decoded.source()) + decoded.sign_extended_immediate();
                match decoded.operation() {
                    0b000 /* LB */ => self.set_register(destination, memory.load_u8(target_address) as i8 as i32 as u32),
                    0b001 /* LH */ => self.set_register(destination, memory.load_u16(target_address) as i16 as i32 as u32),
                    0b010 /* LW */ => self.set_register(destination, memory.load_u32(target_address)),
                    0b011 /* illegal */ => return Err((ExecutionError::IllegalInstruction, operation)),
                    0b100 /* LBU */ => self.set_register(destination, memory.load_u8(target_address) as u32),
                    0b101 /* LHU */ => self.set_register(destination, memory.load_u16(target_address) as u32),
                    0b110 /* illegal */ => return Err((ExecutionError::IllegalInstruction, operation)),
                    0b111 /* illegal */ => return Err((ExecutionError::IllegalInstruction, operation)),
                    _ => unreachable!()
                }
            },
            0b00001 /* LOAD-FP */ => unimpl?,
            0b00011 /* MISC-MEM */ => unimpl?,
            0b00100 /* OP-IMM */ => {
                let decoded = inst::IType::from(operation);

                let rhs = decoded.sign_extended_immediate();
                let lhs = self.get_register(decoded.source());
                let destination = decoded.destination();

                match decoded.operation() {
                    0b000 /* ADDI */ => {
                        self.set_register(destination, lhs.wrapping_add(rhs));
                    },
                    0b001 /* SLLI */ => {
                        self.set_register(destination, lhs.unbounded_shl(rhs));
                    },
                    0b010 /* SLTI */ => {
                        self.set_register(destination, ((lhs as i32) < (rhs as i32)) as u32);
                    },
                    0b011 /* SLTIU */ => {
                        self.set_register(destination, (lhs < rhs) as u32);
                    },
                    0b100 /* XORI */ => {
                        self.set_register(destination, lhs ^ rhs);
                    },
                    0b101 /* SRLI/SRAI */ => {
                        if bits::is_set(operation, 30) {
                            self.set_register_signed(destination, (lhs as i32).unbounded_shr(rhs as u32));
                        } else {
                            self.set_register(destination, lhs.unbounded_shr(rhs));
                        }
                    },
                    0b110 /* ORI */ => {
                        self.set_register(destination, lhs | rhs);
                    },
                    0b111 /* ANDI */ => {
                        self.set_register(destination, lhs & rhs);
                    },
                    _ => unreachable!(),
                }
            },
            0b00101 /* AUIPC */ => {
                let decoded = inst::UJType::from(operation);

                self.set_register(decoded.destination(), decoded.immediate().wrapping_add(self.pc.get()));
            },
            0b00110 /* OP-IMM-32 */ => unimpl?,
            0b01000 /* STORE */ => {
                let decoded = inst::SBType::from(operation);
                let target_address = self.get_register(decoded.source_1()).wrapping_add(decoded.sign_extended_immediate());
                let src = self.get_register(decoded.source_2());
                match decoded.operation() {
                    0b000 /* SB */ => memory.store_u8(target_address, src as u8),
                    0b001 /* SH */ => memory.store_u16(target_address, src as u16),
                    0b010 /* SW */ => memory.store_u32(target_address, src as u32),
                    0b011 | 0b100 | 0b101 | 0b110 | 0b111 /* illegal */ => return Err((ExecutionError::IllegalInstruction, operation)),
                    _ => unreachable!()
                }
            },
            0b01001 /* STORE-FP */ => unimpl?,
            0b01011 /* AMO */ => unimpl?,
            0b01100 /* OP */ => {
                let decoded = inst::RType::from(operation);

                let lhs = self.get_register(decoded.source_1());
                let rhs = self.get_register(decoded.source_2());
                let destination = decoded.destination();

                match decoded.operation() {
                    0b000 /* ADD/SUB */ => {
                        self.set_register(destination, if decoded.funct7_flag_set() {
                            lhs.wrapping_sub(rhs)
                        } else {
                            lhs.wrapping_add(rhs)
                        });
                    },
                    0b001 /* SLL */ => {
                        self.set_register(destination, lhs.unbounded_shl(rhs));
                    },
                    0b010 /* SLT */ => {
                        self.set_register(destination, ((lhs as i32) < (rhs as i32)) as u32);
                    },
                    0b011 /* SLTU */ => {
                        self.set_register(destination, (lhs < rhs) as u32);
                    },
                    0b100 /* XOR */ => {
                        self.set_register(destination, lhs ^ rhs);
                    },
                    0b101 /* SRL/SRA */ => {
                        self.set_register(destination, if decoded.funct7_flag_set() {
                            (lhs as i32).unbounded_shr(rhs) as u32
                        } else {
                            lhs.unbounded_shr(rhs)
                        });
                    },
                    0b110 /* OR */ => {
                        self.set_register(destination, lhs | rhs);
                    },
                    0b111 /* AND */ => {
                        self.set_register(destination, lhs & rhs);
                    },
                    _ => unreachable!(),
                }
            },
            0b01101 /* LUI */ => {
                let decoded = inst::UJType::from(operation);

                self.set_register(decoded.destination(), decoded.immediate());
            },
            0b01110 /* OP-32 */ => unimpl?,
            0b10000 /* MADD */ => unimpl?,
            0b10001 /* MSUB */ => unimpl?,
            0b10010 /* NMSUB */ => unimpl?,
            0b10011 /* NMADD */ => unimpl?,
            0b10100 /* OP-FP */ => unimpl?,
            0b10101 /* OP-V */ => unimpl?,
            0b11000 /* BRANCH */ => {
                let decoded = inst::SBType::from_b_type(operation);
                let lhs = self.get_register(decoded.source_1());
                let rhs = self.get_register(decoded.source_2());
                let branch;
                match decoded.operation() {
                    0b000 /* BEQ */ => {
                        branch = lhs == rhs;
                    },
                    0b001 /* BNE */ => {
                        branch = lhs != rhs;
                    },
                    0b010 /* illegal */ => return Err((ExecutionError::IllegalInstruction, operation)),
                    0b011 /* illegal */ => return Err((ExecutionError::IllegalInstruction, operation)),
                    0b100 /* BLT */ => {
                        branch = (lhs as i32) < (rhs as i32);
                    },
                    0b101 /* BGE */ => {
                        branch = (lhs as i32) >= (rhs as i32);
                    },
                    0b110 /* BLTU */ => {
                        branch = lhs < rhs;
                    },
                    0b111 /* BGEU */ => {
                        branch = lhs >= rhs;
                    },
                    _ => unreachable!(),
                }
                if branch {
                    let offset = decoded.b_offset();
                    self.pc.set((self.pc.get() as i32).wrapping_add(offset) as u32);
                    increment_pc = false;
                }
            },
            0b11001 /* JALR */ => {
                let decoded = inst::IType::from(operation);
                self.set_register(decoded.destination(), self.pc.get().wrapping_add(4));
                let rs1 = decoded.source();
                let target = ((self.get_register(rs1) + decoded.sign_extended_immediate()) >> 1) << 1;
                self.pc.set(target);
                increment_pc = false;
            },
            0b11011 /* JAL */ => {
                let decoded = inst::UJType::from_j_type(operation);
                self.set_register(decoded.destination(), self.pc.get().wrapping_add(4));
                self.pc.set_signed(self.pc.get_signed().wrapping_add(decoded.j_offset()));
                increment_pc = false;
            },
            0b11100 /* SYSTEM */ => {
                let decoded = inst::IType::from(operation);
                match decoded.immediate() {
                    0 /* ECALL */ => {self.pc.add(4); return Ok(StepResult::ECall)},
                    1 /* EBREAK */ => {self.pc.add(4); return Ok(StepResult::EBreak)},
                    _ => return Err((ExecutionError::IllegalInstruction, operation))
                }
            },
            0b11101 /* OP-VE */ => unimpl?,

            0b11010 /* reserved */ => unimpl?,

            0b00010 /* custom-0 */ => unimpl?,
            0b01010 /* custom-1 */ => unimpl?,
            0b10110 /* custom-2/rv128 */ => unimpl?,
            0b11110 /* custom-3/rv128 */ => unimpl?,

            0b00111 /* 48b */ => unimpl?,
            0b01111 /* 64b */ => unimpl?,
            0b10111 /* 48b */ => unimpl?,
            0b11111 /* >=80b */ => unimpl?,

            0b100000.. => unreachable!(),
        }
        if increment_pc {
            self.pc.add(4);
        }
        Ok(StepResult::Unremarkable)
    }
}
/// Represents the result of a successful execution.
pub enum StepResult {
    Unremarkable,
    ECall,
    EBreak,
}
/// Represents an error during execution.
#[derive(Clone, Copy, Debug, Error, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExecutionError {
    #[error("encountered illegal instruction")]
    IllegalInstruction,
    #[error("encountered instruction with an unsupported length")]
    UnsupportedLength,
    #[error("encountered unimplemented instruction")]
    Unimplemented,
}

/// Used internally for formatting binary numbers.
#[allow(unused)]
fn binfmt(bin: u32) -> String {
    format!(
        "{:08b}_{:08b}_{:08b}_{:08b}",
        (bin >> 24) & 0xff,
        (bin >> 16) & 0xff,
        (bin >> 8) & 0xff,
        bin & 0xff
    )
}

/// Used internally for advanced bit manipulation.
mod bits {
    use std::ops::{BitAnd, Not, Shl, Shr};

    use num_traits::{One, Zero};

    /// Sign-extends a `srcbits`-bit number into a [`u32`].
    pub fn sign_extend(base: u32, srcbits: u32) -> u32 {
        if srcbits == 0 {
            return 0;
        }
        let value_bits = srcbits - 1;
        let value = base & !(!0u32 << value_bits);
        let sign = if is_set(base, value_bits) {
            !0u32 << value_bits
        } else {
            0
        };
        let out = sign | value;
        out
    }

    /// Isolates bits `lsb` to `lsb + count` from `value` and moves them to bits 0-`count`.
    ///
    /// Useful for extracting from bitfields.
    pub fn extract<
        T: Zero + Not<Output = T> + Shr<Output = T> + Shl<Output = T> + BitAnd<Output = T>,
    >(
        value: T,
        lsb: T,
        count: T,
    ) -> T {
        (value >> lsb) & !(!T::zero() << count)
    }

    /// Checks if a single bit is set.
    pub fn is_set<T: Zero + One + BitAnd<Output = T> + Shl<Output = T> + PartialEq>(
        value: T,
        bit: T,
    ) -> bool {
        (value & (T::one() << bit)) != T::zero()
    }
}
/// Used internally for decoding instructions.
mod inst {
    use crate::bits;

    /// An R-type instruction.
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct RType {
        rd: u8,
        funct3: u8,
        rs1: u8,
        rs2: u8,
        funct7: u8,
    }
    impl RType {
        pub fn funct7_flag_set(&self) -> bool {
            bits::is_set(self.funct7, 5)
        }
        pub fn operation(&self) -> u8 {
            self.funct3
        }
        pub fn source_1(&self) -> u8 {
            self.rs1
        }
        pub fn source_2(&self) -> u8 {
            self.rs2
        }
        pub fn destination(&self) -> u8 {
            self.rd
        }
    }
    impl From<u32> for RType {
        fn from(value: u32) -> Self {
            Self {
                rd: bits::extract(value, 7, 5) as u8,
                funct3: bits::extract(value, 12, 3) as u8,
                rs1: bits::extract(value, 15, 5) as u8,
                rs2: bits::extract(value, 20, 5) as u8,
                funct7: bits::extract(value, 25, 7) as u8,
            }
        }
    }
    /// An I-type instruction.
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct IType {
        rd: u8,
        funct3: u8,
        rs1: u8,
        imm_11_0: u16,
    }
    impl IType {
        pub fn source(&self) -> u8 {
            self.rs1
        }
        pub fn destination(&self) -> u8 {
            self.rd
        }
        pub fn operation(&self) -> u8 {
            self.funct3
        }
        pub fn immediate(&self) -> u16 {
            self.imm_11_0
        }
        pub fn sign_extended_immediate(&self) -> u32 {
            bits::sign_extend(self.imm_11_0 as u32, 12)
        }
    }
    impl From<u32> for IType {
        fn from(value: u32) -> Self {
            Self {
                rd: bits::extract(value, 7, 5) as u8,
                funct3: bits::extract(value, 12, 3) as u8,
                rs1: bits::extract(value, 15, 5) as u8,
                imm_11_0: bits::extract(value, 20, 12) as u16,
            }
        }
    }
    /// An S or B-type instruction. The [`From`] implementation decodes an S-type.
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct SBType {
        funct3: u8,
        rs1: u8,
        rs2: u8,
        // [11:0] if S-type, non-sign-extended offset if B-type
        immediate_bits: u32,
    }
    impl SBType {
        pub fn source_1(&self) -> u8 {
            self.rs1
        }
        pub fn source_2(&self) -> u8 {
            self.rs2
        }
        pub fn from_b_type(value: u32) -> Self {
            let imm_4_1 = bits::extract(value, 8, 4) << 1;
            let imm_10_5 = bits::extract(value, 25, 6) << 5;
            let imm_11 = bits::extract(value, 7, 1) << 11;
            let imm_12 = bits::extract(value, 31, 1) << 31;
            Self {
                funct3: bits::extract(value, 12, 3) as u8,
                rs1: bits::extract(value, 15, 5) as u8,
                rs2: bits::extract(value, 20, 5) as u8,
                immediate_bits: imm_12 | imm_11 | imm_10_5 | imm_4_1,
            }
        }
        pub fn operation(&self) -> u8 {
            self.funct3
        }
        pub fn b_offset(&self) -> i32 {
            self.sign_extended_immediate() as i32
        }
        pub fn sign_extended_immediate(&self) -> u32 {
            bits::sign_extend(self.immediate_bits as u32, 12)
        }
    }
    impl From<u32> for SBType {
        fn from(value: u32) -> Self {
            Self {
                funct3: bits::extract(value, 12, 3) as u8,
                rs1: bits::extract(value, 15, 5) as u8,
                rs2: bits::extract(value, 20, 5) as u8,
                immediate_bits: bits::extract(value, 7, 5) | (bits::extract(value, 25, 7) << 5),
            }
        }
    }
    /// A U or J-type instruction. The [`From`] implementation decodes a U-type.
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct UJType {
        rd: u8,
        // represents [31:12] if U-type, sign-extended offset if J-type
        immediate_bits: u32,
    }
    impl UJType {
        pub fn destination(&self) -> u8 {
            self.rd
        }
        pub fn immediate(&self) -> u32 {
            self.immediate_bits << 12
        }
        pub fn j_offset(&self) -> i32 {
            self.immediate_bits as i32
        }
        pub fn from_j_type(value: u32) -> Self {
            let imm_19_12 = bits::extract(value, 12, 8) << 12;
            let imm_11 = bits::extract(value, 20, 1) << 11;
            let imm_10_1 = bits::extract(value, 21, 10) << 1;
            let sign_extension = if bits::is_set(value, 31) {
                0b111111111111u32 << 20
            } else {
                0
            };
            let immediate = sign_extension | imm_19_12 | imm_11 | imm_10_1;
            Self {
                rd: bits::extract(value, 7, 5) as u8,
                immediate_bits: immediate,
            }
        }
    }
    impl From<u32> for UJType {
        fn from(value: u32) -> Self {
            Self {
                rd: bits::extract(value, 7, 5) as u8,
                immediate_bits: bits::extract(value, 12, 20) as u32,
            }
        }
    }
}

/// A simple memory type that maps the address range of `[0, <program length>)` to program memory,
/// and the rest of the 32-bit address space to valid, zero-"initialised" RAM.
///
/// See the [`Memory`] trait.
pub struct BasicMemory {
    program: Vec<u8>,
    ram: HashMap<u32, u8>,
}
impl BasicMemory {
    pub fn new(program: Vec<u8>) -> Self {
        Self {
            program,
            ram: HashMap::new(),
        }
    }
}
impl Memory for BasicMemory {
    fn load_u8(&self, index: u32) -> u8 {
        self.program
            .get(index as usize)
            .or_else(|| self.ram.get(&index))
            .copied()
            .unwrap_or(0)
    }
    fn store_u8(&mut self, index: u32, value: u8) {
        if let Some(byte) = self
            .program
            .get_mut(index as usize)
            .or_else(|| self.ram.get_mut(&index))
        {
            *byte = value;
        } else {
            self.ram.insert(index, value);
        }
    }
}

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
