//! Provides functionality for executing RISC-V (`rv32e` variant) machine code.

#![feature(unbounded_shifts)]

mod bits;
mod instruction;

pub mod ecall;
pub mod exec;
pub mod mem;

use std::fmt::Debug;
use exec::{ExecutionError, StepResult};
use mem::Memory;

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
                let decoded = instruction::IType::from(operation);
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
                let decoded = instruction::IType::from(operation);

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
                let decoded = instruction::UJType::from(operation);

                self.set_register(decoded.destination(), decoded.immediate().wrapping_add(self.pc.get()));
            },
            0b00110 /* OP-IMM-32 */ => unimpl?,
            0b01000 /* STORE */ => {
                let decoded = instruction::SBType::from(operation);
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
                let decoded = instruction::RType::from(operation);

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
                let decoded = instruction::UJType::from(operation);

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
                let decoded = instruction::SBType::from_b_type(operation);
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
                let decoded = instruction::IType::from(operation);
                self.set_register(decoded.destination(), self.pc.get().wrapping_add(4));
                let rs1 = decoded.source();
                let target = ((self.get_register(rs1) + decoded.sign_extended_immediate()) >> 1) << 1;
                self.pc.set(target);
                increment_pc = false;
            },
            0b11011 /* JAL */ => {
                let decoded = instruction::UJType::from_j_type(operation);
                self.set_register(decoded.destination(), self.pc.get().wrapping_add(4));
                self.pc.set_signed(self.pc.get_signed().wrapping_add(decoded.j_offset()));
                increment_pc = false;
            },
            0b11100 /* SYSTEM */ => {
                let decoded = instruction::IType::from(operation);
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
