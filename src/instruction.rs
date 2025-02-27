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
