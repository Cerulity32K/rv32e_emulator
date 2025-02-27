use std::collections::HashMap;

// TODO: add capabilities for memory protection/bounds
/// Allows reading and writing to/from memory.
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
