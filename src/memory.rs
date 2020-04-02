use core::fmt;
use std::fmt::Debug;
use crate::rom::ROM;
use crate::format_memory;

pub trait Memory {
    fn get_address(&self, address: u16) -> u8;
    fn set_address(&mut self, address: u16, byte: u8) -> bool;
}

/// Full memory space from 0 to 0xffff, no memory map, not accurate to any machine
pub struct FullMemory {
    pub memory: [u8; 0x10000],
    pub size: u16,
}

impl Memory for FullMemory {
    fn get_address(&self, address: u16) -> u8 {
        self.memory[address as usize]
    }

    fn set_address(&mut self, address: u16, byte: u8) -> bool {
        self.memory[address as usize] = byte;
        if address > self.size {
            self.size = address;
        }
        true
    }
}

impl Debug for FullMemory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = format_memory(&self.memory[0..(self.size as usize)], 24);
        write!(f, "{}", s)
    }
}


impl FullMemory {
    pub fn new() -> FullMemory {
        FullMemory {
            memory: [0; 0x10000],
            size: 0x0080,
        }
    }

    pub fn load_into_mem(&mut self, rom: &ROM, pc: u16) {
        let mut pc = pc;
        for rom_address in 0..rom.size {
            self.memory[pc as usize] = rom.memory[rom_address as usize];
            pc += 1;
        }
    }
}
