use std::fmt::Debug;
use core::fmt;
use crate::format_memory;


pub struct ROM {
    pub memory: [u8; 0x10000],
    pub size: u16,
}

impl ROM {
    /// Creates new rom from string of hex values separated by whitespace
    pub fn new(bytes: &[u8]) -> ROM {
        if bytes.starts_with(b"6502ROM...") {
            let bytes = &bytes[10..];
            let mut rom = ROM {
                memory: [0; 0x10000],
                size: bytes.len() as u16,
            };
            for i in 0..rom.size as usize {
                rom.memory[i] = bytes[i];
            }
            rom
        } else {
            let mut rom = ROM {
                memory: [0; 0x10000],
                size: 0,
            };
            let str: Vec<_> = std::str::from_utf8(&bytes).unwrap().split_whitespace().collect();

            for (index, byte) in str.iter().enumerate() {
                rom.memory[index] = match u8::from_str_radix(byte, 16) {
                    Ok(h) => h,
                    Err(_e) => panic!(format!(
                        "Invalid value fround in byte string at index {:04X}: {}",
                        index, byte,
                    )),
                };
            }

            rom.size = str.len() as u16;

            rom
        }
    }
}

impl Debug for ROM {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", format_memory(&self.memory[0..(self.size as usize)], 8))
    }
}
