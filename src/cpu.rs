use crate::memory;
use crate::memory::Memory;
use core::fmt;
use std::fmt::{Debug, Formatter};
use std::string::ToString;

pub struct CPU<T: Memory> {
    pub reg: Registers,
    pub mem: T,
    current_op: Op,
    current_opcode: u8,
    current_address: String,
    cycles_left_for_op: usize,
}

/// 6502 standard registers
pub struct Registers {
    /// Accumulator
    pub a: u8,
    /// X index
    pub x: u8,
    /// Y index
    pub y: u8,
    /// Stack Pointer
    pub s: u8,
    /// Program Counter
    pub pc: u16,
    /// Processor flags
    pub p: u8,
}

/// Flags
enum Fl {
    /// Carry
    C,
    /// Zero
    Z,
    /// Interrupt Enable/Disable
    I,
    /// Decimal mode (Currently unimplemented)
    D,
    /// Software interrupt
    B,
    /// Overflow
    V,
    /// Sign
    S,
}

/// Opcodes
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum Op {
    /// Add memory to accumulator with carry
    ADC,
    /// "AND" memory with accumulator
    AND,
    /// Shift Left One Bit (Memory or Accumulator)
    ASL,
    /// Branch on Carry Clear
    BCC,
    /// Branch on Carry Set
    BCS,
    /// Branch on result zero
    BEQ,
    /// Test Bits in Memory with Accumulator
    BIT,
    /// Branch on Result Minus
    BMI,
    /// Branch on Result not Zero
    BNE,
    /// Branch on Result Plus
    BPL,
    /// Force Break
    BRK,
    /// Branch on Overflow Clear
    BVC,
    /// Branch on Overflow Set
    BVS,
    /// Clear Carry Flag
    CLC,
    /// Clear Decimal Mode
    CLD,
    /// Clear interrupt Disable Bit
    CLI,
    /// Clear Overflow Flag
    CLV,
    /// Compare Memory and Accumulator
    CMP,
    /// Compare Memory and Index X
    CPX,
    /// Compare Memory and Index Y
    CPY,
    /// Decrement Memory by One
    DEC,
    /// Decrement Index X by One
    DEX,
    /// Decrement Index Y by One
    DEY,
    /// "XOR" Memory with Accumulator
    EOR,
    /// Increment Memory by One
    INC,
    /// Increment Index X by One
    INX,
    /// Increment Index Y by One
    INY,
    /// Jump to New Location
    JMP,
    /// Jump to New Location Saving Return Address
    JSR,
    /// Load Accumulator with Memory
    LDA,
    /// Load Index X with Memory
    LDX,
    /// Load Index Y with Memory
    LDY,
    /// Shift Right One Bit (Memory or Accumulator)
    LSR,
    /// No Operation
    NOP,
    /// "OR" Memory with Accumulator
    ORA,
    /// Push Accumulator on Stack
    PHA,
    /// Push Processor Status on Stack
    PHP,
    /// Pull Accumulator from Stack
    PLA,
    /// Pull Processor Status from Stack
    PLP,
    /// Rotate One Bit Left (Memory or Accumulator)
    ROL,
    /// Rotate One Bit Right (Memory or Accumulator)
    ROR,
    /// Return from Interrupt
    RTI,
    /// Return from Subroutine
    RTS,
    /// Subtract Memory from Accumulator with Borrow
    SBC,
    /// Set Carry Flag
    SEC,
    /// Set Decimal Mode
    SED,
    /// Set Interrupt Disable Status
    SEI,
    /// Store Accumulator in Memory
    STA,
    /// Store Index X in Memory
    STX,
    /// Store Index Y in Memory
    STY,
    /// Transfer Accumulator to Index X
    TAX,
    /// Transfer Accumulator to Index Y
    TAY,
    /// Transfer Stack Pointer to Index X
    TSX,
    /// Transfer Index X to Accumulator
    TXA,
    /// Transfer Index X to Stack Pointer
    TXS,
    /// Transfer Index Y to Accumulator
    TYA,
}

/// Addressing modes
enum Addr {
    Implied,
    Accumulator,
    Immediate,
    Absolute,
    AbsoluteXIndexed,
    AbsoluteYIndexed,
    Zeropage,
    ZeropageXIndexed,
    ZeropageYIndexed,
    IndirectYIndexed,
    XIndexedIndirect,
    Indirect,
    Relative,
}

/// Destination for an Operation Execution
enum Dest {
    Acc,
    Adr(u16),
    None,
}

/// Decodes `u8` value to related `Op` and `Addr` and number of cycles in `usize`
fn decode_op(op_code: u8) -> (Op, usize, Addr) {
    match op_code {
        0x00 => (Op::BRK, 7, Addr::Implied),
        0x01 => (Op::ORA, 6, Addr::XIndexedIndirect),
        0x05 => (Op::ORA, 3, Addr::Zeropage),
        0x06 => (Op::ASL, 5, Addr::Zeropage),
        0x08 => (Op::PHP, 3, Addr::Implied),
        0x09 => (Op::ORA, 2, Addr::Immediate),
        0x0A => (Op::ASL, 2, Addr::Accumulator),
        0x0D => (Op::ORA, 4, Addr::Absolute),
        0x0E => (Op::ASL, 6, Addr::Absolute),
        0x10 => (Op::BPL, 2, Addr::Relative),
        0x11 => (Op::ORA, 5, Addr::IndirectYIndexed),
        0x15 => (Op::ORA, 4, Addr::ZeropageXIndexed),
        0x16 => (Op::ASL, 6, Addr::ZeropageXIndexed),
        0x18 => (Op::CLC, 2, Addr::Implied),
        0x19 => (Op::ORA, 4, Addr::AbsoluteYIndexed),
        0x1D => (Op::ORA, 4, Addr::AbsoluteXIndexed),
        0x1E => (Op::ASL, 7, Addr::AbsoluteXIndexed),
        0x20 => (Op::JSR, 6, Addr::Absolute),
        0x21 => (Op::AND, 6, Addr::XIndexedIndirect),
        0x24 => (Op::BIT, 3, Addr::Zeropage),
        0x25 => (Op::AND, 3, Addr::Zeropage),
        0x26 => (Op::ROL, 5, Addr::Zeropage),
        0x28 => (Op::PLP, 3, Addr::Implied),
        0x29 => (Op::AND, 2, Addr::Immediate),
        0x2A => (Op::ROL, 2, Addr::Accumulator),
        0x2C => (Op::BIT, 4, Addr::Absolute),
        0x2D => (Op::AND, 4, Addr::Absolute),
        0x2E => (Op::ROL, 6, Addr::Absolute),
        0x30 => (Op::BMI, 2, Addr::Relative),
        0x31 => (Op::AND, 5, Addr::IndirectYIndexed),
        0x35 => (Op::AND, 4, Addr::ZeropageXIndexed),
        0x36 => (Op::ROL, 6, Addr::ZeropageXIndexed),
        0x38 => (Op::SEC, 2, Addr::Implied),
        0x39 => (Op::AND, 4, Addr::AbsoluteYIndexed),
        0x3D => (Op::AND, 4, Addr::AbsoluteXIndexed),
        0x3E => (Op::ROL, 7, Addr::AbsoluteXIndexed),
        0x40 => (Op::RTI, 6, Addr::Implied),
        0x41 => (Op::EOR, 6, Addr::XIndexedIndirect),
        0x45 => (Op::EOR, 3, Addr::Zeropage),
        0x46 => (Op::LSR, 5, Addr::Zeropage),
        0x48 => (Op::PHA, 3, Addr::Implied),
        0x49 => (Op::EOR, 2, Addr::Immediate),
        0x4A => (Op::LSR, 2, Addr::Accumulator),
        0x4C => (Op::JMP, 3, Addr::Absolute),
        0x4D => (Op::EOR, 4, Addr::Absolute),
        0x4E => (Op::LSR, 6, Addr::Absolute),
        0x50 => (Op::BVC, 2, Addr::Relative),
        0x51 => (Op::EOR, 5, Addr::IndirectYIndexed),
        0x55 => (Op::EOR, 4, Addr::ZeropageXIndexed),
        0x56 => (Op::LSR, 6, Addr::ZeropageXIndexed),
        0x58 => (Op::CLI, 2, Addr::Implied),
        0x59 => (Op::EOR, 4, Addr::AbsoluteYIndexed),
        0x5D => (Op::EOR, 4, Addr::AbsoluteXIndexed),
        0x5E => (Op::LSR, 7, Addr::AbsoluteXIndexed),
        0x60 => (Op::RTS, 6, Addr::Implied),
        0x61 => (Op::ADC, 6, Addr::XIndexedIndirect),
        0x65 => (Op::ADC, 3, Addr::Zeropage),
        0x66 => (Op::ROR, 5, Addr::Zeropage),
        0x68 => (Op::PLA, 4, Addr::Implied),
        0x69 => (Op::ADC, 2, Addr::Immediate),
        0x6A => (Op::ROR, 2, Addr::Accumulator),
        0x6C => (Op::JMP, 5, Addr::Indirect),
        0x6D => (Op::ADC, 4, Addr::Absolute),
        0x6E => (Op::ROR, 6, Addr::Absolute),
        0x70 => (Op::BVS, 2, Addr::Relative),
        0x71 => (Op::ADC, 5, Addr::IndirectYIndexed),
        0x75 => (Op::ADC, 4, Addr::ZeropageXIndexed),
        0x76 => (Op::ROR, 6, Addr::ZeropageXIndexed),
        0x78 => (Op::SEI, 2, Addr::Implied),
        0x79 => (Op::ADC, 4, Addr::AbsoluteYIndexed),
        0x7D => (Op::ADC, 4, Addr::AbsoluteXIndexed),
        0x7E => (Op::ROR, 7, Addr::AbsoluteXIndexed),
        0x81 => (Op::STA, 6, Addr::XIndexedIndirect),
        0x84 => (Op::STY, 3, Addr::Zeropage),
        0x85 => (Op::STA, 3, Addr::Zeropage),
        0x86 => (Op::STX, 3, Addr::Zeropage),
        0x88 => (Op::DEY, 2, Addr::Implied),
        0x8A => (Op::TXA, 2, Addr::Implied),
        0x8C => (Op::STY, 4, Addr::Absolute),
        0x8D => (Op::STA, 4, Addr::Absolute),
        0x8E => (Op::STX, 4, Addr::Absolute),
        0x90 => (Op::BCC, 2, Addr::Relative),
        0x91 => (Op::STA, 6, Addr::IndirectYIndexed),
        0x94 => (Op::STY, 4, Addr::ZeropageXIndexed),
        0x95 => (Op::STA, 4, Addr::ZeropageXIndexed),
        0x96 => (Op::STX, 4, Addr::ZeropageYIndexed),
        0x98 => (Op::TYA, 2, Addr::Implied),
        0x99 => (Op::STA, 5, Addr::AbsoluteYIndexed),
        0x9A => (Op::TXS, 2, Addr::Implied),
        0x9D => (Op::STA, 5, Addr::AbsoluteXIndexed),
        0xA0 => (Op::LDY, 2, Addr::Immediate),
        0xA1 => (Op::LDA, 6, Addr::XIndexedIndirect),
        0xA2 => (Op::LDX, 2, Addr::Immediate),
        0xA4 => (Op::LDY, 3, Addr::Zeropage),
        0xA5 => (Op::LDA, 3, Addr::Zeropage),
        0xA6 => (Op::LDX, 3, Addr::Zeropage),
        0xA8 => (Op::TAY, 2, Addr::Implied),
        0xA9 => (Op::LDA, 2, Addr::Immediate),
        0xAA => (Op::TAX, 2, Addr::Implied),
        0xAC => (Op::LDY, 4, Addr::Absolute),
        0xAD => (Op::LDA, 4, Addr::Absolute),
        0xAE => (Op::LDX, 4, Addr::Absolute),
        0xB0 => (Op::BCS, 2, Addr::Relative),
        0xB1 => (Op::LDA, 5, Addr::IndirectYIndexed),
        0xB4 => (Op::LDY, 4, Addr::ZeropageXIndexed),
        0xB5 => (Op::LDA, 4, Addr::ZeropageXIndexed),
        0xB6 => (Op::LDX, 4, Addr::ZeropageYIndexed),
        0xB8 => (Op::CLV, 2, Addr::Implied),
        0xB9 => (Op::LDA, 4, Addr::AbsoluteYIndexed),
        0xBA => (Op::TSX, 2, Addr::Implied),
        0xBC => (Op::LDY, 4, Addr::AbsoluteXIndexed),
        0xBD => (Op::LDA, 4, Addr::AbsoluteXIndexed),
        0xBE => (Op::LDX, 4, Addr::AbsoluteYIndexed),
        0xC0 => (Op::CPY, 2, Addr::Immediate),
        0xC1 => (Op::CMP, 6, Addr::XIndexedIndirect),
        0xC4 => (Op::CPY, 3, Addr::Zeropage),
        0xC5 => (Op::CMP, 3, Addr::Zeropage),
        0xC6 => (Op::DEC, 5, Addr::Zeropage),
        0xC8 => (Op::INY, 2, Addr::Implied),
        0xC9 => (Op::CMP, 2, Addr::Immediate),
        0xCA => (Op::DEX, 2, Addr::Implied),
        0xCC => (Op::CPY, 4, Addr::Absolute),
        0xCD => (Op::CMP, 4, Addr::Absolute),
        0xCE => (Op::DEC, 6, Addr::Absolute),
        0xD0 => (Op::BNE, 2, Addr::Relative),
        0xD1 => (Op::CMP, 5, Addr::IndirectYIndexed),
        0xD5 => (Op::CMP, 4, Addr::ZeropageXIndexed),
        0xD6 => (Op::DEC, 6, Addr::ZeropageXIndexed),
        0xD8 => (Op::CLD, 2, Addr::Implied),
        0xD9 => (Op::CMP, 4, Addr::AbsoluteYIndexed),
        0xDD => (Op::CMP, 4, Addr::AbsoluteXIndexed),
        0xDE => (Op::DEC, 7, Addr::AbsoluteXIndexed),
        0xE0 => (Op::CPX, 2, Addr::Immediate),
        0xE1 => (Op::SBC, 6, Addr::XIndexedIndirect),
        0xE4 => (Op::CPX, 3, Addr::Zeropage),
        0xE5 => (Op::SBC, 3, Addr::Zeropage),
        0xE6 => (Op::INC, 5, Addr::Zeropage),
        0xE8 => (Op::INX, 2, Addr::Implied),
        0xE9 => (Op::SBC, 2, Addr::Immediate),
        0xEA => (Op::NOP, 2, Addr::Implied),
        0xEC => (Op::CPX, 4, Addr::Absolute),
        0xED => (Op::SBC, 4, Addr::Absolute),
        0xEE => (Op::INC, 6, Addr::Absolute),
        0xF0 => (Op::BEQ, 2, Addr::Relative),
        0xF1 => (Op::SBC, 5, Addr::IndirectYIndexed),
        0xF5 => (Op::SBC, 4, Addr::ZeropageXIndexed),
        0xF6 => (Op::INC, 6, Addr::ZeropageXIndexed),
        0xF8 => (Op::SED, 2, Addr::Implied),
        0xF9 => (Op::SBC, 4, Addr::AbsoluteYIndexed),
        0xFD => (Op::SBC, 4, Addr::AbsoluteXIndexed),
        0xFE => (Op::INC, 7, Addr::AbsoluteXIndexed),

        _ => panic!(format!("Code 0x{:02X} is not valid", &op_code)),
    }
}

impl Registers {
    fn new() -> Registers {
        Registers {
            p: 0x34,
            a: 0x00,
            x: 0x00,
            y: 0x00,
            s: 0x00,
            pc: 0x00,
        }
    }

    /// Transforms a flag into its bit position in register `P`
    fn flag_to_bit(f: Fl) -> u8 {
        match f {
            Fl::C => 0,
            Fl::Z => 1,
            Fl::I => 2,
            Fl::D => 3,
            Fl::B => 4,
            Fl::V => 6,
            Fl::S => 7,
        }
    }

    /// Retrieves specified flag from register `P`
    fn get_flag(&self, f: Fl) -> bool {
        ((self.p >> Registers::flag_to_bit(f)) & 0x1) == 1
    }

    /// Sets flag `f` in register `P` based on bool value `v`
    fn set_flag(&mut self, f: Fl, v: bool) {
        if v {
            self.p |= 1 << Registers::flag_to_bit(f);
        } else {
            self.p &= !(1 << Registers::flag_to_bit(f));
        }
    }

    /// Sets sign flag based on `u8` value
    fn set_sign(&mut self, v: u8) {
        self.set_flag(Fl::S, ((v >> 7) & 0x1) == 1);
    }

    /// Sets zero flag based on `u8` value
    fn set_zero(&mut self, v: u8) {
        self.set_flag(Fl::Z, v == 0);
    }

    fn get_stack_pointer(&mut self) -> u16 {
        self.s as u16 + 0x0100
    }
}

impl Debug for Registers {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "a: 0x{:02X}  x: 0x{:02X}  y: 0x{:02X}  s: 0x{:02X}  pc: 0x{:04X}       SV-BDIZC\n\
            {:<08b} {:b<08b} {:b<08b} {:b<08b} {:b<016b} {:b<08b}",
            self.a,
            self.x,
            self.y,
            self.s,
            self.pc,
            self.a,
            self.x,
            self.y,
            self.s,
            self.pc,
            self.p
        )
    }
}

impl<T: Memory> CPU<T> {
    pub fn new(t: T) -> Self {
        CPU {
            reg: Registers::new(),
            mem: t,
            current_opcode: 0,
            current_op: Op::JMP,
            current_address: "#$0000".to_string(),
            cycles_left_for_op: 0,
        }
    }

    pub fn step(&mut self) {
        if self.cycles_left_for_op > 0 {
            self.cycles_left_for_op -= 1;
        } else {
            self.step_next_op()
        }
    }

    pub fn step_next_op(&mut self) {
        let op_code = self.mem.get_address(self.reg.pc);
        let (op, cycles, addr) = decode_op(op_code);

        self.cycles_left_for_op = cycles.saturating_sub(1);
        self.current_op = op;
        self.current_opcode = op_code;

        let mut s = "".to_string();

        match addr {
            Addr::Implied => {
                self.execute_op(0, Dest::None, op);
                self.reg.pc += 1;
            }
            Addr::Accumulator => {
                self.execute_op(self.reg.a, Dest::Acc, op);
                self.reg.pc += 2;
                s.push_str("A");
            }
            Addr::Immediate => {
                let address = self.mem.get_address(self.reg.pc + 1);
                self.execute_op(address, Dest::Adr(address as u16), op);
                self.reg.pc += 2;
                s.push_str(&format!("#${:02X}", address))
            }
            Addr::Absolute => {
                let address = self.mem.get_address(self.reg.pc + 1) as u16
                    + self.mem.get_address(self.reg.pc + 2) as u16 * 0x10;
                let val = self.mem.get_address(address);
                self.execute_op(val, Dest::Adr(address), op);
                if op != Op::JMP {
                    self.reg.pc += 3;
                }
                s.push_str(&format!("${:04X}", address))
            }
            Addr::AbsoluteXIndexed => {
                let arg = self.mem.get_address(self.reg.pc + 1) as u16
                    + (self.mem.get_address(self.reg.pc + 2) as u16 * 256);
                let address = arg + self.reg.x as u16;
                let val = self.mem.get_address(address);
                self.execute_op(val, Dest::Adr(address), op);
                self.reg.pc += 3;
                s.push_str(&format!("${:02X},X", address))
            }
            Addr::AbsoluteYIndexed => {
                let arg = self.mem.get_address(self.reg.pc + 1) as u16
                    + (self.mem.get_address(self.reg.pc + 2) as u16 * 256);
                let address = arg + self.reg.y as u16;
                let val = self.mem.get_address(address);
                self.execute_op(val, Dest::Adr(address), op);
                self.reg.pc += 3;
                s.push_str(&format!("${:04X},Y", address))
            }
            Addr::Zeropage => {
                let address = self.mem.get_address(self.reg.pc + 1) as u16 % 256;
                let val = self.mem.get_address(address);
                self.execute_op(val, Dest::Adr(address), op);
                self.reg.pc += 2;
                s.push_str(&format!("${:04X}", address))
            }
            Addr::ZeropageXIndexed => {
                let address =
                    (self.mem.get_address(self.reg.pc + 1) as u16 + self.reg.x as u16) % 256;
                let val = self.mem.get_address(address);
                self.execute_op(val, Dest::Adr(address), op);
                self.reg.pc += 2;
                s.push_str(&format!("${:02X},X", address))
            }
            Addr::ZeropageYIndexed => {
                let address = (self
                    .mem
                    .get_address(self.reg.pc + 1 as u16 + self.reg.y as u16)
                    as u16)
                    % 256;
                let val = self.mem.get_address(address);
                self.execute_op(val, Dest::Adr(address), op);
                self.reg.pc += 2;
                s.push_str(&format!("${:02X},Y", address))
            }
            Addr::IndirectYIndexed => {
                let arg = self.mem.get_address(self.reg.pc + 1) as u16
                    + (self.mem.get_address(self.reg.pc + 2) as u16 * 256);
                let address = self.mem.get_address(arg) as u16
                    + self.mem.get_address((arg + 1) % 256) as u16 * 256
                    + self.reg.y as u16;
                let val = self.mem.get_address(address);
                self.execute_op(val, Dest::Adr(address), op);
                self.reg.pc += 2;
                s.push_str(&format!("(${:02X}),Y", address))
            }
            Addr::XIndexedIndirect => {
                let arg = self.mem.get_address(self.reg.pc + 1) as u16
                    + (self.mem.get_address(self.reg.pc + 2) as u16 * 256);
                let address = self.mem.get_address((arg + self.reg.x as u16) % 256) as u16
                    + self.mem.get_address((arg + self.reg.x as u16 + 1) % 256) as u16 * 256;
                let val = self.mem.get_address(address);
                self.execute_op(val, Dest::None, op);
                self.reg.pc += 2;
                s.push_str(&format!("(${:02X},X)", address))
            }
            Addr::Indirect => {
                let address = self.mem.get_address(self.reg.pc + 1) as u16
                    + self.mem.get_address(self.reg.pc + 2) as u16 * 0x10;
                self.execute_op(0, Dest::Adr(address), op);
                self.reg.pc += 3;
                s.push_str(&format!("(${:04X})", address))
            }
            Addr::Relative => {
                let rel = self.mem.get_address(self.reg.pc + 1);
                self.reg.pc += 2;
                self.execute_op(rel, Dest::None, op);
                s.push_str(&format!("${:02X}", rel as i8))
            }
        }

        self.current_address = s;
    }

    fn execute_op(&mut self, src: u8, dest: Dest, op: Op) {
        let mut src = src;
        match op {
            Op::ADC => {
                let (tmp, carry1) = self.reg.a.overflowing_add(src);
                let (tmp, carry2) =
                    tmp.overflowing_add(if self.reg.get_flag(Fl::C) { 1 } else { 0 });
                if self.reg.get_flag(Fl::D) {
                    unimplemented!();
                } else {
                    self.reg.set_sign(tmp);
                    self.reg.set_flag(
                        Fl::V,
                        (((self.reg.a ^ src) & 0x80) == 0)
                            && (((self.reg.a ^ tmp as u8) & 0x80) != 0),
                    );
                    self.reg.set_flag(Fl::C, carry1 || carry2);
                }
                self.reg.a = tmp;
            }
            Op::AND => {
                src &= self.reg.a;
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                self.reg.a = src;
            }
            Op::ASL => {
                self.reg.set_flag(Fl::C, (src & 0x80) != 0);
                let (src, _overflow) = src.overflowing_shl(1);
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                match dest {
                    Dest::Acc => {
                        self.reg.a = src;
                    }
                    Dest::Adr(a) => {
                        self.mem.set_address(a, src);
                    }
                    _ => panic!("Invalid destination for ASL"),
                }
            }
            Op::BCC => {
                if !self.reg.get_flag(Fl::C) {
                    self.cycles_left_for_op +=
                        if (self.reg.pc & 0xFF00) != ((self.reg.pc + src as u16) & 0xFF00)
                        { 2 } else { 1 };
                    let (result, _carry) = self.reg.pc.overflowing_add(src as u16);
                    self.reg.pc = result;
                }
            }
            Op::BCS => {
                if self.reg.get_flag(Fl::C) {
                    self.cycles_left_for_op +=
                        if (self.reg.pc & 0xFF00) != ((self.reg.pc + src as u16) & 0xFF00)
                        { 2 } else { 1 };
                    let (result, _carry) = self.reg.pc.overflowing_add(src as u16);
                    self.reg.pc = result;
                }
            }
            Op::BEQ => {
                if self.reg.get_flag(Fl::Z) {
                    self.cycles_left_for_op +=
                        if (self.reg.pc & 0xFF00) != ((self.reg.pc + src as u16) & 0xFF00)
                        { 2 } else { 1 };
                    let (result, _carry) = self.reg.pc.overflowing_add(src as u16);
                    self.reg.pc = result;
                }
            }
            Op::BIT => {
                self.reg.set_sign(src);
                self.reg.set_flag(Fl::Z, (0x40 & src) != 0);
                self.reg.set_zero(src & self.reg.a);
            }
            Op::BMI => {
                if self.reg.get_flag(Fl::S) {
                    self.cycles_left_for_op +=
                        if (self.reg.pc & 0xFF00) != ((self.reg.pc + src as u16) & 0xFF00)
                        { 2 } else { 1 };
                    let (result, _carry) = self.reg.pc.overflowing_add(src as u16);
                    self.reg.pc = result;
                }
            }
            Op::BNE => {
                if !self.reg.get_flag(Fl::Z) {
                    self.cycles_left_for_op +=
                        if (self.reg.pc & 0xFF00) != ((self.reg.pc + src as u16) & 0xFF00)
                        { 2 } else { 1 };
                    let (result, _carry) = self.reg.pc.overflowing_add(src as u16);
                    self.reg.pc = result;
                }
            }
            Op::BPL => {
                if !self.reg.get_flag(Fl::S) {
                    self.cycles_left_for_op +=
                        if (self.reg.pc & 0xFF00) != ((self.reg.pc + src as u16) & 0xFF00)
                        { 2 } else { 1 };
                    let (result, _carry) = self.reg.pc.overflowing_add(src as u16);
                    self.reg.pc = result;
                }
            }
            Op::BRK => {
                self.reg.pc += 1;
                self.push_stack((self.reg.pc >> 8) as u8);
                self.push_stack((self.reg.pc & 0xff) as u8);
                self.reg.set_flag(Fl::B, true);
                self.push_stack(self.reg.p);
                self.reg.set_flag(Fl::I, true);
                self.reg.pc = self.mem.get_address(0xFFFE) as u16
                    | ((self.mem.get_address(0xFFFF) as u16) << 8);
            }
            Op::BVC => {
                if !self.reg.get_flag(Fl::V) {
                    self.cycles_left_for_op +=
                        if (self.reg.pc & 0xFF00) != ((self.reg.pc + src as u16) & 0xFF00)
                        { 2 } else { 1 };
                    let (result, _carry) = self.reg.pc.overflowing_add(src as u16);
                    self.reg.pc = result;
                }
            }
            Op::BVS => {
                if self.reg.get_flag(Fl::V) {
                    self.cycles_left_for_op +=
                        if (self.reg.pc & 0xFF00) != ((self.reg.pc + src as u16) & 0xFF00)
                        { 2 } else { 1 };
                    let (result, _carry) = self.reg.pc.overflowing_add(src as u16);
                    self.reg.pc = result;
                }
            }
            Op::CLC => self.reg.set_flag(Fl::C, false),
            Op::CLD => self.reg.set_flag(Fl::D, false),
            Op::CLI => self.reg.set_flag(Fl::I, false),
            Op::CLV => self.reg.set_flag(Fl::V, false),
            Op::CMP => {
                let (src, carry) = self.reg.a.overflowing_sub(src);
                self.reg.set_flag(Fl::C, carry);
                self.reg.set_sign(src);
                self.reg.set_zero(src)
            }
            Op::CPX => {
                let (src, carry) = self.reg.x.overflowing_sub(src);
                self.reg.set_flag(Fl::C, carry);
                self.reg.set_sign(src);
                self.reg.set_zero(src)
            }
            Op::CPY => {
                let (src, carry) = self.reg.y.overflowing_sub(src);
                self.reg.set_flag(Fl::C, carry);
                self.reg.set_sign(src);
                self.reg.set_zero(src)
            }
            Op::DEC => {
                let (src, _overflow) = src.overflowing_sub(1);
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                match dest {
                    Dest::Adr(a) => {
                        self.mem.set_address(a, src);
                    }
                    _ => panic!("Invalid destination for DEC"),
                }
            }
            Op::DEX => {
                let src = self.reg.x;
                let (src, _overflow) = src.overflowing_sub(1);
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                self.reg.x = src;
            }
            Op::DEY => {
                let src = self.reg.y;
                let (src, _overflow) = src.overflowing_sub(1);
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                self.reg.y = src;
            }
            Op::EOR => {
                src ^= self.reg.a;
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                self.reg.a = src;
            }
            Op::INC => {
                let (src, _overflow) = src.overflowing_add(1);
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                match dest {
                    Dest::Adr(a) => {
                        self.mem.set_address(a, src);
                    }
                    _ => panic!("Invalid destination for INC"),
                }
            }
            Op::INX => {
                let src = self.reg.x;
                let (src, _overflow) = src.overflowing_add(1);
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                self.reg.x = src;
            }
            Op::INY => {
                let src = self.reg.y;
                let (src, _overflow) = src.overflowing_add(1);
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                self.reg.y = src;
            }
            Op::JMP => match dest {
                Dest::Adr(a) => self.reg.pc = a,
                _ => panic!("No address provided to JMP"),
            },
            Op::JSR => {
                self.reg.pc -= 1;
                self.push_stack(((self.reg.pc >> 8) & 0xff) as u8);
                self.push_stack((self.reg.pc & 0xff) as u8);
                self.reg.pc = src as u16;
            }
            Op::LDA => {
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                self.reg.a = src;
            }
            Op::LDX => {
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                self.reg.x = src;
            }
            Op::LDY => {
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                self.reg.y = src;
            }
            Op::LSR => {
                let (src, overflow) = src.overflowing_shr(1);
                self.reg.set_flag(Fl::C, overflow);
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                match dest {
                    Dest::Adr(a) => {
                        self.mem.set_address(a, src);
                    }
                    Dest::Acc => {
                        self.reg.a = src;
                    }
                    _ => panic!("Invalid destination for LSR"),
                }
            }
            Op::NOP => {}
            Op::ORA => {
                src |= self.reg.a;
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                self.reg.a = src;
            }
            Op::PHA => {
                self.push_stack(self.reg.a);
            }
            Op::PHP => self.push_stack(self.reg.p),
            Op::PLA => {
                src = self.pull_stack();
                self.reg.set_sign(src);
                self.reg.set_zero(src);
            }
            Op::PLP => {
                self.reg.p = self.pull_stack();
            }
            Op::ROL => {
                let (mut src, overflow) = src.overflowing_shl(1);
                if self.reg.get_flag(Fl::C) {
                    src |= 0x1;
                }
                self.reg.set_flag(Fl::C, overflow);
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                match dest {
                    Dest::Adr(a) => {
                        self.mem.set_address(a, src);
                    }
                    Dest::Acc => {
                        self.reg.a = src;
                    }
                    _ => panic!("Invalid destination for ROL"),
                }
            }
            Op::ROR => {
                let (mut src, overflow) = src.overflowing_shr(1);
                if self.reg.get_flag(Fl::C) {
                    src |= 0x80;
                }
                self.reg.set_flag(Fl::C, overflow);
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                match dest {
                    Dest::Adr(a) => {
                        self.mem.set_address(a, src);
                    }
                    Dest::Acc => {
                        self.reg.a = src;
                    }
                    _ => panic!("Invalid destination for ROR"),
                }
            }
            Op::RTI => {
                src = self.pull_stack();
                self.reg.p = src;
                let mut src = self.pull_stack() as u16;
                src |= (self.pull_stack() as u16) << 8;
                self.reg.pc = src;
            }
            Op::RTS => {
                let mut src = self.pull_stack() as u16;
                src += ((self.pull_stack() as u16) << 8) + 1;
                self.reg.pc = src;
            }
            Op::SBC => {
                let (tmp, overflow1) = (self.reg.a as usize).overflowing_sub(src as usize);
                let (tmp, overflow2) =
                    tmp.overflowing_sub(if self.reg.get_flag(Fl::C) { 0 } else { 1 });
                self.reg.set_sign(tmp as u8);
                self.reg.set_zero(tmp as u8);
                self.reg.set_flag(
                    Fl::V,
                    (((self.reg.a ^ tmp as u8) & 0x80) != 0)
                        && (((self.reg.a ^ src as u8) & 0x80) != 0),
                );
                if self.reg.get_flag(Fl::D) {
                    unimplemented!()
                }
                self.reg.set_flag(Fl::C, overflow1 || overflow2);
                self.reg.a = tmp as u8;
            }
            Op::SEC => self.reg.set_flag(Fl::C, true),
            Op::SED => self.reg.set_flag(Fl::D, true),
            Op::SEI => self.reg.set_flag(Fl::I, true),
            Op::STA => match dest {
                Dest::Adr(a) => {
                    self.mem.set_address(a, self.reg.a);
                }
                _ => panic!("Invalid destination for STA"),
            },
            Op::STX => match dest {
                Dest::Adr(a) => {
                    self.mem.set_address(a, self.reg.x);
                }
                _ => panic!("Invalid destination for STX"),
            },
            Op::STY => match dest {
                Dest::Adr(a) => {
                    self.mem.set_address(a, self.reg.y);
                }
                _ => panic!("Invalid destination for STY"),
            },
            Op::TAX => {
                let src = self.reg.a;
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                self.reg.x = src;
            }
            Op::TAY => {
                let src = self.reg.a;
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                self.reg.y = src;
            }
            Op::TSX => {
                let src = self.reg.s;
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                self.reg.x = src;
            }
            Op::TXA => {
                let src = self.reg.x;
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                self.reg.a = src;
            }
            Op::TXS => {
                let src = self.reg.a;
                self.reg.s = src;
            }
            Op::TYA => {
                let src = self.reg.y;
                self.reg.set_sign(src);
                self.reg.set_zero(src);
                self.reg.a = src;
            }
        }
    }

    fn push_stack(&mut self, val: u8) {
        self.mem.set_address(self.reg.get_stack_pointer(), val);
        let (sp, overflow) = self.reg.s.overflowing_add(1);
        if overflow {
            eprintln!("STACK OVERFLOWED!")
        }
        self.reg.s = sp;
    }

    fn pull_stack(&mut self) -> u8 {
        let val = self.mem.get_address(self.reg.get_stack_pointer());
        let (sp, overflow) = self.reg.s.overflowing_sub(1);
        if overflow {
            eprintln!("STACK UNDERFLOW!")
        }
        self.reg.s = sp;
        val
    }

    pub fn get_remaining_cycles(&self) -> usize {
        self.cycles_left_for_op
    }
}

impl<T: memory::Memory> Debug for CPU<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Currently executing: {:02X} {:?} {:07} Cycles remaining: {}",
            self.current_opcode, self.current_op, self.current_address, self.cycles_left_for_op
        )
    }
}
