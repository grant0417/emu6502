use emu6502::{FullMemory, CPU, ROM};
use std::fs;

fn main() {
    let mut cpu = CPU::new(FullMemory::new());

    let rom = ROM::new(&fs::read("roms/fib.hex").unwrap());
    println!("{:?}", rom);

    cpu.mem.load_into_mem(&rom, 0x00);

    loop {
        println!("{:?}", cpu);
        println!("{:?}", cpu.reg);
        println!();
        std::thread::sleep(std::time::Duration::from_millis(500));
        cpu.step();
    }
}
