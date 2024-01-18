use cpu::CPU;
use memory::Memory;

mod cpu;
mod memory;

fn main() {
    let program = vec![
        0xA9, 0x10, // LDA #$10 -> A = #$10
        0x85, 0x20, // STA $20  -> $20 = #$10
        0xA9, 0x01, // LDA #$1  -> A = #$1
        0x65, 0x20, // ADC $20  -> A = #$11
        0x85, 0x21, // STA $21  -> $21=#$11
        0xE6, 0x21, // INC $21  -> $21=#$12
        0xA4, 0x21, // LDY $21  -> Y=#$12
        0xC8,       // INY      -> Y=#$13
        0x00,       // BRK
    ];
    let memory = Memory::from(program.as_slice());
    let mut cpu = CPU::new(memory);
    loop {
        cpu.tick();
    }
}
