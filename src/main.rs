use bitflags::bitflags;

const ROM_BASE_ADDRESS: u16 = 0x8000;
const MEMORY_SIZE: usize = 0xFFFF;

#[derive(Debug)]
struct Memory([u8; MEMORY_SIZE]);

impl Memory {
    pub fn new() -> Self {
        Memory([0; MEMORY_SIZE])
    }

    pub fn with_program(rom: &[u8]) -> Self {
        let mut mem = Memory::new();
        mem.load(rom, ROM_BASE_ADDRESS);
        mem
    }

    pub fn load(&mut self, src: &[u8], pos: u16) {
        let range = (pos as usize)..(pos as usize) + src.len();
        self.0[range].copy_from_slice(src);
    }

    pub fn read_u8(&self, pos: u16) -> u8 {
        self.0[pos as usize]
    }

    pub fn write_u8(&mut self, pos: u16, data: u8) {
        self.0[pos as usize] = data;
    }
}

bitflags! {
    #[derive(Debug, Copy, Clone, PartialEq)]
    pub struct Status: u8 {
        const C = 0b0000_0001; // Carry
        const Z = 0b0000_0010; // Zero
        const I = 0b0000_0100; // Disable Interrupt
        const D = 0b0000_1000; // Decimal Mode
        const B = 0b0001_0000; // Break
        const U = 0b0010_0000; // Unused
        const V = 0b0100_0000; // Overflow
        const N = 0b1000_0000; // Negative
    }
}

// naming conventions from https://www.masswerk.at/6502/6502_instruction_set.html
#[derive(Debug)]
struct CPU {
    // acccumulator
    acc: u8,
    // X register
    x: u8,
    // Y register
    y: u8,
    // status register [NV-BDIZC]
    sr: Status,
    // stacck pointer
    sp: u8,
    // program counter
    pc: u16,
    memory: Memory,
}

#[derive(Debug)]
#[allow(clippy::upper_case_acronyms)]
// FIXME: only zero-page access currently supported
enum Instruction {
    BRK,
    ADC(u8),
    STA(u8),
    LDY(u8),
    LDA(u8),
    INY,
    INC(u8),
    Illegal(u8),
}

impl CPU {
    pub fn new(memory: Memory) -> CPU {
        CPU {
            acc: 0,
            x: 0,
            y: 0,
            sr: Status::U & Status::I,
            sp: 0,
            pc: 0x8000,
            memory,
        }
    }

    fn fetch(&mut self) -> u8 {
        let opcode = self.memory.read_u8(self.pc);
        self.pc += 1;
        opcode
    }

    // may step PC if opcode requires data
    fn decode(&mut self, opcode: u8) -> Instruction {
        use Instruction::*;
        match opcode {
            0x00 => BRK,
            0x65 => ADC(self.fetch()),
            0x85 => STA(self.fetch()),
            0xA4 => LDY(self.fetch()),
            0xA9 => LDA(self.fetch()),
            0xC8 => INY,
            0xE6 => INC(self.fetch()),
            _ => Illegal(opcode)
        }
    }

    fn execute(&mut self, inst: Instruction) {
        use Instruction::*;
        match inst {
            BRK => {
                // TODO
                // loop forever until we come up with a better
                // way of handling this
                loop {}
            }
            ADC(addr) => {
                self.acc += self.memory.read_u8(addr as u16);

                self.sr.set(Status::Z, self.acc == 0);
                self.sr.set(Status::N, self.acc & 0b1000_0000 != 0);
                // TODO: carry flag
            }
            LDA(data) => {
                self.acc = data;

                self.sr.set(Status::Z, self.acc == 0);
                self.sr.set(Status::N, self.acc & 0b1000_0000 != 0);
            }
            STA(addr) => {
                self.memory.write_u8(addr as u16, self.acc)
            }
            INC(addr) => {
                let data = self.memory.read_u8(addr as u16);
                // TODO: handle flags & overflow
                self.memory.write_u8(addr as u16, data + 1);
            }
            LDY(data) => {
                self.y = data;
                // TODO: flags
            }
            INY => {
                self.y += 1;
                // TODO: flags
            }
            Illegal(opcode) => panic!("illegal opcode: 0x{:02X}", opcode)
        }
    }

    pub fn tick(&mut self) {
        let opcode = self.fetch();
        let inst = self.decode(opcode);
        self.execute(inst);
    }
}

#[test]
fn test_0x00_brk() {
    // TODO
}

#[test]
fn test_0xa9_lda_immediate() {
    let mem = Memory::with_program(&[0xA9, 0x05]);
    let mut cpu = CPU::new(mem);
    cpu.tick();
    assert_eq!(cpu.acc, 0x05);
    assert!(cpu.sr.is_empty());
}

#[test]
fn test_0xa9_lda_zero_flag() {
    let mem = Memory::with_program(&[0xA9, 0x00]);
    let mut cpu = CPU::new(mem);
    cpu.tick();
    assert!(cpu.sr.contains(Status::Z));
}

#[test]
fn test_0xa9_lda_negative_flag() {
    let mem = Memory::with_program(&[0xA9, 0xFF]);
    let mut cpu = CPU::new(mem);
    cpu.tick();
    assert!(cpu.sr.contains(Status::N));
}

#[test]
fn test_0x85_sta() {
    let mem = Memory::with_program(&[0x85, 0xFF]);
    let mut cpu = CPU::new(mem);
    cpu.acc = 42;
    cpu.tick();
    assert_eq!(cpu.memory.read_u8(0xFF), 42);
}

#[test]
fn test_0x65_adc() {
    let mut mem = Memory::with_program(&[0x65, 0x20]);
    mem.write_u8(0x20, 2);
    let mut cpu = CPU::new(mem);
    cpu.acc = 40;
    cpu.tick();
    assert_eq!(cpu.acc, 42);
    assert!(cpu.sr.is_empty());
}

#[test]
fn test_0x65_adc_zero_flag() {
    let mem = Memory::with_program(&[0x65, 0x00]);
    let mut cpu = CPU::new(mem);
    cpu.acc = 0;
    cpu.tick();
    assert!(cpu.sr.contains(Status::Z));
}

#[test]
fn test_0xe6_inc() {
    let mut mem = Memory::with_program(&[0xE6, 0x20]);
    mem.write_u8(0x20, 41);
    let mut cpu = CPU::new(mem);
    cpu.tick();
    assert_eq!(cpu.memory.read_u8(0x20), 42);
}

#[test]
fn test_0xa4_ldy() {
    let mem = Memory::with_program(&[0xA4, 0xFF]);
    let mut cpu = CPU::new(mem);
    cpu.tick();
    assert_eq!(cpu.y, 0xFF);
}

#[test]
fn test_0xc8_iny() {
    let mem = Memory::with_program(&[0xC8]);
    let mut cpu = CPU::new(mem);
    cpu.y = 41;
    cpu.tick();
    assert_eq!(cpu.y, 42);
}

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
    let memory = Memory::with_program(&program);
    let mut cpu = CPU::new(memory);
    loop {
        cpu.tick();
    }
}
