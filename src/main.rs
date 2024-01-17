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

impl Status {
    fn set_zn_flags(&mut self, val: u8) {
        self.set(Status::Z, val == 0);
        self.set(Status::N, val & 0x80 == 0x80);
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
    AND(u8),
    ASL(u8),
    ADC(u8),
    STA(u8),
    BCC(u8),
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
            0x06 => ASL(self.fetch()),
            0x25 => AND(self.fetch()),
            0x65 => ADC(self.fetch()),
            0x85 => STA(self.fetch()),
            0x90 => BCC(self.fetch()),
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
            ASL(addr) => {
                let data = self.memory.read_u8(addr as u16);
                self.sr.set(Status::C, (data >> 7) & 1 > 0);
                let x = data.wrapping_shl(1);
                self.sr.set_zn_flags(x);
                self.memory.write_u8(addr as u16, x);
            }
            AND(addr) => {
                let data = self.memory.read_u8(addr as u16);
                self.acc &= data;
                self.sr.set_zn_flags(self.acc);
            }
            ADC(addr) => {
                let data = self.memory.read_u8(addr as u16);
                let (x, o) = self.acc.overflowing_add(data);
                self.acc = x;
                self.sr.set_zn_flags(self.acc);
                self.sr.set(Status::C, o);
                // TODO: overflow flag
            }
            LDA(data) => {
                self.acc = data;
                self.sr.set_zn_flags(self.acc);
            }
            STA(addr) => {
                self.memory.write_u8(addr as u16, self.acc)
            }
            BCC(offset) => {
                if self.sr.contains(Status::C) {
                    self.pc = self.pc.wrapping_add(offset as u16);
                }
            }
            INC(addr) => {
                let data = self.memory.read_u8(addr as u16);
                let x = data.wrapping_add(1);
                self.memory.write_u8(addr as u16, x);
                self.sr.set_zn_flags(x);
            }
            LDY(data) => {
                self.y = data;
                self.sr.set_zn_flags(self.y);
            }
            INY => {
                self.y = self.y.wrapping_add(1);
                self.sr.set_zn_flags(self.y);
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
fn test_0x06_asl() {
    let mut mem = Memory::with_program(&[0x06, 0x20]);
    mem.write_u8(0x20, 0b0000_0001);
    let mut cpu = CPU::new(mem);
    cpu.tick();
    assert_eq!(cpu.memory.read_u8(0x20), 0b0000_0010);
    assert!(cpu.sr.is_empty());
}

#[test]
fn test_0x06_asl_zero_flag() {
    let mem = Memory::with_program(&[0x06, 0x00]);
    let mut cpu = CPU::new(mem);
    cpu.tick();
    assert!(cpu.sr.contains(Status::Z));
}

#[test]
fn test_0x06_asl_negative_flag() {
    let mut mem = Memory::with_program(&[0x06, 0x20]);
    mem.write_u8(0x20, 0x40);
    let mut cpu = CPU::new(mem);
    cpu.tick();
    // multiplies by 2
    assert_eq!(cpu.memory.read_u8(0x20), 0x80);
    assert!(cpu.sr.contains(Status::N));
}

#[test]
fn test_0x06_asl_carry_flag() {
    let mut mem = Memory::with_program(&[0x06, 0x20]);
    mem.write_u8(0x20, 0b1000_0000);
    let mut cpu = CPU::new(mem);
    cpu.tick();
    assert!(cpu.sr.contains(Status::C));
}

#[test]
fn test_0x25_and() {
    let mut mem = Memory::with_program(&[0x25, 0x20]);
    mem.write_u8(0x20, 0b1010);
    let mut cpu = CPU::new(mem);
    cpu.acc = 0b1111;
    cpu.tick();
    assert_eq!(cpu.acc, 0b1010);
    assert!(cpu.sr.is_empty());
}

#[test]
fn test_0x25_and_zero_flag() {
    let mem = Memory::with_program(&[0x25, 0x00]);
    let mut cpu = CPU::new(mem);
    cpu.acc = 0;
    cpu.tick();
    assert!(cpu.sr.contains(Status::Z));
}

#[test]
fn test_0x25_and_negative_flag() {
    let mut mem = Memory::with_program(&[0x25, 0x20]);
    mem.write_u8(0x20, 0xFF);
    let mut cpu = CPU::new(mem);
    cpu.acc = 0x80;
    cpu.tick();
    assert!(cpu.sr.contains(Status::N));
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
    let mem = Memory::with_program(&[0xA9, 0x80]);
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
fn test_0x90_bcc_with_carry() {
    let mem = Memory::with_program(&[0x90, 0x00, 0xC8]);
    let mut cpu = CPU::new(mem);
    cpu.sr.set(Status::C, true);
    cpu.tick();
    cpu.tick();
    assert_eq!(cpu.y, 1);
}

#[test]
fn test_0x90_bcc_offset() {
    let mem = Memory::with_program(&[
        0x90, 0x02,
        0x00, 0x00, // should never be reached
        0xC8,
    ]);
    let mut cpu = CPU::new(mem);
    cpu.sr.set(Status::C, true);
    cpu.tick();
    cpu.tick();
    assert_eq!(cpu.y, 1);
}

#[test]
fn test_0x90_bcc_no_carry() {
    let mem = Memory::with_program(&[
        0x90, 0x02,
        0xA9, 0xFF,
        0xC8, // shouldn't be reached in test
    ]);
    let mut cpu = CPU::new(mem);
    cpu.sr.set(Status::C, false);
    cpu.tick();
    cpu.tick();
    assert_eq!(cpu.acc, 0xFF);
    // shouldn't have run INY
    assert_eq!(cpu.y, 0);
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
fn test_0x65_adc_negative_flag() {
    let mut mem = Memory::with_program(&[0x65, 0x20]);
    mem.write_u8(0x20, 1);
    let mut cpu = CPU::new(mem);
    cpu.acc = 0x7F;
    cpu.tick();
    assert!(cpu.sr.contains(Status::N));
}

#[test]
fn test_0x65_adc_carry_flag() {
    let mut mem = Memory::with_program(&[0x65, 0x20]);
    mem.write_u8(0x20, 1);
    let mut cpu = CPU::new(mem);
    cpu.acc = 0xFF;
    cpu.tick();
    assert!(cpu.sr.contains(Status::C));
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
fn test_0xe6_inc_zero_flag() {
    let mut mem = Memory::with_program(&[0xE6, 0x20]);
    mem.write_u8(0x20, 0xFF);
    let mut cpu = CPU::new(mem);
    cpu.tick();
    assert!(cpu.sr.contains(Status::Z));
}

#[test]
fn test_0xe6_inc_negative_flag() {
    let mut mem = Memory::with_program(&[0xE6, 0x20]);
    mem.write_u8(0x20, 0x7F);
    let mut cpu = CPU::new(mem);
    cpu.tick();
    assert!(cpu.sr.contains(Status::N));
}

#[test]
fn test_0xa4_ldy() {
    let mem = Memory::with_program(&[0xA4, 42]);
    let mut cpu = CPU::new(mem);
    cpu.tick();
    assert_eq!(cpu.y, 42);
    assert!(cpu.sr.is_empty());
}

#[test]
fn test_0xa4_ldy_zero_flag() {
    let mem = Memory::with_program(&[0xA4, 0x00]);
    let mut cpu = CPU::new(mem);
    cpu.tick();
    assert!(cpu.sr.contains(Status::Z));
}

#[test]
fn test_0x_a4_ldy_negative_flag() {
    let mem = Memory::with_program(&[0xA4, 0x80]);
    let mut cpu = CPU::new(mem);
    cpu.tick();
    assert!(cpu.sr.contains(Status::N));
}

#[test]
fn test_0xc8_iny() {
    let mem = Memory::with_program(&[0xC8]);
    let mut cpu = CPU::new(mem);
    cpu.y = 41;
    cpu.tick();
    assert_eq!(cpu.y, 42);
    assert!(cpu.sr.is_empty());
}

#[test]
fn test_0xc8_iny_zero_flag() {
    let mem = Memory::with_program(&[0xC8]);
    let mut cpu = CPU::new(mem);
    cpu.y = 0xFF;
    cpu.tick();
    assert!(cpu.sr.contains(Status::Z));
}

#[test]
fn test_0xc8_iny_negative_flag() {
    let mem = Memory::with_program(&[0xC8]);
    let mut cpu = CPU::new(mem);
    cpu.y = 0x7F;
    cpu.tick();
    assert!(cpu.sr.contains(Status::N));
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
