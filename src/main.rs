const MEMORY_SIZE: usize = 0xFFFF;

#[derive(Debug)]
struct Memory([u8; MEMORY_SIZE]);

impl Memory {
    pub fn new() -> Memory {
        Memory([0; MEMORY_SIZE])
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
    sr: u8,
    // stacck pointer
    sp: u8,
    // program counter
    pc: u16,
    memory: Memory,
}

#[derive(Debug)]
enum Instruction {
    LoadAccumulator(u8),
    Invalid(u8),
}

impl CPU {
    pub fn new(memory: Memory) -> CPU {
        CPU {
            acc: 0,
            x: 0,
            y: 0,
            sr: 0,
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

    fn decode(&mut self, opcode: u8) -> Instruction {
        use Instruction::*;
        match opcode {
            0xA9 => LoadAccumulator(self.fetch()),
            _ => Invalid(opcode)
        }
    }

    fn execute(&mut self, inst: Instruction) {
        use Instruction::*;
        match inst {
            LoadAccumulator(param) => {
                self.acc = param;

                if self.acc == 0 {
                    // TODO: make a nice way of setting flags
                    self.sr |= 0b0000_0010;
                } else {
                    self.sr &= 0b1111_1101;
                }

                if self.acc & 0b1000_0000 != 0 {
                    self.sr |= 0b1000_0000;
                } else {
                    self.sr &= 0b0111_1111;
                }
            }
            Invalid(opcode) => panic!("invalid opcode: 0x{:02X}", opcode)
        }
    }

    pub fn tick(&mut self) {
        let opcode = self.fetch();
        let inst = self.decode(opcode);
        self.execute(inst);
    }
}

#[test]
fn test_0xa9_lda_immediate() {
    let mut mem = Memory::new();
    mem.load(&[0xA9, 0x05], 0x8000);
    let mut cpu = CPU::new(mem);
    cpu.tick();
    assert_eq!(cpu.acc, 0x05);
    assert_eq!(cpu.sr & 0b0000_0010, 0);
    assert_eq!(cpu.sr & 0b1000_0000, 0);
}

#[test]
fn test_0xa9_lda_zero_flag() {
    let mut mem = Memory::new();
    mem.load(&[0xA9, 0x00], 0x8000);
    let mut cpu = CPU::new(mem);
    cpu.tick();
    assert_eq!(cpu.sr & 0b0000_0010, 0b10);
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
    let mut memory = Memory::new();
    memory.load(&program, 0x8000);

    let mut cpu = CPU::new(memory);
    cpu.tick();
    println!("Hello CPU: {:?}", cpu);
}
