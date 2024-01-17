use bitflags::bitflags;
use crate::memory::Memory;

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
pub struct CPU {
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
    ADC(u8),
    AND(u8),
    ASL(u8),
    BRK,
    BCC(u8),
    CLC,
    CLD,
    CLI,
    CLV,
    DEX,
    DEY,
    INC(u8),
    INX,
    INY,
    LDA(u8), // Immediate
    LDX(u8), // Immediate
    LDY(u8), // Immediate
    NOP,
    SEC,
    SED,
    SEI,
    STA(u8),
    Illegal(u8),
}

impl CPU {
    pub fn new(memory: Memory) -> CPU {
        CPU {
            acc: 0,
            x: 0,
            y: 0,
            sr: Status::U & Status::I,
            sp: 0xFD,
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
            0x18 => CLC,
            0x25 => AND(self.fetch()),
            0x38 => SEC,
            0x58 => CLI,
            0x65 => ADC(self.fetch()),
            0x78 => SEI,
            0x85 => STA(self.fetch()),
            0x88 => DEY,
            0x90 => BCC(self.fetch()),
            0xA4 => LDY(self.fetch()),
            0xA6 => LDX(self.fetch()),
            0xA9 => LDA(self.fetch()),
            0xB8 => CLV,
            0xC8 => INY,
            0xCA => DEX,
            0xD8 => CLD,
            0xE6 => INC(self.fetch()),
            0xE8 => INX,
            0xEA => NOP,
            0xF8 => SED,
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
            CLC => {
                self.sr.set(Status::C, false);
            }
            CLD => {
                self.sr.set(Status::D, false);
            }
            CLI => {
                self.sr.set(Status::I, false);
            }
            CLV => {
                self.sr.set(Status::V, false);
            }
            DEX => {
                self.x = self.x.wrapping_sub(1);
                self.sr.set_zn_flags(self.x);
            }
            DEY => {
                self.y = self.y.wrapping_sub(1);
                self.sr.set_zn_flags(self.y);
            }
            LDA(data) => {
                self.acc = data;
                self.sr.set_zn_flags(self.acc);
            }
            SEC => {
                self.sr.set(Status::C, true);
            }
            SED => {
                self.sr.set(Status::D, true);
            }
            SEI => {
                self.sr.set(Status::I, true);
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
            LDX(data) => {
                self.x = data;
                self.sr.set_zn_flags(self.x);
            }
            LDY(data) => {
                self.y = data;
                self.sr.set_zn_flags(self.y);
            }
            NOP => {}
            INX => {
                self.x = self.x.wrapping_add(1);
                self.sr.set_zn_flags(self.x);
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

#[cfg(test)]
mod tests {
    use super::*;

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
    fn test_0x18_clc() {
        let mem = Memory::with_program(&[0x18]);
        let mut cpu = CPU::new(mem);
        cpu.sr.set(Status::C, true);
        cpu.tick();
        assert_eq!(cpu.sr.contains(Status::C), false);
    }

    #[test]
    fn test_0xd8_cld() {
        let mem = Memory::with_program(&[0xD8]);
        let mut cpu = CPU::new(mem);
        cpu.sr.set(Status::D, true);
        cpu.tick();
        assert_eq!(cpu.sr.contains(Status::D), false);
    }

    #[test]
    fn test_0x58_cli() {
        let mem = Memory::with_program(&[0x58]);
        let mut cpu = CPU::new(mem);
        cpu.sr.set(Status::I, true);
        cpu.tick();
        assert_eq!(cpu.sr.contains(Status::I), false);
    }

    #[test]
    fn test_0xb8_clv() {
        let mem = Memory::with_program(&[0xB8]);
        let mut cpu = CPU::new(mem);
        cpu.sr.set(Status::V, true);
        cpu.tick();
        assert_eq!(cpu.sr.contains(Status::V), false);
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
            0xFF, 0xFF, // should never be reached
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
    fn test_0xa6_ldx() {
        let mem = Memory::with_program(&[0xA6, 42]);
        let mut cpu = CPU::new(mem);
        cpu.tick();
        assert_eq!(cpu.x, 42);
        assert!(cpu.sr.is_empty());
    }

    #[test]
    fn test_0xa6_ldx_zero_flag() {
        let mem = Memory::with_program(&[0xA6, 0]);
        let mut cpu = CPU::new(mem);
        cpu.tick();
        assert!(cpu.sr.contains(Status::Z));
    }

    #[test]
    fn test_0xa6_ldx_negative_flag() {
        let mem = Memory::with_program(&[0xA6, 0x80]);
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
    fn test_0xa4_ldy_negative_flag() {
        let mem = Memory::with_program(&[0xA4, 0x80]);
        let mut cpu = CPU::new(mem);
        cpu.tick();
        assert!(cpu.sr.contains(Status::N));
    }

    #[test]
    fn test_0xe8_inx() {
        let mem = Memory::with_program(&[0xE8]);
        let mut cpu = CPU::new(mem);
        cpu.x = 41;
        cpu.tick();
        assert_eq!(cpu.x, 42);
        assert!(cpu.sr.is_empty());
    }

    #[test]
    fn test_0xe8_inx_zero_flag() {
        let mem = Memory::with_program(&[0xE8]);
        let mut cpu = CPU::new(mem);
        cpu.x = 0xFF;
        cpu.tick();
        assert_eq!(cpu.x, 0);
        assert!(cpu.sr.contains(Status::Z));
    }

    #[test]
    fn test_0xe8_inx_negative_flag() {
        let mem = Memory::with_program(&[0xE8]);
        let mut cpu = CPU::new(mem);
        cpu.x = 0x7F;
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
        assert_eq!(cpu.y, 0);
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

    #[test]
    fn test_0xca_dex() {
        let mem = Memory::with_program(&[0xCA]);
        let mut cpu = CPU::new(mem);
        cpu.x = 2;
        cpu.tick();
        assert_eq!(cpu.x, 1);
        assert!(cpu.sr.is_empty());
    }

    #[test]
    fn test_0xca_dex_underflow() {
        let mem = Memory::with_program(&[0xCA]);
        let mut cpu = CPU::new(mem);
        cpu.x = 0;
        cpu.tick();
        assert_eq!(cpu.x, 0xFF);
    }

    #[test]
    fn test_0xca_dex_zero_flag() {
        let mem = Memory::with_program(&[0xCA]);
        let mut cpu = CPU::new(mem);
        cpu.x = 1;
        cpu.tick();
        assert_eq!(cpu.x, 0);
        assert!(cpu.sr.contains(Status::Z));
    }

    #[test]
    fn test_0xca_dex_negative_flag() {
        let mem = Memory::with_program(&[0xCA]);
        let mut cpu = CPU::new(mem);
        cpu.x = 0xFF;
        cpu.tick();
        assert_eq!(cpu.x, 0xFE);
        assert!(cpu.sr.contains(Status::N));
    }

    #[test]
    fn test_0x88_dey() {
        let mem = Memory::with_program(&[0x88]);
        let mut cpu = CPU::new(mem);
        cpu.y = 2;
        cpu.tick();
        assert_eq!(cpu.y, 1);
        assert!(cpu.sr.is_empty());
    }

    #[test]
    fn test_0x88_dey_underflow() {
        let mem = Memory::with_program(&[0x88]);
        let mut cpu = CPU::new(mem);
        cpu.y = 0;
        cpu.tick();
        assert_eq!(cpu.y, 0xFF);
    }

    #[test]
    fn test_0x88_dey_zero_flag() {
        let mem = Memory::with_program(&[0x88]);
        let mut cpu = CPU::new(mem);
        cpu.y = 1;
        cpu.tick();
        assert_eq!(cpu.y, 0);
        assert!(cpu.sr.contains(Status::Z));
    }

    #[test]
    fn test_0x88_dey_negative_flag() {
        let mem = Memory::with_program(&[0x88]);
        let mut cpu = CPU::new(mem);
        cpu.y = 0xFF;
        cpu.tick();
        assert_eq!(cpu.y, 0xFE);
        assert!(cpu.sr.contains(Status::N));
    }

    #[test]
    fn test_0xea_nop() {
        let mem = Memory::with_program(&[0xEA]);
        let mut cpu = CPU::new(mem);
        cpu.tick();
        // as long as we don't panic, we're good
    }

    #[test]
    fn test_0x38_sec() {
        let mem = Memory::with_program(&[0x38]);
        let mut cpu = CPU::new(mem);
        cpu.sr.set(Status::C, false);
        cpu.tick();
        assert!(cpu.sr.contains(Status::C));
    }

    #[test]
    fn test_0xf8_sed() {
        let mem = Memory::with_program(&[0xF8]);
        let mut cpu = CPU::new(mem);
        cpu.sr.set(Status::D, false);
        cpu.tick();
        assert!(cpu.sr.contains(Status::D));
    }

    #[test]
    fn test_0x78_sei() {
        let mem = Memory::with_program(&[0x78]);
        let mut cpu = CPU::new(mem);
        cpu.sr.set(Status::I, false);
        cpu.tick();
        assert!(cpu.sr.contains(Status::I));
    }
}
