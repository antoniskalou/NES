use crate::memory::Memory;
use bitflags::bitflags;

// 2KB working RAM for the CPU
const WRAM_SIZE: usize = 0x0800;
// not the real size of a rom, just for now
const ROM_SIZE: usize = 0x0F00;

#[allow(clippy::upper_case_acronyms)]
type WRAM = Memory<WRAM_SIZE>;

#[allow(clippy::upper_case_acronyms)]
type ROM = Memory<ROM_SIZE>;

/// see https://www.nesdev.org/obelisk-6502-guide/addressing.html
#[derive(Debug)]
pub enum AddressingMode {
    Implicit,
    Accumulator,
    Immediate(u8),
    ZeroPage(u8),
    ZeroPageX(u8),
    ZeroPageY(u8),
    Relative(i8),
    Absolute,
    AbsoluteX,
    AbsoluteY,
    Indirect,
    IndexedIndirect,
    IndirectIndexed,
}

bitflags! {
    /// see https://www.nesdev.org/obelisk-6502-guide/registers.html
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
    fn set_n_flag(&mut self, val: u8) {
        self.set(Status::N, val & 0x80 == 0x80);
    }

    fn set_zn_flags(&mut self, val: u8) {
        self.set(Status::Z, val == 0);
        self.set_n_flag(val);
    }
}

/// see https://www.nesdev.org/obelisk-6502-guide/reference.html
#[derive(Debug)]
#[allow(clippy::upper_case_acronyms)]
#[rustfmt::skip]
enum Opcode {
    ADC, AND, ASL, BCC, BCS, BEQ, BIT, BMI, BNE, BPL, BRK, BVC, BVS, CLC, CLD,
    CLI, CLV, CMP, CPX, CPY, DEC, DEX, DEY, EOR, INC, INX, INY, JMP, JSR, LDA,
    LDX, LDY, LSR, NOP, ORA, PHA, PHP, PLA, PLP, ROL, ROR, RTI, RTS, SBC, SEC,
    SED, SEI, STA, STX, STY, TAX, TAY, TSX, TXA, TXS, TYA, Illegal(u8),
}

#[derive(Debug)]
struct Instruction {
    opcode: Opcode,
    mode: AddressingMode,
}

#[derive(Debug)]
pub struct CPU {
    // accumulator
    a: u8,
    // X register
    x: u8,
    // Y register
    y: u8,
    // status register [NV-BDIZC]
    p: Status,
    // stack pointer
    sp: u8,
    // program counter
    pc: u16,
    wram: WRAM,
    rom: ROM,
}

impl CPU {
    pub fn new(rom: ROM) -> CPU {
        let wram = WRAM::new();
        CPU {
            a: 0,
            x: 0,
            y: 0,
            p: Status::U & Status::I,
            sp: 0xFD,
            pc: 0,
            rom,
            wram,
        }
    }

    fn read_operand(&self, mode: &AddressingMode) -> u8 {
        use AddressingMode::*;
        match *mode {
            Immediate(data) => data,
            Accumulator => self.a,
            ZeroPage(addr) => self.wram.read_u8(addr as u16),
            ZeroPageX(addr) => {
                let addr = addr + self.x;
                self.wram.read_u8(addr as u16)
            }
            ZeroPageY(addr) => {
                let addr = addr + self.y;
                self.wram.read_u8(addr as u16)
            }
            _ => panic!("unsupported read mode: {:?}", mode),
        }
    }

    fn write_operand(&mut self, mode: AddressingMode, data: u8) {
        use AddressingMode::*;
        match mode {
            Accumulator => self.a = data,
            ZeroPage(addr) => self.wram.write_u8(addr as u16, data),
            ZeroPageX(addr) => {
                let addr = addr + self.x;
                self.wram.write_u8(addr as u16, data);
            }
            ZeroPageY(addr) => {
                let addr = addr + self.y;
                self.wram.write_u8(addr as u16, data);
            }
            _ => panic!("unsupported write mode: {:?}", mode),
        }
    }

    fn branch(&mut self, offset: i8) {
        self.pc = self.pc.wrapping_add_signed(offset as i16);
    }

    fn fetch(&mut self) -> u8 {
        let opcode = self.rom.read_u8(self.pc);
        self.pc += 1;
        opcode
    }

    // may step PC if opcode requires data
    fn decode(&mut self, opcode: u8) -> Instruction {
        use AddressingMode::*;
        use Opcode::*;
        let (opcode, mode) = match opcode {
            0x00 => (BRK, Implicit),
            0x05 => (ORA, ZeroPage(self.fetch())),
            0x06 => (ASL, ZeroPage(self.fetch())),
            0x09 => (ORA, Immediate(self.fetch())),
            0x0A => (ASL, Accumulator),
            0x10 => (BPL, Relative(self.fetch() as i8)),
            0x15 => (ORA, ZeroPageX(self.fetch())),
            0x16 => (ASL, ZeroPageX(self.fetch())),
            0x18 => (CLC, Implicit),
            0x25 => (AND, ZeroPage(self.fetch())),
            0x26 => (ROL, ZeroPage(self.fetch())),
            0x29 => (AND, Immediate(self.fetch())),
            0x2A => (ROL, Accumulator),
            0x30 => (BMI, Relative(self.fetch() as i8)),
            0x35 => (AND, ZeroPageX(self.fetch())),
            0x36 => (ROL, ZeroPageX(self.fetch())),
            0x38 => (SEC, Implicit),
            0x46 => (LSR, ZeroPage(self.fetch())),
            0x4A => (LSR, Accumulator),
            0x50 => (BVC, Relative(self.fetch() as i8)),
            0x56 => (LSR, ZeroPageX(self.fetch())),
            0x58 => (CLI, Implicit),
            0x65 => (ADC, ZeroPage(self.fetch())),
            0x66 => (ROR, ZeroPage(self.fetch())),
            0x69 => (ADC, Immediate(self.fetch())),
            0x6A => (ROR, Accumulator),
            0x70 => (BVS, Relative(self.fetch() as i8)),
            0x75 => (ADC, ZeroPageX(self.fetch())),
            0x76 => (ROR, ZeroPageX(self.fetch())),
            0x78 => (SEI, Implicit),
            0x85 => (STA, ZeroPage(self.fetch())),
            0x88 => (DEY, Implicit),
            0x8A => (TXA, Implicit),
            // conversion from u8 to i8 uses the same schemantics as the CPU
            0x90 => (BCC, Relative(self.fetch() as i8)),
            0x95 => (STA, ZeroPageX(self.fetch())),
            0x98 => (TYA, Implicit),
            0xA0 => (LDY, Immediate(self.fetch())),
            0xA2 => (LDX, Immediate(self.fetch())),
            0xA4 => (LDY, ZeroPage(self.fetch())),
            0xA5 => (LDA, ZeroPage(self.fetch())),
            0xA6 => (LDX, ZeroPage(self.fetch())),
            0xA8 => (TAY, Implicit),
            0xA9 => (LDA, Immediate(self.fetch())),
            0xAA => (TAX, Implicit),
            0xB0 => (BCS, Relative(self.fetch() as i8)),
            0xB4 => (LDY, ZeroPageX(self.fetch())),
            0xB5 => (LDA, ZeroPageX(self.fetch())),
            0xB6 => (LDX, ZeroPageY(self.fetch())),
            0xB8 => (CLV, Implicit),
            0xC5 => (CMP, ZeroPage(self.fetch())),
            0xC6 => (DEC, ZeroPage(self.fetch())),
            0xC8 => (INY, Implicit),
            0xC9 => (CMP, Immediate(self.fetch())),
            0xCA => (DEX, Implicit),
            0xD0 => (BNE, Relative(self.fetch() as i8)),
            0xD5 => (CMP, ZeroPageX(self.fetch())),
            0xD6 => (DEC, ZeroPageX(self.fetch())),
            0xD8 => (CLD, Implicit),
            0xE0 => (CPX, Immediate(self.fetch())),
            0xE4 => (CPX, ZeroPage(self.fetch())),
            0xE5 => (SBC, ZeroPage(self.fetch())),
            0xE6 => (INC, ZeroPage(self.fetch())),
            0xE8 => (INX, Implicit),
            0xE9 => (SBC, Immediate(self.fetch())),
            0xEA => (NOP, Implicit),
            0xF0 => (BEQ, Relative(self.fetch() as i8)),
            0xF5 => (SBC, ZeroPageX(self.fetch())),
            0xF6 => (INC, ZeroPageX(self.fetch())),
            0xF8 => (SED, Implicit),
            _ => (Illegal(opcode), Implicit),
        };
        Instruction { opcode, mode }
    }

    fn execute(&mut self, inst: Instruction) {
        use AddressingMode::*;
        use Opcode::*;
        match (inst.opcode, inst.mode) {
            (ASL, mode) => {
                let data = self.read_operand(&mode);
                self.p.set(Status::C, (data >> 7) & 1 != 0);
                let x = data.wrapping_shl(1);
                self.p.set_zn_flags(x);
                self.write_operand(mode, x);
            }
            (AND, mode) => {
                let data = self.read_operand(&mode);
                self.a &= data;
                self.p.set_zn_flags(self.a);
            }
            (ADC, mode) => {
                let data = self.read_operand(&mode);
                let (x, o) = self.a.overflowing_add(data);
                self.a = x;
                self.p.set_zn_flags(self.a);
                self.p.set(Status::C, o);
                // TODO: overflow flag
            }
            (BCC, Relative(offset)) => {
                if !self.p.contains(Status::C) {
                    self.branch(offset);
                }
            }
            (BCS, Relative(offset)) => {
                if self.p.contains(Status::C) {
                    self.branch(offset);
                }
            }
            (BEQ, Relative(offset)) => {
                if self.p.contains(Status::Z) {
                    self.branch(offset);
                }
            }
            (BMI, Relative(offset)) => {
                if self.p.contains(Status::N) {
                    self.branch(offset);
                }
            }
            (BNE, Relative(offset)) => {
                if !self.p.contains(Status::Z) {
                    self.branch(offset);
                }
            }
            (BPL, Relative(offset)) => {
                if !self.p.contains(Status::N) {
                    self.branch(offset);
                }
            }
            (BRK, Implicit) => {
                todo!("CPU halt");
            }
            (BVC, Relative(offset)) => {
                if !self.p.contains(Status::V) {
                    self.branch(offset);
                }
            }
            (BVS, Relative(offset)) => {
                if self.p.contains(Status::V) {
                    self.branch(offset);
                }
            }
            (CLC, Implicit) => {
                self.p.set(Status::C, false);
            }
            (CLD, Implicit) => {
                self.p.set(Status::D, false);
            }
            (CLI, Implicit) => {
                self.p.set(Status::I, false);
            }
            (CLV, Implicit) => {
                self.p.set(Status::V, false);
            }
            (CMP, mode) => {
                let data = self.read_operand(&mode);
                self.p.set(Status::C, self.a >= data);
                self.p.set(Status::Z, self.a == data);
                self.p.set_n_flag(self.a);
            }
            (CPX, mode) => {
                let data = self.read_operand(&mode);
                self.p.set(Status::C, self.x >= data);
                self.p.set(Status::Z, self.x == data);
                self.p.set_n_flag(self.x);
            }
            (DEC, mode) => {
                let data = self.read_operand(&mode);
                let x = data.wrapping_sub(1);
                self.p.set_zn_flags(x);
                self.write_operand(mode, x);
            }
            (DEX, Implicit) => {
                self.x = self.x.wrapping_sub(1);
                self.p.set_zn_flags(self.x);
            }
            (DEY, Implicit) => {
                self.y = self.y.wrapping_sub(1);
                self.p.set_zn_flags(self.y);
            }
            (LDA, mode) => {
                self.a = self.read_operand(&mode);
                self.p.set_zn_flags(self.a);
            }
            (LDX, mode) => {
                self.x = self.read_operand(&mode);
                self.p.set_zn_flags(self.x);
            }
            (LDY, mode) => {
                self.y = self.read_operand(&mode);
                self.p.set_zn_flags(self.y);
            }
            (LSR, mode) => {
                let data = self.read_operand(&mode);
                self.p.set(Status::C, data & 1 != 0);
                let x = data.wrapping_shr(1);
                self.p.set_zn_flags(x);
                self.write_operand(mode, x);
            }
            (ORA, mode) => {
                let data = self.read_operand(&mode);
                self.a |= data;
                self.p.set_zn_flags(self.a);
            }
            (ROL, mode) => {
                let data = self.read_operand(&mode);
                self.p.set(Status::C, (data >> 7) & 1 != 0);
                let x = data.rotate_left(1);
                self.p.set_zn_flags(x);
                self.write_operand(mode, x);
            }
            (ROR, mode) => {
                let data = self.read_operand(&mode);
                self.p.set(Status::C, data & 1 != 0);
                let x = data.rotate_right(1);
                self.p.set_zn_flags(x);
                self.write_operand(mode, x);
            }
            (SEC, Implicit) => {
                self.p.set(Status::C, true);
            }
            (SED, Implicit) => {
                self.p.set(Status::D, true);
            }
            (SEI, Implicit) => {
                self.p.set(Status::I, true);
            }
            (STA, mode) => self.write_operand(mode, self.a),
            (SBC, mode) => {
                let data = self.read_operand(&mode);
                let (x, o) = self.a.overflowing_sub(data);
                self.a = x;
                self.p.set(Status::C, o);
                self.p.set_zn_flags(self.a);
            }
            (INC, mode) => {
                let data = self.read_operand(&mode);
                let x = data.wrapping_add(1);
                self.p.set_zn_flags(x);
                self.write_operand(mode, x);
            }
            (NOP, Implicit) => {}
            (INX, Implicit) => {
                self.x = self.x.wrapping_add(1);
                self.p.set_zn_flags(self.x);
            }
            (INY, Implicit) => {
                self.y = self.y.wrapping_add(1);
                self.p.set_zn_flags(self.y);
            }
            (TAX, Implicit) => {
                self.x = self.a;
                self.p.set_zn_flags(self.x);
            }
            (TAY, Implicit) => {
                self.y = self.a;
                self.p.set_zn_flags(self.y);
            }
            (TXA, Implicit) => {
                self.a = self.x;
                self.p.set_zn_flags(self.a);
            }
            (TYA, Implicit) => {
                self.a = self.y;
                self.p.set_zn_flags(self.a);
            }
            (Illegal(opcode), _) => panic!("illegal opcode: 0x{:02X}", opcode),
            // programming error
            inst => unreachable!("unhandled instruction: {:?}", inst),
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

    fn program(bytes: &[u8]) -> CPU {
        CPU::new(Memory::from(bytes))
    }

    #[test]
    fn test_0x00_brk() {
        // TODO
    }

    #[test]
    fn test_0x06_asl_zpg() {
        let mut cpu = program(&[0x06, 0x20]);
        cpu.wram.write_u8(0x20, 0b0000_0001);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b0000_0010);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x06_asl_zpg_zero_flag() {
        let mut cpu = program(&[0x06, 0x20]);
        cpu.tick();
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0x06_asl_zpg_negative_flag() {
        let mut cpu = program(&[0x06, 0x20]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.tick();
        // multiplies by 2
        assert_eq!(cpu.wram.read_u8(0x20), 0x80);
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x06_asl_zpg_carry_flag() {
        let mut cpu = program(&[0x06, 0x20]);
        cpu.wram.write_u8(0x20, 0b1000_0000);
        cpu.tick();
        assert!(cpu.p.contains(Status::C));
    }

    #[test]
    fn test_0x0a_asl_acc() {
        let mut cpu = program(&[0x0A]);
        cpu.a = 0b0000_0001;
        cpu.tick();
        assert_eq!(cpu.a, 0b0000_0010);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x0a_asl_acc_zero_flag() {
        let mut cpu = program(&[0x0A]);
        cpu.a = 0;
        cpu.tick();
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0x0a_asl_acc_negative_flag() {
        let mut cpu = program(&[0x0A]);
        cpu.a = 0x40;
        cpu.tick();
        assert_eq!(cpu.a, 0x80);
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x0a_asl_acc_carry_flag() {
        let mut cpu = program(&[0x0A]);
        cpu.a = 0b1000_0000;
        cpu.tick();
        assert!(cpu.p.contains(Status::C));
    }

    #[test]
    fn test_0x16_asl_zpgx() {
        let mut cpu = program(&[0x16, 0x10]);
        cpu.x = 0x10;
        cpu.wram.write_u8(0x20, 0b0000_0001);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b0000_0010);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x16_asl_zpgx_zero_flag() {
        let mut cpu = program(&[0x16, 0x20]);
        cpu.x = 0;
        cpu.wram.write_u8(0x20, 0);
        cpu.tick();
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0x16_asl_zpgx_negative_flag() {
        let mut cpu = program(&[0x16, 0x20]);
        cpu.x = 0;
        cpu.wram.write_u8(0x20, 0x40);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0x80);
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x16_asl_zpgx_carry_flag() {
        let mut cpu = program(&[0x16, 0x20]);
        cpu.x = 0;
        cpu.wram.write_u8(0x20, 0b1000_0000);
        cpu.tick();
        assert!(cpu.p.contains(Status::C));
    }

    #[test]
    fn test_0x4a_lsr_acc() {
        let mut cpu = program(&[0x4A]);
        cpu.a = 0b0000_0010;
        cpu.tick();
        assert_eq!(cpu.a, 0b0000_0001);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x4a_lsr_acc_zero_flag() {
        let mut cpu = program(&[0x4A]);
        cpu.a = 0;
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0x4a_lsr_acc_negative_flag() {
        let mut cpu = program(&[0x4A]);
        cpu.a = 0xFF;
        cpu.tick();
        assert_eq!(cpu.a, 0x7F);
        // its impossible for the N flag to be set, shifting right guarantees
        // that there will be no 1 bit set bit in 7.
        // 0b1111_1111 (0xFF) >> 1 == 0b0111_1111 (0x7F)
        assert!(!cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x4a_lsr_acc_carry_flag() {
        let mut cpu = program(&[0x4A]);
        cpu.a = 0b0000_0011;
        cpu.tick();
        assert_eq!(cpu.p, Status::C);
    }

    #[test]
    fn test_0x46_lsr_zpg() {
        let mut cpu = program(&[0x46, 0x20]);
        cpu.wram.write_u8(0x20, 0b0000_0010);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b0000_0001);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x46_lsr_zpg_zero_flag() {
        let mut cpu = program(&[0x46, 0x20]);
        cpu.wram.write_u8(0x20, 0);
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0x46_lsr_zpg_negative_flag() {
        let mut cpu = program(&[0x46, 0x20]);
        cpu.wram.write_u8(0x20, 0xFF);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0x7F);
        assert!(!cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x46_lsr_zpg_carry_flag() {
        let mut cpu = program(&[0x46, 0x20]);
        cpu.wram.write_u8(0x20, 0b0000_0011);
        cpu.tick();
        assert_eq!(cpu.p, Status::C);
    }

    #[test]
    fn test_0x56_lsr_zpgx() {
        let mut cpu = program(&[0x56, 0x10]);
        cpu.wram.write_u8(0x20, 0b0000_0010);
        cpu.x = 0x10;
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b0000_0001);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x56_lsr_zpgx_zero_flag() {
        let mut cpu = program(&[0x56, 0x20]);
        cpu.wram.write_u8(0x20, 0);
        cpu.x = 0;
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0x56_lsr_zpgx_negative_flag() {
        let mut cpu = program(&[0x56, 0x20]);
        cpu.wram.write_u8(0x20, 0xFF);
        cpu.x = 0;
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0x7F);
        assert!(!cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x56_lsr_zpgx_carry_flag() {
        let mut cpu = program(&[0x56, 0x20]);
        cpu.wram.write_u8(0x20, 0b0000_0011);
        cpu.x = 0;
        cpu.tick();
        assert_eq!(cpu.p, Status::C);
    }

    #[test]
    fn test_0x18_clc() {
        let mut cpu = program(&[0x18]);
        cpu.p.set(Status::C, true);
        cpu.tick();
        assert_eq!(cpu.p.contains(Status::C), false);
    }

    #[test]
    fn test_0xd8_cld() {
        let mut cpu = program(&[0xD8]);
        cpu.p.set(Status::D, true);
        cpu.tick();
        assert_eq!(cpu.p.contains(Status::D), false);
    }

    #[test]
    fn test_0x58_cli() {
        let mut cpu = program(&[0x58]);
        cpu.p.set(Status::I, true);
        cpu.tick();
        assert_eq!(cpu.p.contains(Status::I), false);
    }

    #[test]
    fn test_0xb8_clv() {
        let mut cpu = program(&[0xB8]);
        cpu.p.set(Status::V, true);
        cpu.tick();
        assert_eq!(cpu.p.contains(Status::V), false);
    }

    #[test]
    fn test_0x25_and_zpg() {
        let mut cpu = program(&[0x25, 0x20]);
        cpu.wram.write_u8(0x20, 0b1010);
        cpu.a = 0b1111;
        cpu.tick();
        assert_eq!(cpu.a, 0b1010);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x25_and_zpg_zero_flag() {
        let mut cpu = program(&[0x25, 0]);
        cpu.a = 0;
        cpu.tick();
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0x25_and_zpg_negative_flag() {
        let mut cpu = program(&[0x25, 0x20]);
        cpu.wram.write_u8(0x20, 0xFF);
        cpu.a = 0x80;
        cpu.tick();
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x29_and_imm() {
        let mut cpu = program(&[0x29, 0b1010]);
        cpu.a = 0b1111;
        cpu.tick();
        assert_eq!(cpu.a, 0b1010);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x29_and_imm_zero_flag() {
        let mut cpu = program(&[0x29, 0]);
        cpu.a = 0;
        cpu.tick();
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0x29_and_imm_negative_flag() {
        let mut cpu = program(&[0x29, 0xFF]);
        cpu.a = 0x80;
        cpu.tick();
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x35_and_zpgx() {
        let mut cpu = program(&[0x35, 0x10]);
        cpu.wram.write_u8(0x20, 0b1010);
        cpu.x = 0x10;
        cpu.a = 0b1111;
        cpu.tick();
        assert_eq!(cpu.a, 0b1010);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x35_and_zpgx_zero_flag() {
        let mut cpu = program(&[0x35, 0x20]);
        cpu.wram.write_u8(0x20, 0);
        cpu.x = 0;
        cpu.a = 0;
        cpu.tick();
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0x35_and_zpgx_negative_flag() {
        let mut cpu = program(&[0x35, 0x20]);
        cpu.wram.write_u8(0x20, 0xFF);
        cpu.x = 0;
        cpu.a = 0x80;
        cpu.tick();
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x09_ora_imm() {
        let mut cpu = program(&[0x09, 0b0101_0101]);
        cpu.a = 0b0000_1111;
        cpu.tick();
        assert_eq!(cpu.a, 0b0101_1111);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x09_ora_imm_zero_flag() {
        let mut cpu = program(&[0x09, 0x00]);
        cpu.a = 0x00;
        cpu.tick();
        assert_eq!(cpu.a, 0x00);
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0x09_ora_imm_negative_flag() {
        let mut cpu = program(&[0x09, 0x00]);
        cpu.a = 0x80;
        cpu.tick();
        assert_eq!(cpu.a, 0x80);
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0x05_ora_zpg() {
        let mut cpu = program(&[0x05, 0x20]);
        cpu.wram.write_u8(0x20, 0b0101_0101);
        cpu.a = 0b0000_1111;
        cpu.tick();
        assert_eq!(cpu.a, 0b0101_1111);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x05_ora_zpg_zero_flag() {
        let mut cpu = program(&[0x05, 0x20]);
        cpu.wram.write_u8(0x20, 0x00);
        cpu.a = 0x00;
        cpu.tick();
        assert_eq!(cpu.a, 0x00);
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0x05_ora_zpg_negative_flag() {
        let mut cpu = program(&[0x05, 0x20]);
        cpu.wram.write_u8(0x20, 0x00);
        cpu.a = 0x80;
        cpu.tick();
        assert_eq!(cpu.a, 0x80);
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0x15_ora_zpgx() {
        let mut cpu = program(&[0x15, 0x10]);
        cpu.wram.write_u8(0x20, 0b0101_0101);
        cpu.x = 0x10;
        cpu.a = 0b0000_1111;
        cpu.tick();
        assert_eq!(cpu.a, 0b0101_1111);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x15_ora_zpgx_zero_flag() {
        let mut cpu = program(&[0x15, 0x20]);
        cpu.wram.write_u8(0x20, 0x00);
        cpu.x = 0x00;
        cpu.a = 0x00;
        cpu.tick();
        assert_eq!(cpu.a, 0x00);
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0x15_ora_zpgx_negative_flag() {
        let mut cpu = program(&[0x15, 0x20]);
        cpu.wram.write_u8(0x20, 0x00);
        cpu.x = 0x00;
        cpu.a = 0x80;
        cpu.tick();
        assert_eq!(cpu.a, 0x80);
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0x2a_rol_acc() {
        let mut cpu = program(&[0x2A]);
        cpu.a = 0b0000_1010;
        cpu.tick();
        assert_eq!(cpu.a, 0b0001_0100);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x2a_rol_acc_zero_flag() {
        let mut cpu = program(&[0x2A]);
        cpu.a = 0x00;
        cpu.tick();
        assert_eq!(cpu.a, 0x00);
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0x2a_rol_acc_negative_flag() {
        let mut cpu = program(&[0x2A]);
        cpu.a = 0b0101_0101;
        cpu.tick();
        assert_eq!(cpu.a, 0b1010_1010);
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0x2a_rol_acc_carry_flag() {
        let mut cpu = program(&[0x2A, 0x2A]);
        cpu.a = 0b1010_1010;
        cpu.tick();
        assert_eq!(cpu.a, 0b0101_0101);
        assert_eq!(cpu.p, Status::C);
        // flag cleared on second tick
        cpu.tick();
        assert_eq!(cpu.a, 0b1010_1010);
        assert!(!cpu.p.contains(Status::C));
    }

    #[test]
    fn test_0x26_rol_zpg() {
        let mut cpu = program(&[0x26, 0x20]);
        cpu.wram.write_u8(0x20, 0b0000_1010);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b0001_0100);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x26_rol_zpg_zero_flag() {
        let mut cpu = program(&[0x26, 0x20]);
        cpu.wram.write_u8(0x20, 0x00);
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0x26_rol_zpg_negative_flag() {
        let mut cpu = program(&[0x26, 0x20]);
        cpu.wram.write_u8(0x20, 0b0101_0101);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b1010_1010);
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0x26_rol_zpg_carry_flag() {
        let mut cpu = program(&[0x26, 0x20, 0x26, 0x20]);
        cpu.wram.write_u8(0x20, 0b1010_1010);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b0101_0101);
        assert_eq!(cpu.p, Status::C);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b1010_1010);
        assert!(!cpu.p.contains(Status::C));
    }

    #[test]
    fn test_0x36_rol_zpgx() {
        let mut cpu = program(&[0x36, 0x10]);
        cpu.wram.write_u8(0x20, 0b0000_1010);
        cpu.x = 0x10;
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b0001_0100);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x36_rol_zpgx_zero_flag() {
        let mut cpu = program(&[0x36, 0x20]);
        cpu.wram.write_u8(0x20, 0x00);
        cpu.x = 0x00;
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0x36_rol_zpgx_negative_flag() {
        let mut cpu = program(&[0x36, 0x20]);
        cpu.wram.write_u8(0x20, 0b0101_0101);
        cpu.x = 0x00;
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b1010_1010);
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0x36_rol_zpgx_carry_flag() {
        let mut cpu = program(&[0x36, 0x10, 0x36, 0x10]);
        cpu.wram.write_u8(0x20, 0b1010_1010);
        cpu.x = 0x10;
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b0101_0101);
        assert_eq!(cpu.p, Status::C);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b1010_1010);
        assert!(!cpu.p.contains(Status::C));
    }

    #[test]
    fn test_0x6a_ror_acc() {
        let mut cpu = program(&[0x6A]);
        cpu.a = 0b1010_1010;
        cpu.tick();
        assert_eq!(cpu.a, 0b0101_0101);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x6a_ror_acc_zero_flag() {
        let mut cpu = program(&[0x6A]);
        cpu.a = 0x00;
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0x6a_ror_acc_negative_flag() {
        let mut cpu = program(&[0x6A]);
        cpu.a = 0b0000_0001;
        cpu.tick();
        assert_eq!(cpu.a, 0b1000_0000);
        // will also contain C
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x6a_ror_acc_carry_flag() {
        let mut cpu = program(&[0x6A, 0x6A]);
        cpu.a = 0b0101_0101;
        cpu.tick();
        assert_eq!(cpu.a, 0b1010_1010);
        // will also contain N
        assert!(cpu.p.contains(Status::C));
        cpu.tick();
        assert_eq!(cpu.a, 0b0101_0101);
        assert!(!cpu.p.contains(Status::C));
    }

    #[test]
    fn test_0x66_ror_zpg() {
        let mut cpu = program(&[0x66, 0x20]);
        cpu.wram.write_u8(0x20, 0b1010_1010);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b0101_0101);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x66_ror_zpg_zero_flag() {
        let mut cpu = program(&[0x66, 0x20]);
        cpu.wram.write_u8(0x20, 0x00);
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0x66_ror_zpg_negative_flag() {
        let mut cpu = program(&[0x66, 0x20]);
        cpu.wram.write_u8(0x20, 0b0000_0001);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b1000_0000);
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x66_ror_zpg_carry_flag() {
        let mut cpu = program(&[0x66, 0x20, 0x66, 0x20]);
        cpu.wram.write_u8(0x20, 0b0101_0101);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b1010_1010);
        assert!(cpu.p.contains(Status::C));
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b0101_0101);
        assert!(!cpu.p.contains(Status::C));
    }

    #[test]
    fn test_0x76_ror_zpgx() {
        let mut cpu = program(&[0x76, 0x10]);
        cpu.wram.write_u8(0x20, 0b1010_1010);
        cpu.x = 0x10;
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b0101_0101);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x76_ror_zpgx_zero_flag() {
        let mut cpu = program(&[0x76, 0x20]);
        cpu.wram.write_u8(0x20, 0x00);
        cpu.x = 0x00;
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0x00);
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0x76_ror_zpgx_negative_flag() {
        let mut cpu = program(&[0x76, 0x20]);
        cpu.wram.write_u8(0x20, 0b0000_0001);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b1000_0000);
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x76_ror_zpgx_carry_flag() {
        let mut cpu = program(&[0x76, 0x10, 0x76, 0x10]);
        cpu.wram.write_u8(0x20, 0b0101_0101);
        cpu.x = 0x10;
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b1010_1010);
        assert!(cpu.p.contains(Status::C));
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0b0101_0101);
        assert!(!cpu.p.contains(Status::C));
    }

    #[test]
    fn test_0xa9_lda_imm() {
        let mut cpu = program(&[0xA9, 0x40]);
        cpu.tick();
        assert_eq!(cpu.a, 0x40);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xa9_lda_imm_zero_flag() {
        let mut cpu = program(&[0xA9, 0x00]);
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0xa9_lda_imm_negative_flag() {
        let mut cpu = program(&[0xA9, 0x80]);
        cpu.tick();
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0xa5_lda_zpg() {
        let mut cpu = program(&[0xA5, 0x20]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.tick();
        assert_eq!(cpu.a, 0x40);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xa5_lda_zpg_zero_flag() {
        let mut cpu = program(&[0xA5, 0x20]);
        cpu.wram.write_u8(0x20, 0);
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0xa5_lda_zpg_negative_flag() {
        let mut cpu = program(&[0xA5, 0x20]);
        cpu.wram.write_u8(0x20, 0x80);
        cpu.tick();
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0xb5_lda_zpgx() {
        let mut cpu = program(&[0xB5, 0x10]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.x = 0x10;
        cpu.tick();
        assert_eq!(cpu.a, 0x40);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xb5_lda_zpgx_zero_flag() {
        let mut cpu = program(&[0xB5, 0x20]);
        cpu.wram.write_u8(0x20, 0);
        cpu.x = 0;
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0xb5_lda_zpgx_negative_flag() {
        let mut cpu = program(&[0xB5, 0x20]);
        cpu.wram.write_u8(0x20, 0x80);
        cpu.x = 0;
        cpu.tick();
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0x85_sta_zpg() {
        let mut cpu = program(&[0x85, 0x20]);
        cpu.a = 0xFF;
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0xFF);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x95_sta_zpgx() {
        let mut cpu = program(&[0x95, 0x10]);
        cpu.x = 0x10;
        cpu.a = 0xFF;
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0xFF);
    }

    /// creates a program that checks the behaviour of a branch operation
    /// when its condition is false.
    ///
    /// if run correctly the program will set the accumulator to 0xFF.
    fn branch_no_skip(opcode: u8) -> [u8; 5] {
        [
            opcode, 0x02,
            0xA9,   0xFF,
            0x00, // unreachable
        ]
    }

    /// creates a program that checks that branching works with positive
    /// offsets.
    ///
    /// if run correctly the program will increment the Y register.
    fn branch_offset(opcode: u8) -> [u8; 5] {
        [
            opcode, 0x02,
            0x00,   0x00, // unreachable
            0xC8,         // INY
        ]
    }

    /// creates a program that checks that branching works with negative
    /// offsets.
    ///
    /// if run correctly the program will increment (with INY) the Y register
    /// twice, once when run normally and again when the program jumps back to
    /// the INY instruction.
    fn branch_negative_offset(opcode: u8) -> [u8; 4] {
        [
            0xC8,         // INY,
            opcode, 0xFD, // jump to start (-3)
            0x00,
        ]
    }

    #[test]
    fn test_0x90_bcc_no_skip() {
        let mut cpu = program(&branch_no_skip(0x90));
        cpu.p.set(Status::C, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_0x90_bcc_offset() {
        let mut cpu = program(&branch_offset(0x90));
        cpu.p.set(Status::C, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 1);
    }

    #[test]
    fn test_0x90_bcc_negative_offset() {
        let mut cpu = program(&branch_negative_offset(0x90));
        cpu.tick();
        cpu.p.set(Status::C, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 2);
    }

    #[test]
    fn test_0xb0_bcs_no_skip() {
        let mut cpu = program(&branch_no_skip(0xB0));
        cpu.p.set(Status::C, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_0xb0_bcs_offset() {
        let mut cpu = program(&branch_offset(0xB0));
        cpu.p.set(Status::C, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 1);
    }

    #[test]
    fn test_0xb0_bcs_negative_offset() {
        let mut cpu = program(&branch_negative_offset(0xB0));
        cpu.tick();
        cpu.p.set(Status::C, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 2);
    }

    #[test]
    fn test_0xf0_beq_no_skip() {
        let mut cpu = program(&branch_no_skip(0xF0));
        cpu.p.set(Status::Z, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_0xf0_beq_offset() {
        let mut cpu = program(&branch_offset(0xF0));
        cpu.p.set(Status::Z, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 1);
    }

    #[test]
    fn test_0xf0_beq_negative_offset() {
        let mut cpu = program(&branch_negative_offset(0xF0));
        cpu.tick();
        cpu.p.set(Status::Z, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 2);
    }

    #[test]
    fn test_0x30_bmi_no_skip() {
        let mut cpu = program(&branch_no_skip(0x30));
        cpu.p.set(Status::N, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_0x30_bmi_offset() {
        let mut cpu = program(&branch_offset(0x30));
        cpu.p.set(Status::N, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 1);
    }

    #[test]
    fn test_0x30_bmi_negative_offset() {
        let mut cpu = program(&branch_negative_offset(0x30));
        cpu.tick();
        cpu.p.set(Status::N, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 2);
    }

    #[test]
    fn test_0xd0_bne_no_skip() {
        let mut cpu = program(&branch_no_skip(0xD0));
        cpu.p.set(Status::Z, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_0xd0_bne_offset() {
        let mut cpu = program(&branch_offset(0xD0));
        cpu.p.set(Status::Z, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 1);
    }

    #[test]
    fn test_0xd0_bne_negative_offset() {
        let mut cpu = program(&branch_negative_offset(0xD0));
        cpu.tick();
        cpu.p.set(Status::Z, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 2);
    }

    #[test]
    fn test_0x10_bpl_no_skip() {
        let mut cpu = program(&branch_no_skip(0x10));
        cpu.p.set(Status::N, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_0x10_bpl_offset() {
        let mut cpu = program(&branch_offset(0x10));
        cpu.p.set(Status::N, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 1);
    }

    #[test]
    fn test_0x10_bpl_negative_offset() {
        let mut cpu = program(&branch_negative_offset(0x10));
        cpu.tick();
        cpu.p.set(Status::N, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 2);
    }

    #[test]
    fn test_0x50_bvc_no_skip() {
        let mut cpu = program(&branch_no_skip(0x50));
        cpu.p.set(Status::V, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_0x50_bvc_offset() {
        let mut cpu = program(&branch_offset(0x50));
        cpu.p.set(Status::V, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 1);
    }

    #[test]
    fn test_0x50_bvc_negative_offset() {
        let mut cpu = program(&branch_negative_offset(0x50));
        cpu.tick();
        cpu.p.set(Status::V, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 2);
    }

    #[test]
    fn test_0x70_bvs_no_skip() {
        let mut cpu = program(&branch_no_skip(0x70));
        cpu.p.set(Status::V, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_0x70_bvs_offset() {
        let mut cpu = program(&branch_offset(0x70));
        cpu.p.set(Status::V, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 1);
    }

    #[test]
    fn test_0x70_bvs_negative_offset() {
        let mut cpu = program(&branch_negative_offset(0x70));
        cpu.tick();
        cpu.p.set(Status::V, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 2);
    }

    #[test]
    fn test_0x69_adc_imm() {
        let mut cpu = program(&[0x69, 0x40]);
        cpu.a = 0x04;
        cpu.tick();
        assert_eq!(cpu.a, 0x44);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x69_adc_imm_zero_flag() {
        let mut cpu = program(&[0x69, 0x0]);
        cpu.a = 0;
        cpu.tick();
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0x69_adc_imm_negative_flag() {
        let mut cpu = program(&[0x69, 0x01]);
        cpu.a = 0x7F;
        cpu.tick();
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x69_adc_imm_carry_flag() {
        let mut cpu = program(&[0x69, 0x01]);
        cpu.a = 0xFF;
        cpu.tick();
        assert!(cpu.p.contains(Status::C));
    }

    #[test]
    fn test_0x65_adc_zpg() {
        let mut cpu = program(&[0x65, 0x20]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.a = 0x04;
        cpu.tick();
        assert_eq!(cpu.a, 0x44);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x65_adc_zpg_zero_flag() {
        let mut cpu = program(&[0x65, 0x20]);
        cpu.a = 0;
        cpu.tick();
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0x65_adc_zpg_negative_flag() {
        let mut cpu = program(&[0x65, 0x20]);
        cpu.wram.write_u8(0x20, 1);
        cpu.a = 0x7F;
        cpu.tick();
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x65_adc_zpg_carry_flag() {
        let mut cpu = program(&[0x65, 0x20]);
        cpu.wram.write_u8(0x20, 1);
        cpu.a = 0xFF;
        cpu.tick();
        assert!(cpu.p.contains(Status::C));
    }

    #[test]
    fn test_0x75_adc_zpgx() {
        let mut cpu = program(&[0x75, 0x10]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.x = 0x10;
        cpu.a = 0x04;
        cpu.tick();
        assert_eq!(cpu.a, 0x44);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xe9_sbc_imm() {
        let mut cpu = program(&[0xE9, 0x20]);
        cpu.a = 0x40;
        cpu.tick();
        assert_eq!(cpu.a, 0x20);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xe6_inc_zpg() {
        let mut cpu = program(&[0xE6, 0x20]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0x41);
    }

    #[test]
    fn test_0xe6_inc_zpg_zero_flag() {
        let mut cpu = program(&[0xE6, 0x20]);
        cpu.wram.write_u8(0x20, 0xFF);
        cpu.tick();
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0xe6_inc_zpg_negative_flag() {
        let mut cpu = program(&[0xE6, 0x20]);
        cpu.wram.write_u8(0x20, 0x7F);
        cpu.tick();
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0xf6_inc_zpgx() {
        let mut cpu = program(&[0xF6, 0x10]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.x = 0x10;
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0x41);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xf6_inc_zpgx_zero_flag() {
        let mut cpu = program(&[0xF6, 0x20]);
        cpu.wram.write_u8(0x20, 0xFF);
        cpu.x = 0;
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0xf6_zpgx_negative_flag() {
        let mut cpu = program(&[0xF6, 0x20]);
        cpu.wram.write_u8(0x20, 0x7F);
        cpu.x = 0;
        cpu.tick();
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0xa2_ldx_imm() {
        let mut cpu = program(&[0xA2, 0x40]);
        cpu.tick();
        assert_eq!(cpu.x, 0x40);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xa2_ldx_imm_zero_flag() {
        let mut cpu = program(&[0xA2, 0]);
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0xa2_ldx_imm_negative_flag() {
        let mut cpu = program(&[0xA2, 0x80]);
        cpu.tick();
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0xa6_ldx_zpg() {
        let mut cpu = program(&[0xA6, 0x20]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.tick();
        assert_eq!(cpu.x, 0x40);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xa6_ldx_zpg_zero_flag() {
        let mut cpu = program(&[0xA6, 0x20]);
        cpu.wram.write_u8(0x20, 0);
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0xa6_ldx_zpg_negative_flag() {
        let mut cpu = program(&[0xA6, 0x20]);
        cpu.wram.write_u8(0x20, 0x80);
        cpu.tick();
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0xb6_ldx_zpgy() {
        let mut cpu = program(&[0xB6, 0x10]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.y = 0x10;
        cpu.tick();
        assert_eq!(cpu.x, 0x40);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xb6_ldx_zpgy_zero_flag() {
        let mut cpu = program(&[0xB6, 0x20]);
        cpu.wram.write_u8(0x20, 0);
        cpu.y = 0;
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0xb6_ldx_zpgy_negative_flag() {
        let mut cpu = program(&[0xB6, 0x20]);
        cpu.wram.write_u8(0x20, 0x80);
        cpu.y = 0;
        cpu.tick();
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0xa0_ldy_imm() {
        let mut cpu = program(&[0xA0, 0x40]);
        cpu.tick();
        assert_eq!(cpu.y, 0x40);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xa0_ldy_imm_zero_flag() {
        let mut cpu = program(&[0xA0, 0x00]);
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0xa0_ldy_imm_negative_flag() {
        let mut cpu = program(&[0xA0, 0x80]);
        cpu.tick();
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0xa4_ldy_zpg() {
        let mut cpu = program(&[0xA4, 0x20]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.tick();
        assert_eq!(cpu.y, 0x40);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xa4_ldy_zpg_zero_flag() {
        let mut cpu = program(&[0xA4, 0x20]);
        cpu.wram.write_u8(0x20, 0);
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0xa4_ldy_zpg_negative_flag() {
        let mut cpu = program(&[0xA4, 0x20]);
        cpu.wram.write_u8(0x20, 0x80);
        cpu.tick();
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0xb4_ldy_zpgx() {
        let mut cpu = program(&[0xB4, 0x10]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.x = 0x10;
        cpu.tick();
        assert_eq!(cpu.y, 0x40);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xb4_ldy_zpgx_zero_flag() {
        let mut cpu = program(&[0xB4, 0x20]);
        cpu.wram.write_u8(0x20, 0);
        cpu.x = 0;
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0xb4_ldy_zpgx_negative_flag() {
        let mut cpu = program(&[0xB4, 0x20]);
        cpu.wram.write_u8(0x20, 0x80);
        cpu.x = 0;
        cpu.tick();
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0xe8_inx() {
        let mut cpu = program(&[0xE8]);
        cpu.x = 0x40;
        cpu.tick();
        assert_eq!(cpu.x, 0x41);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xe8_inx_zero_flag() {
        let mut cpu = program(&[0xE8]);
        cpu.x = 0xFF;
        cpu.tick();
        assert_eq!(cpu.x, 0);
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0xe8_inx_negative_flag() {
        let mut cpu = program(&[0xE8]);
        cpu.x = 0x7F;
        cpu.tick();
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0xc8_iny() {
        let mut cpu = program(&[0xC8]);
        cpu.y = 0x40;
        cpu.tick();
        assert_eq!(cpu.y, 0x41);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xc8_iny_zero_flag() {
        let mut cpu = program(&[0xC8]);
        cpu.y = 0xFF;
        cpu.tick();
        assert_eq!(cpu.y, 0);
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0xc8_iny_negative_flag() {
        let mut cpu = program(&[0xC8]);
        cpu.y = 0x7F;
        cpu.tick();
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0xc6_dec_zpg() {
        let mut cpu = program(&[0xC6, 0x20]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0x3F);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xc6_dec_zpg_zero_flag() {
        let mut cpu = program(&[0xC6, 0x20]);
        cpu.wram.write_u8(0x20, 0x01);
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0xc6_dec_zpg_negative_flag() {
        let mut cpu = program(&[0xC6, 0x20]);
        cpu.wram.write_u8(0x20, 0x00);
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0xFF);
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0xd6_dec_zpgx() {
        let mut cpu = program(&[0xD6, 0x10]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.x = 0x10;
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0x3F);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xd6_dec_zpgx_zero_flag() {
        let mut cpu = program(&[0xD6, 0x20]);
        cpu.wram.write_u8(0x20, 0x01);
        cpu.x = 0;
        cpu.tick();
        assert_eq!(cpu.p, Status::Z);
    }

    #[test]
    fn test_0xd6_dec_zpgx_negative_flag() {
        let mut cpu = program(&[0xD6, 0x20]);
        cpu.wram.write_u8(0x20, 0x00);
        cpu.x = 0;
        cpu.tick();
        assert_eq!(cpu.wram.read_u8(0x20), 0xFF);
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0xca_dex() {
        let mut cpu = program(&[0xCA]);
        cpu.x = 2;
        cpu.tick();
        assert_eq!(cpu.x, 1);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xca_dex_underflow() {
        let mut cpu = program(&[0xCA]);
        cpu.x = 0;
        cpu.tick();
        assert_eq!(cpu.x, 0xFF);
    }

    #[test]
    fn test_0xca_dex_zero_flag() {
        let mut cpu = program(&[0xCA]);
        cpu.x = 1;
        cpu.tick();
        assert_eq!(cpu.x, 0);
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0xca_dex_negative_flag() {
        let mut cpu = program(&[0xCA]);
        cpu.x = 0xFF;
        cpu.tick();
        assert_eq!(cpu.x, 0xFE);
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x88_dey() {
        let mut cpu = program(&[0x88]);
        cpu.y = 2;
        cpu.tick();
        assert_eq!(cpu.y, 1);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x88_dey_underflow() {
        let mut cpu = program(&[0x88]);
        cpu.y = 0;
        cpu.tick();
        assert_eq!(cpu.y, 0xFF);
    }

    #[test]
    fn test_0x88_dey_zero_flag() {
        let mut cpu = program(&[0x88]);
        cpu.y = 1;
        cpu.tick();
        assert_eq!(cpu.y, 0);
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0x88_dey_negative_flag() {
        let mut cpu = program(&[0x88]);
        cpu.y = 0xFF;
        cpu.tick();
        assert_eq!(cpu.y, 0xFE);
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0xea_nop() {
        let mut cpu = program(&[0xEA]);
        cpu.tick();
        // as long as we don't panic, we're good
    }

    #[test]
    fn test_0x38_sec() {
        let mut cpu = program(&[0x38]);
        cpu.p.set(Status::C, false);
        cpu.tick();
        assert!(cpu.p.contains(Status::C));
    }

    #[test]
    fn test_0xf8_sed() {
        let mut cpu = program(&[0xF8]);
        cpu.p.set(Status::D, false);
        cpu.tick();
        assert!(cpu.p.contains(Status::D));
    }

    #[test]
    fn test_0x78_sei() {
        let mut cpu = program(&[0x78]);
        cpu.p.set(Status::I, false);
        cpu.tick();
        assert!(cpu.p.contains(Status::I));
    }

    #[test]
    fn test_0xaa_tax() {
        let mut cpu = program(&[0xAA]);
        cpu.x = 0x00;
        cpu.a = 0x40;
        cpu.tick();
        assert_eq!(cpu.x, 0x40);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xaa_tax_zero_flag() {
        let mut cpu = program(&[0xAA]);
        cpu.x = 0x40;
        cpu.a = 0x00;
        cpu.tick();
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0xaa_tax_negative_flag() {
        let mut cpu = program(&[0xAA]);
        cpu.x = 0x00;
        cpu.a = 0x80;
        cpu.tick();
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0xa8_tay() {
        let mut cpu = program(&[0xA8]);
        cpu.y = 0x00;
        cpu.a = 0x40;
        cpu.tick();
        assert_eq!(cpu.y, 0x40);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xa8_tay_zero_flag() {
        let mut cpu = program(&[0xA8]);
        cpu.y = 0x40;
        cpu.a = 0x00;
        cpu.tick();
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0xa8_tay_negative_flag() {
        let mut cpu = program(&[0xA8]);
        cpu.y = 0x00;
        cpu.a = 0x80;
        cpu.tick();
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x8a_txa() {
        let mut cpu = program(&[0x8A]);
        cpu.a = 0x00;
        cpu.x = 0x40;
        cpu.tick();
        assert_eq!(cpu.a, 0x40);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x8a_txa_zero_flag() {
        let mut cpu = program(&[0x8A]);
        cpu.a = 0x40;
        cpu.x = 0x00;
        cpu.tick();
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0x8a_txa_negative_flag() {
        let mut cpu = program(&[0x8A]);
        cpu.a = 0x00;
        cpu.x = 0x80;
        cpu.tick();
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0x98_txa() {
        let mut cpu = program(&[0x98]);
        cpu.a = 0x00;
        cpu.y = 0x40;
        cpu.tick();
        assert_eq!(cpu.a, 0x40);
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0x98_txa_zero_flag() {
        let mut cpu = program(&[0x98]);
        cpu.a = 0x40;
        cpu.y = 0x00;
        cpu.tick();
        assert!(cpu.p.contains(Status::Z));
    }

    #[test]
    fn test_0x98_txa_negative_flag() {
        let mut cpu = program(&[0x98]);
        cpu.a = 0x00;
        cpu.y = 0x80;
        cpu.tick();
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_0xc9_cmp_imm_eq() {
        let mut cpu = program(&[0xC9, 0x40]);
        cpu.a = 0x40;
        cpu.tick();
        assert_eq!(cpu.p, Status::C | Status::Z)
    }

    #[test]
    fn test_0xc9_cmp_imm_gt() {
        let mut cpu = program(&[0xC9, 0x40]);
        cpu.a = 0x41;
        cpu.tick();
        assert_eq!(cpu.p, Status::C);
    }

    #[test]
    fn test_0xc9_cmp_imm_lt() {
        let mut cpu = program(&[0xC9, 0x41]);
        cpu.a = 0x40;
        cpu.tick();
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xc9_cmp_imm_negative_flag() {
        let mut cpu = program(&[0xC9, 0xFF]);
        cpu.a = 0x80;
        cpu.tick();
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0xc5_cmp_zpg_eq() {
        let mut cpu = program(&[0xC5, 0x20]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.a = 0x40;
        cpu.tick();
        assert_eq!(cpu.p, Status::C | Status::Z);
    }

    #[test]
    fn test_0xc5_cmp_zpg_gt() {
        let mut cpu = program(&[0xC5, 0x20]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.a = 0x41;
        cpu.tick();
        assert_eq!(cpu.p, Status::C);
    }

    #[test]
    fn test_0xc5_cmp_zpg_lt() {
        let mut cpu = program(&[0xC5, 0x20]);
        cpu.wram.write_u8(0x20, 0x41);
        cpu.a = 0x40;
        cpu.tick();
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xc5_cmp_zpg_negative_flag() {
        let mut cpu = program(&[0xC5, 0x20]);
        cpu.wram.write_u8(0x20, 0xFF);
        cpu.a = 0x80;
        cpu.tick();
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0xd5_cmp_zpgx_eq() {
        let mut cpu = program(&[0xD5, 0x10]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.x = 0x10;
        cpu.a = 0x40;
        cpu.tick();
        assert_eq!(cpu.p, Status::C | Status::Z);
    }

    #[test]
    fn test_0xd5_cmp_zpgx_gt() {
        let mut cpu = program(&[0xD5, 0x10]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.x = 0x10;
        cpu.a = 0x41;
        cpu.tick();
        assert_eq!(cpu.p, Status::C);
    }

    #[test]
    fn test_0xd5_cmp_zpgx_lt() {
        let mut cpu = program(&[0xD5, 0x10]);
        cpu.wram.write_u8(0x20, 0x41);
        cpu.x = 0x10;
        cpu.a = 0x40;
        cpu.tick();
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xd5_cmp_zpgx_negative_flag() {
        let mut cpu = program(&[0xD5, 0x10]);
        cpu.wram.write_u8(0x20, 0xFF);
        cpu.x = 0x10;
        cpu.a = 0x80;
        cpu.tick();
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0xe0_cpx_imm_eq() {
        let mut cpu = program(&[0xE0, 0x40]);
        cpu.x = 0x40;
        cpu.tick();
        assert_eq!(cpu.p, Status::C | Status::Z);
    }

    #[test]
    fn test_0xe0_cpx_imm_gt() {
        let mut cpu = program(&[0xE0, 0x40]);
        cpu.x = 0x41;
        cpu.tick();
        assert_eq!(cpu.p, Status::C);
    }

    #[test]
    fn test_0xe0_cpx_imm_lt() {
        let mut cpu = program(&[0xE0, 0x41]);
        cpu.x = 0x40;
        cpu.tick();
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xe0_cpx_imm_negative_flag() {
        let mut cpu = program(&[0xE0, 0xFF]);
        cpu.x = 0x80;
        cpu.tick();
        assert_eq!(cpu.p, Status::N);
    }

    #[test]
    fn test_0xe4_cpx_zpg_eq() {
        let mut cpu = program(&[0xE4, 0x20]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.x = 0x40;
        cpu.tick();
        assert_eq!(cpu.p, Status::C | Status::Z);
    }

    #[test]
    fn test_0xe4_cpx_zpg_gt() {
        let mut cpu = program(&[0xE4, 0x20]);
        cpu.wram.write_u8(0x20, 0x40);
        cpu.x = 0x41;
        cpu.tick();
        assert_eq!(cpu.p, Status::C);
    }

    #[test]
    fn test_0xe4_cpx_zpg_lt() {
        let mut cpu = program(&[0xE4, 0x20]);
        cpu.wram.write_u8(0x20, 0x41);
        cpu.x = 0x40;
        cpu.tick();
        assert!(cpu.p.is_empty());
    }

    #[test]
    fn test_0xe4_cpx_zpg_negative_flag() {
        let mut cpu = program(&[0xE4, 0x20]);
        cpu.wram.write_u8(0x20, 0xFF);
        cpu.x = 0x80;
        cpu.tick();
        assert_eq!(cpu.p, Status::N);
    }
}
