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
#[derive(Clone, Copy, Debug)]
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

    fn push_stack(&mut self, val: u8) {
        // FIXME: stack isn't stored in wram
        self.wram.write_u8(self.sp as u16, val);
        self.sp = self.sp.wrapping_sub(1);
    }

    fn pop_stack(&mut self) -> u8 {
        self.sp = self.sp.wrapping_add(1);
        self.wram.read_u8(self.sp as u16)
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
            // conversion from u8 to i8 uses the same schemantics as the CPU
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
            0xC0 => (CPY, Immediate(self.fetch())),
            0xC4 => (CPY, ZeroPage(self.fetch())),
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
                let result = data.wrapping_shl(1);
                self.p.set_zn_flags(result);
                self.write_operand(mode, result);
            }
            (AND, mode) => {
                let data = self.read_operand(&mode);
                self.a &= data;
                self.p.set_zn_flags(self.a);
            }
            (ADC, mode) => {
                let data = self.read_operand(&mode);
                let (result, o) = self.a.overflowing_add(data);
                self.a = result;
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
            (CPY, mode) => {
                let data = self.read_operand(&mode);
                self.p.set(Status::C, self.y >= data);
                self.p.set(Status::Z, self.y == data);
                self.p.set_n_flag(self.y);
            }
            (DEC, mode) => {
                let data = self.read_operand(&mode);
                let result = data.wrapping_sub(1);
                self.p.set_zn_flags(result);
                self.write_operand(mode, result);
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
                let result = data.wrapping_shr(1);
                self.p.set_zn_flags(result);
                self.write_operand(mode, result);
            }
            (ORA, mode) => {
                let data = self.read_operand(&mode);
                self.a |= data;
                self.p.set_zn_flags(self.a);
            }
            (ROL, mode) => {
                let data = self.read_operand(&mode);
                self.p.set(Status::C, (data >> 7) & 1 != 0);
                let result = data.rotate_left(1);
                self.p.set_zn_flags(result);
                self.write_operand(mode, result);
            }
            (ROR, mode) => {
                let data = self.read_operand(&mode);
                self.p.set(Status::C, data & 1 != 0);
                let result = data.rotate_right(1);
                self.p.set_zn_flags(result);
                self.write_operand(mode, result);
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
                let carry = !self.p.contains(Status::C) as u8;
                let (result, o1) = self.a.overflowing_sub(data);
                let (result, o2) = result.overflowing_sub(carry);
                self.a = result;
                self.p.set(Status::C, o1 || o2);
                self.p.set_zn_flags(self.a);
            }
            (INC, mode) => {
                let data = self.read_operand(&mode);
                let result = data.wrapping_add(1);
                self.p.set_zn_flags(result);
                self.write_operand(mode, result);
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
    use super::AddressingMode::*;

    fn program(bytes: &[u8]) -> CPU {
        CPU::new(Memory::from(bytes))
    }

    fn program_with_mode(opcode: u8, mode: AddressingMode) -> CPU {
        let bytes = match mode {
            Implicit | Accumulator => vec![opcode],
            Immediate(val)
            | ZeroPage(val)
            | ZeroPageX(val)
            | ZeroPageY(val) => vec![opcode, val],
            _ => todo!("mode {:?}", mode)
        };
        program(&bytes)
    }

    // required for stringify!
    impl std::fmt::Display for Status {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{:?}", self)
        }
    }

    // modified version of https://github.com/starrhorne/nes-rust/blob/master/src/cpu_test.rs#L63
    macro_rules! test_op {
        ($inst:expr, $mode:expr, [$($b:expr),*]{$($sk:ident : $sv:expr),*} => [$($rb:expr),*]{$($ek:ident : $ev:expr),*}) => {
            {
                let mut cpu = program_with_mode($inst, $mode);
                let mut mem: Vec<u8> = Vec::new();
                $(mem.push($b);)*
                cpu.wram.load(&mem, 0);
                $(cpu.$sk = $sv;)*
                cpu.tick();
                $(
                    assert!(
                        cpu.$ek == $ev,
                        "Incorrect register. Expected cpu.{} to be {}, got {}",
                        stringify!($ek),
                        stringify!($ev),
                        cpu.$ek
                    );
                )*
                let mut mem = Vec::new();
                $(mem.push($rb);)*
                for (i, &b) in mem.iter().enumerate() {
                    assert!(
                        cpu.wram.read_u8(i as u16) == b,
                        "Incorrect memory. Expected wram[{}] to be {}, got {}",
                        i, b, cpu.wram.read_u8(i as u16)
                    );
                }
                cpu
            }
        }
    }

    #[test]
    fn test_brk() {
        // TODO
    }

    #[test]
    fn test_asl() {
        // 0b01 << 1 == 0b10
        test_op!(0x0A, Accumulator, []{ a: 0x01 } => []{ a: 0x02, p: Status::empty() });
        test_op!(0x06, ZeroPage(0), [0x01]{} => [0x02]{ p: Status::empty() });
        test_op!(0x16, ZeroPageX(0), [0, 0x01]{ x: 1 } => [0, 0x02]{ p: Status::empty() });

        // negative flag
        test_op!(0x0A, Accumulator, []{ a: 0x40 } => []{ a: 0x80, p: Status::N });
        test_op!(0x06, ZeroPage(0), [0x40]{} => [0x80]{ p: Status::N });
        test_op!(0x16, ZeroPageX(0), [0, 0x40]{ x: 1 } => [0, 0x80]{ p: Status::N });

        // carry & zero flag
        // 0b1000_0000 (0x80) << 1 == 0
        test_op!(0x0A, Accumulator, []{ a: 0x80 } => []{ a: 0, p: Status::C | Status::Z });
        test_op!(0x06, ZeroPage(0), [0x80]{} => [0]{ p: Status::C | Status::Z });
        test_op!(0x16, ZeroPageX(0), [0, 0x80]{ x: 1 } => [0, 0]{ p: Status::C | Status::Z });
    }

    #[test]
    fn test_rol() {
        let cpu = test_op!(0x2A, Accumulator, []{ a: 0b0000_1010 } => []{ a: 0b0001_0100 });
        assert!(cpu.p.is_empty());
        let cpu = test_op!(0x26, ZeroPage(0), [0b0000_1010]{} => [0b0001_0100]{});
        assert!(cpu.p.is_empty());
        let cpu = test_op!(0x36, ZeroPageX(0), [0, 0b0000_1010]{ x: 1 } => [0, 0b0001_0100]{});
        assert!(cpu.p.is_empty());

        // negative flag
        let cpu = test_op!(0x2A, Accumulator, []{ a: 0b0101_0101 } => []{ a: 0b1010_1010 });
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0x26, ZeroPage(0), [0b0101_0101]{} => [0b1010_1010]{});
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0x36, ZeroPageX(0), [0, 0b0101_0101]{ x: 1 } => [0, 0b1010_1010]{});
        assert!(cpu.p.contains(Status::N));

        // zero flag
        let cpu = test_op!(0x2A, Accumulator, []{ a: 0 } => []{ a: 0 });
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0x26, ZeroPage(0), [0]{} => [0]{});
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0x36, ZeroPageX(0), [0, 0]{} => [0, 0]{});
        assert!(cpu.p.contains(Status::Z));

        // carry flag
        test_op!(0x2A, Accumulator, []{ a: 0b1010_1010 } => []{ a: 0b0101_0101, p: Status::C });
        test_op!(0x26, ZeroPage(0), [0b1010_1010]{} => [0b0101_0101]{ p: Status::C });
        test_op!(0x36, ZeroPageX(0), [0, 0b1010_1010]{ x: 1 } => [0, 0b0101_0101]{ p: Status::C });
    }

    #[test]
    fn test_ror() {
        let cpu = test_op!(0x6A, Accumulator, []{ a: 0b1010_1010 } => []{ a: 0b0101_0101 });
        assert!(cpu.p.is_empty());
        let cpu = test_op!(0x66, ZeroPage(0), [0b1010_1010]{} => [0b0101_0101]{});
        assert!(cpu.p.is_empty());
        let cpu = test_op!(0x76, ZeroPageX(0), [0, 0b1010_1010]{ x: 1 } => [0, 0b0101_0101]{});
        assert!(cpu.p.is_empty());

        // negative flag
        let cpu = test_op!(0x6A, Accumulator, []{ a: 0b0000_0001 } => []{ a: 0b1000_0000 });
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0x66, ZeroPage(0), [0b0000_0001]{} => [0b1000_0000]{});
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0x76, ZeroPageX(0), [0, 0b0000_0001]{ x: 1 } => [0, 0b1000_0000]{});
        assert!(cpu.p.contains(Status::N));

        // zero flag
        let cpu = test_op!(0x6A, Accumulator, []{ a: 0 } => []{ a: 0 });
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0x66, ZeroPage(0), [0]{ } => [0]{});
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0x76, ZeroPageX(0), [0, 0]{ x: 1 } => [0, 0]{});
        assert!(cpu.p.contains(Status::Z));

        // carry flag
        let cpu = test_op!(0x6A, Accumulator, []{ a: 0b0101_0101 } => []{ a: 0b1010_1010 });
        assert!(cpu.p.contains(Status::C));
        let cpu = test_op!(0x66, ZeroPage(0), [0b0101_0101]{} => [0b1010_1010]{});
        assert!(cpu.p.contains(Status::C));
        let cpu = test_op!(0x76, ZeroPageX(0), [0, 0b0101_0101]{ x: 1 } => [0, 0b1010_1010]{});
        assert!(cpu.p.contains(Status::C));
    }

    #[test]
    fn test_ora() {
        let cpu = test_op!(0x09, Immediate(0b0101_0101), []{ a: 0b0000_1111 } => []{ a: 0b0101_1111 });
        assert!(cpu.p.is_empty());
        let cpu = test_op!(0x05, ZeroPage(0), [0b0101_0101]{ a: 0b0000_1111 } => []{ a: 0b0101_1111 });
        assert!(cpu.p.is_empty());
        let cpu = test_op!(0x15, ZeroPageX(0), [0, 0b0101_0101]{ x: 1, a: 0b0000_1111 } => []{ a: 0b0101_1111 });
        assert!(cpu.p.is_empty());

        // zero flag
        let cpu = test_op!(0x09, Immediate(0), []{ a: 0 } => []{ a: 0 });
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0x05, ZeroPage(0), [0]{ a: 0 } => []{ a: 0 });
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0x15, ZeroPageX(0), [0, 0]{ a: 0 } => []{ a: 0 });
        assert!(cpu.p.contains(Status::Z));

        // negative flag
        let cpu = test_op!(0x09, Immediate(0), []{ a: 0x80 } => []{ a: 0x80 });
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0x05, ZeroPage(0), [0]{ a: 0x80 } => []{ a: 0x80 });
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0x15, ZeroPageX(0), [0, 0]{ a: 0x80 } => []{ a: 0x80 });
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_adc() {
        let cpu = test_op!(0x69, Immediate(0x40), []{ a: 0x04 } => []{ a: 0x44 });
        assert!(cpu.p.is_empty());
        let cpu = test_op!(0x65, ZeroPage(0), [0x40]{ a: 0x04 } => []{ a: 0x44 });
        assert!(cpu.p.is_empty());
        let cpu = test_op!(0x75, ZeroPageX(0), [0, 0x40]{ x: 1, a: 0x04 } => []{ a: 0x44 });
        assert!(cpu.p.is_empty());

        // zero flag
        let cpu = test_op!(0x69, Immediate(0), []{ a: 0 } => []{ a: 0 });
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0x65, ZeroPage(0), [0]{} => []{ a: 0 });
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0x75, ZeroPageX(0), [0, 0]{ x: 1 } => []{ a: 0 });
        assert!(cpu.p.contains(Status::Z));

        // negative flag
        let cpu = test_op!(0x69, Immediate(0x01), []{ a: 0x7F } => []{ a: 0x80 });
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0x65, ZeroPage(0), [0x01]{ a: 0x7F } => []{ a: 0x80 });
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0x75, ZeroPageX(0), [0, 0x01]{ x: 1, a: 0x7F } => []{ a: 0x80 });
        assert!(cpu.p.contains(Status::N));

        // carry flag
        let cpu = test_op!(0x69, Immediate(0x01), []{ a: 0xFF } => []{ a: 0 });
        assert!(cpu.p.contains(Status::C));
        let cpu = test_op!(0x65, ZeroPage(0), [0x01]{ a: 0xFF } => []{ a: 0 });
        assert!(cpu.p.contains(Status::C));
        let cpu = test_op!(0x75, ZeroPageX(0), [0, 0x01]{ x: 1, a: 0xFF } => []{ a: 0 });
        assert!(cpu.p.contains(Status::C));
    }

    #[test]
    fn test_sbc() {
        test_op!(0xE9, Immediate(0x20), []{ a: 0x40, p: Status::C } => []{ a: 0x20, p: Status::empty() });
        test_op!(0xE5, ZeroPage(0), [0x20]{ a: 0x40, p: Status::C } => []{ a: 0x20, p: Status::empty() });
        test_op!(0xF5, ZeroPageX(0), [0, 0x20]{ x: 1, a: 0x40, p: Status::C } => []{ a: 0x20, p: Status::empty() });
        // zero flag
        test_op!(0xE9, Immediate(0), []{ a: 0, p: Status::C } => []{ a: 0, p: Status::Z });
        test_op!(0xE5, ZeroPage(0), [0]{ a: 0, p: Status::C } => []{ a: 0, p: Status::Z });
        test_op!(0xF5, ZeroPageX(0), [0, 0]{ x: 1, a: 0, p: Status::C } => []{ a: 0, p: Status::Z });
        // negative flag
        let cpu = test_op!(0xE9, Immediate(1), []{ a: 0, p: Status::C } => []{ a: 0xFF });
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0xE5, ZeroPage(0), [1]{ a: 0, p: Status::C } => []{ a: 0xFF });
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0xF5, ZeroPageX(0), [0, 1]{ x: 1, a: 0, p: Status::C } => []{ a: 0xFF });
        assert!(cpu.p.contains(Status::N));
        // carry flag
        test_op!(0xE9, Immediate(2), []{ a: 10, p: Status::C } => []{ a: 8 });
        test_op!(0xE9, Immediate(2), []{ a: 10, p: Status::empty() } => []{ a: 7 });
        test_op!(0xE5, ZeroPage(0), [2]{ a: 10, p: Status::C } => []{ a: 8 });
        test_op!(0xE5, ZeroPage(0), [2]{ a: 10, p: Status::empty() } => []{ a: 7 });
        test_op!(0xF5, ZeroPageX(0), [0, 2]{ x: 1, a: 10, p: Status::C } => []{ a: 8 });
        test_op!(0xF5, ZeroPageX(0), [0, 2]{ x: 1, a: 10, p: Status::empty() } => []{ a: 7 });
        // TODO: overflow
    }

    #[test]
    fn test_and() {
        let cpu = test_op!(0x29, Immediate(0b1010), []{ a: 0b1111 } => []{ a: 0b1010 });
        assert!(cpu.p.is_empty());
        let cpu = test_op!(0x25, ZeroPage(0), [0b1010]{ a: 0b1111 } => []{ a: 0b1010 });
        assert!(cpu.p.is_empty());
        let cpu = test_op!(0x35, ZeroPageX(0), [0, 0b1010]{ x: 1, a: 0b1111 } => []{ a: 0b1010 });
        assert!(cpu.p.is_empty());

        // zero flag
        let cpu = test_op!(0x29, Immediate(0), []{ a: 0 } => []{ a: 0 });
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0x25, ZeroPage(0), [0]{ a: 0 } => []{ a: 0 });
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0x35, ZeroPageX(0), [0, 0]{ x: 1, a: 0 } => []{ a: 0 });
        assert!(cpu.p.contains(Status::Z));

        // negative flag
        let cpu = test_op!(0x29, Immediate(0xFF), []{ a: 0x80 } => []{ a: 0x80 });
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0x25, ZeroPage(0), [0xFF]{ a: 0x80 } => []{ a: 0x80 });
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0x35, ZeroPageX(0), [0, 0xFF]{ x: 1, a: 0x80 } => []{ a: 0x80 });
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_lda() {
        let cpu = test_op!(0xA9, Immediate(0x40), []{} => []{ a: 0x40 });
        assert!(cpu.p.is_empty());
        let cpu = test_op!(0xA5, ZeroPage(0), [0x40]{} => []{ a: 0x40 });
        assert!(cpu.p.is_empty());
        let cpu = test_op!(0xB5, ZeroPageX(0), [0, 0x40]{ x: 1 } => []{ a: 0x40 });
        assert!(cpu.p.is_empty());

        // zero flag
        let cpu = test_op!(0xA9, Immediate(0), []{} => []{ a: 0 });
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0xA5, ZeroPage(0), [0]{} => []{ a: 0 });
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0xB5, ZeroPageX(0), [0, 0]{ x: 1 } => []{ a: 0 });
        assert!(cpu.p.contains(Status::Z));

        // negative flag
        let cpu = test_op!(0xA9, Immediate(0xFF), []{} => []{ a: 0xFF });
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0xA5, ZeroPage(0), [0xFF]{} => []{ a: 0xFF });
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0xB5, ZeroPageX(0), [0, 0xFF]{ x: 1 } => []{ a: 0xFF });
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_ldx() {
        let cpu = test_op!(0xA2, Immediate(0x40), []{} => []{ x: 0x40 });
        assert!(cpu.p.is_empty());
        let cpu = test_op!(0xA6, ZeroPage(0), [0x40]{} => []{ x: 0x40 });
        assert!(cpu.p.is_empty());
        let cpu = test_op!(0xB6, ZeroPageY(0), [0, 0x40]{ y: 1 } => []{ x: 0x40 });
        assert!(cpu.p.is_empty());

        // zero flag
        let cpu = test_op!(0xA2, Immediate(0), []{} => []{ x: 0 });
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0xA6, ZeroPage(0), [0]{} => []{ x: 0 });
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0xB6, ZeroPageY(0), [0, 0]{ y: 1 } => []{ x: 0 });
        assert!(cpu.p.contains(Status::Z));

        // negative flag
        let cpu = test_op!(0xA2, Immediate(0x80), []{} => []{ x: 0x80 });
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0xA6, ZeroPage(0), [0x80]{} => []{ x: 0x80 });
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0xB6, ZeroPageY(0), [0, 0x80]{ y: 1 } => []{ x: 0x80 });
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_ldy() {
        let cpu = test_op!(0xA0, Immediate(0x40), []{} => []{ y: 0x40 });
        assert!(cpu.p.is_empty());
        let cpu = test_op!(0xA4, ZeroPage(0), [0x40]{} => []{ y: 0x40 });
        assert!(cpu.p.is_empty());
        let cpu = test_op!(0xB4, ZeroPageX(0), [0, 0x40]{ x: 1 } => []{ y: 0x40 });
        assert!(cpu.p.is_empty());

        // zero flag
        let cpu = test_op!(0xA0, Immediate(0), []{} => []{ y: 0 });
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0xA4, ZeroPage(0), [0]{} => []{ y: 0 });
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0xA4, ZeroPageX(0), [0, 0]{ x: 1 } => []{ y: 0 });
        assert!(cpu.p.contains(Status::Z));

        // negative flag
        let cpu = test_op!(0xA0, Immediate(0x80), []{} => []{ y: 0x80 });
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0xA4, ZeroPage(0), [0x80]{} => []{ y: 0x80 });
        assert!(cpu.p.contains(Status::N));
        let cpu = test_op!(0xB4, ZeroPageX(0), [0, 0x80]{ x: 1 } => []{ y: 0x80 });
        assert!(cpu.p.contains(Status::N));
    }

    #[test]
    fn test_dec() {
        test_op!(0xC6, ZeroPage(0), [0x40]{} => [0x3F]{ p: Status::empty() });
        test_op!(0xD6, ZeroPageX(0), [0, 0x40]{ x: 1 } => [0, 0x3F]{ p: Status::empty() });

        // negative flag
        test_op!(0xC6, ZeroPage(0), [0x00]{} => [0xFF]{ p: Status::N });
        test_op!(0xD6, ZeroPageX(0), [0, 0x00]{ x: 1 } => [0, 0xFF]{ p: Status::N });

        // zero flag
        test_op!(0xC6, ZeroPage(0), [0x01]{} => [0x00]{ p: Status::Z });
        test_op!(0xD6, ZeroPageX(0), [0, 0x01]{ x: 1 } => [0, 0x00]{ p: Status::Z });
    }

    #[test]
    fn test_dex() {
        test_op!(0xCA, Implicit, []{ x: 2 } => []{ x: 1, p: Status::empty() });
        // underflow & negative flag
        test_op!(0xCA, Implicit, []{ x: 0 } => []{ x: 0xFF, p: Status::N });
        // zero flag
        test_op!(0xCA, Implicit, []{ x: 1 } => []{ x: 0, p: Status::Z });
    }

    #[test]
    fn test_dey() {
        test_op!(0x88, Implicit, []{ y: 2 } => []{ y: 1, p: Status::empty() });
        // underflow & negative flag
        test_op!(0x88, Implicit, []{ y: 0 } => []{ y: 0xFF, p: Status::N });
        // zero flag
        test_op!(0x88, Implicit, []{ y: 1 } => []{ y: 0, p: Status::Z });
    }

    #[test]
    fn test_inc() {
        test_op!(0xE6, ZeroPage(0), [0x40]{} => [0x41]{});
        test_op!(0xF6, ZeroPageX(0), [0, 0x40]{ x: 1 } => [0, 0x41]{});

        // negative flag
        test_op!(0xE6, ZeroPage(0), [0x7F]{} => [0x80]{ p: Status::N });
        test_op!(0xF6, ZeroPageX(0), [0, 0x7F]{ x: 1 } => [0, 0x80]{ p: Status::N });

        // zero flag
        test_op!(0xE6, ZeroPage(0), [0xFF]{} => [0x00]{ p: Status::Z });
        test_op!(0xF6, ZeroPageX(0), [0, 0xFF]{ x: 1 } => [0, 0x00]{ p: Status::Z });
    }

    #[test]
    fn test_inx() {
        test_op!(0xE8, Implicit, []{ x: 0x40 } => []{ x: 0x41, p: Status::empty() });
        // overflow & zero flag
        test_op!(0xE8, Implicit, []{ x: 0xFF } => []{ x: 0, p: Status::Z });
        // negative flag
        test_op!(0xE8, Implicit, []{ x: 0x7F } => []{ x: 0x80, p: Status::N });
    }

    #[test]
    fn test_iny() {
        test_op!(0xC8, Implicit, []{ y: 0x40 } => []{ y: 0x41, p: Status::empty() });
        // overflow & zero flag
        test_op!(0xC8, Implicit, []{ y: 0xFF } => []{ y: 0, p: Status::Z });
        // negative flag
        test_op!(0xC8, Implicit, []{ y: 0x7F } => []{ y: 0x80, p: Status::N });
    }

    #[test]
    fn test_lsr() {
        test_op!(0x4A, Accumulator, []{ a: 0b10 } => []{ a: 0b01, p: Status::empty() });
        test_op!(0x46, ZeroPage(0), [0b10]{} => [0b01]{ p: Status::empty() });
        test_op!(0x56, ZeroPageX(0), [0, 0b10]{ x: 1 } => [0, 0b01]{ p: Status::empty() });

        // carry flag
        test_op!(0x4A, Accumulator, []{ a: 0b11 } => []{ a: 0b01, p: Status::C });
        test_op!(0x46, ZeroPage(0), [0b11]{} => [0b01]{ p: Status::C });
        test_op!(0x56, ZeroPageX(0), [0, 0b11]{ x: 1 } => [0, 0b01]{ p: Status::C });

        // zero flag
        let cpu = test_op!(0x4A, Accumulator, []{ a: 0b01 } => []{ a: 0b00});
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0x46, ZeroPage(0), [0b01]{} => [0b00]{});
        assert!(cpu.p.contains(Status::Z));
        let cpu = test_op!(0x56, ZeroPageX(0), [0, 0b01]{ x: 1 } => [0, 0b00]{});
        assert!(cpu.p.contains(Status::Z));

        // its impossible for the N flag to be set, shifting right guarantees
        // that there will be no 1 bit set bit in 7.
        // 0b1111_1111 (0xFF) >> 1 == 0b0111_1111 (0x7F)
        test_op!(0x4A, Accumulator, []{ a: 0xFF } => []{ a: 0x7F });
        test_op!(0x46, ZeroPage(0), [0xFF]{} => [0x7F]{});
        test_op!(0x56, ZeroPageX(0), [0, 0xFF]{ x: 1 } => [0, 0x7F]{});
    }

    #[test]
    fn test_tax() {
        test_op!(0xAA, Implicit, []{ a: 0x40 } => []{ x: 0x40, p: Status::empty() });
        // zero flag
        test_op!(0xAA, Implicit, []{ x: 0x40 } => []{ x: 0, p: Status::Z });
        // negative flag
        test_op!(0xAA, Implicit, []{ a: 0x80 } => []{ a: 0x80, p: Status::N });
    }

    #[test]
    fn test_tay() {
        test_op!(0xA8, Implicit, []{ a: 0x40 } => []{ y: 0x40, p: Status::empty() });
        // zero flag
        test_op!(0xA8, Implicit, []{ y: 0x40 } => []{ y: 0, p: Status::Z });
        // negative flag
        test_op!(0xA8, Implicit, []{ a: 0x80 } => []{ y: 0x80, p: Status::N });
    }

    #[test]
    fn test_txa() {
        test_op!(0x8A, Implicit, []{ x: 0x40 } => []{ a: 0x40, p: Status::empty() });
        // zero flag
        test_op!(0x8A, Implicit, []{ a: 0x40 } => []{ x: 0, p: Status::Z });
        // negative flag
        test_op!(0x8A, Implicit, []{ x: 0x80 } => []{ a: 0x80, p: Status::N });
    }

    #[test]
    fn test_tya() {
        test_op!(0x98, Implicit, []{ y: 0x40 } => []{ a: 0x40, p: Status::empty() });
        // zero flag
        test_op!(0x98, Implicit, []{ a: 0x40 } => []{ y: 0, p: Status::Z });
        // negative flag
        test_op!(0x98, Implicit, []{ y: 0x80 } => []{ a: 0x80, p: Status::N });
    }

    #[test]
    fn test_sta() {
        test_op!(0x85, ZeroPage(0), []{ a: 0xFF } => [0xFF]{ p: Status::empty() });
        test_op!(0x95, ZeroPageX(0), []{ a: 0xFF, x: 1 } => [0, 0xFF]{ p: Status::empty() });
    }

    #[test]
    fn test_cmp() {
        // a == b
        test_op!(0xC9, Immediate(0x40), []{ a: 0x40 } => []{ p: Status::C | Status::Z });
        test_op!(0xC5, ZeroPage(0), [0x40]{ a: 0x40 } => []{ p: Status::C | Status::Z });
        test_op!(0xD5, ZeroPageX(0), [0, 0x40]{ a: 0x40, x: 1 } => []{ p: Status::C | Status::Z });
        // a > b
        test_op!(0xC9, Immediate(0x40), []{ a: 0x41 } => []{ p: Status::C });
        test_op!(0xC5, ZeroPage(0), [0x40]{ a: 0x41 } => []{ p: Status::C });
        test_op!(0xD5, ZeroPageX(0), [0, 0x40]{ a: 0x41, x: 1 } => []{ p: Status::C });
        // a < b
        test_op!(0xC9, Immediate(0x41), []{ a: 0x40 } => []{ p: Status::empty() });
        test_op!(0xC5, ZeroPage(0), [0x41]{ a: 0x40 } => []{ p: Status::empty() });
        test_op!(0xD5, ZeroPageX(0), [0, 0x41]{ a: 0x40, x: 1 } => []{ p: Status::empty() });
        // negative flag
        test_op!(0xC9, Immediate(0xFF), []{ a: 0x80 } => []{ p: Status::N });
        test_op!(0xC5, ZeroPage(0), [0xFF]{ a: 0x80 } => []{ p: Status::N });
        test_op!(0xD5, ZeroPageX(0), [0, 0xFF]{ a: 0x80, x: 1 } => []{ p: Status::N });
    }

    #[test]
    fn test_cpx() {
        // a == b
        test_op!(0xE0, Immediate(0x40), []{ x: 0x40 } => []{ p: Status::C | Status::Z });
        test_op!(0xE4, ZeroPage(0), [0x40]{ x: 0x40 } => []{ p: Status::C | Status::Z });
        // a > b
        test_op!(0xE0, Immediate(0x40), []{ x: 0x41 } => []{ p: Status::C });
        test_op!(0xE4, ZeroPage(0), [0x40]{ x: 0x41 } => []{ p: Status::C });
        // a < b
        test_op!(0xE0, Immediate(0x41), []{ x: 0x40 } => []{ p: Status::empty() });
        test_op!(0xE4, ZeroPage(0), [0x41]{ x: 0x40 } => []{ p: Status::empty() });
        // negative flag
        test_op!(0xE0, Immediate(0xFF), []{ x: 0x80 } => []{ p: Status::N });
        test_op!(0xE4, ZeroPage(0), [0xFF]{ x: 0x80 } => []{ p: Status::N });
    }

    #[test]
    fn test_cpy() {
        // a == b
        test_op!(0xC0, Immediate(0x40), []{ y: 0x40 } => []{ p: Status::C | Status::Z });
        test_op!(0xC4, ZeroPage(0), [0x40]{ y: 0x40 } => []{ p: Status::C | Status::Z });
        // a > b
        test_op!(0xC0, Immediate(0x40), []{ y: 0x41 } => []{ p: Status::C });
        test_op!(0xC4, ZeroPage(0), [0x40]{ y: 0x41 } => []{ p: Status::C });
        // a < b
        test_op!(0xC0, Immediate(0x41), []{ y: 0x40 } => []{ p: Status::empty() });
        test_op!(0xC4, ZeroPage(0), [0x41]{ y: 0x40 } => []{ p: Status::empty() });
        // negative flag
        test_op!(0xC0, Immediate(0xFF), []{ y: 0x80 } => []{ p: Status::N });
        test_op!(0xC4, ZeroPage(0), [0xFF]{ y: 0x80 } => []{ p: Status::N });
    }

    #[test]
    fn test_clc() {
        let mut cpu = program(&[0x18]);
        cpu.p.set(Status::C, true);
        cpu.tick();
        assert_eq!(cpu.p.contains(Status::C), false);
    }

    #[test]
    fn test_cld() {
        let mut cpu = program(&[0xD8]);
        cpu.p.set(Status::D, true);
        cpu.tick();
        assert_eq!(cpu.p.contains(Status::D), false);
    }

    #[test]
    fn test_cli() {
        let mut cpu = program(&[0x58]);
        cpu.p.set(Status::I, true);
        cpu.tick();
        assert_eq!(cpu.p.contains(Status::I), false);
    }

    #[test]
    fn test_clv() {
        let mut cpu = program(&[0xB8]);
        cpu.p.set(Status::V, true);
        cpu.tick();
        assert_eq!(cpu.p.contains(Status::V), false);
    }

    #[test]
    fn test_nop() {
        let mut cpu = program(&[0xEA]);
        cpu.tick();
        // as long as we don't panic, we're good
    }

    #[test]
    fn test_sec() {
        let mut cpu = program(&[0x38]);
        cpu.p.set(Status::C, false);
        cpu.tick();
        assert!(cpu.p.contains(Status::C));
    }

    #[test]
    fn test_sed() {
        let mut cpu = program(&[0xF8]);
        cpu.p.set(Status::D, false);
        cpu.tick();
        assert!(cpu.p.contains(Status::D));
    }

    #[test]
    fn test_sei() {
        let mut cpu = program(&[0x78]);
        cpu.p.set(Status::I, false);
        cpu.tick();
        assert!(cpu.p.contains(Status::I));
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
    fn test_bcc_no_skip() {
        let mut cpu = program(&branch_no_skip(0x90));
        cpu.p.set(Status::C, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_bcc_offset() {
        let mut cpu = program(&branch_offset(0x90));
        cpu.p.set(Status::C, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 1);
    }

    #[test]
    fn test_bcc_negative_offset() {
        let mut cpu = program(&branch_negative_offset(0x90));
        cpu.tick();
        cpu.p.set(Status::C, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 2);
    }

    #[test]
    fn test_bcs_no_skip() {
        let mut cpu = program(&branch_no_skip(0xB0));
        cpu.p.set(Status::C, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_bcs_offset() {
        let mut cpu = program(&branch_offset(0xB0));
        cpu.p.set(Status::C, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 1);
    }

    #[test]
    fn test_bcs_negative_offset() {
        let mut cpu = program(&branch_negative_offset(0xB0));
        cpu.tick();
        cpu.p.set(Status::C, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 2);
    }

    #[test]
    fn test_beq_no_skip() {
        let mut cpu = program(&branch_no_skip(0xF0));
        cpu.p.set(Status::Z, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_beq_offset() {
        let mut cpu = program(&branch_offset(0xF0));
        cpu.p.set(Status::Z, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 1);
    }

    #[test]
    fn test_beq_negative_offset() {
        let mut cpu = program(&branch_negative_offset(0xF0));
        cpu.tick();
        cpu.p.set(Status::Z, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 2);
    }

    #[test]
    fn test_bmi_no_skip() {
        let mut cpu = program(&branch_no_skip(0x30));
        cpu.p.set(Status::N, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_bmi_offset() {
        let mut cpu = program(&branch_offset(0x30));
        cpu.p.set(Status::N, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 1);
    }

    #[test]
    fn test_bmi_negative_offset() {
        let mut cpu = program(&branch_negative_offset(0x30));
        cpu.tick();
        cpu.p.set(Status::N, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 2);
    }

    #[test]
    fn test_bne_no_skip() {
        let mut cpu = program(&branch_no_skip(0xD0));
        cpu.p.set(Status::Z, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_bne_offset() {
        let mut cpu = program(&branch_offset(0xD0));
        cpu.p.set(Status::Z, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 1);
    }

    #[test]
    fn test_bne_negative_offset() {
        let mut cpu = program(&branch_negative_offset(0xD0));
        cpu.tick();
        cpu.p.set(Status::Z, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 2);
    }

    #[test]
    fn test_bpl_no_skip() {
        let mut cpu = program(&branch_no_skip(0x10));
        cpu.p.set(Status::N, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_bpl_offset() {
        let mut cpu = program(&branch_offset(0x10));
        cpu.p.set(Status::N, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 1);
    }

    #[test]
    fn test_bpl_negative_offset() {
        let mut cpu = program(&branch_negative_offset(0x10));
        cpu.tick();
        cpu.p.set(Status::N, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 2);
    }

    #[test]
    fn test_bvc_no_skip() {
        let mut cpu = program(&branch_no_skip(0x50));
        cpu.p.set(Status::V, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_bvc_offset() {
        let mut cpu = program(&branch_offset(0x50));
        cpu.p.set(Status::V, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 1);
    }

    #[test]
    fn test_bvc_negative_offset() {
        let mut cpu = program(&branch_negative_offset(0x50));
        cpu.tick();
        cpu.p.set(Status::V, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 2);
    }

    #[test]
    fn test_bvs_no_skip() {
        let mut cpu = program(&branch_no_skip(0x70));
        cpu.p.set(Status::V, false);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_bvs_offset() {
        let mut cpu = program(&branch_offset(0x70));
        cpu.p.set(Status::V, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 1);
    }

    #[test]
    fn test_bvs_negative_offset() {
        let mut cpu = program(&branch_negative_offset(0x70));
        cpu.tick();
        cpu.p.set(Status::V, true);
        cpu.tick();
        cpu.tick();
        assert_eq!(cpu.y, 2);
    }
}
