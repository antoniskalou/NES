// 2KB CPU RAM
const MEMORY_SIZE: usize = 0x0800;

#[derive(Debug)]
pub struct Memory([u8; MEMORY_SIZE]);

impl Memory {
    pub fn new() -> Self {
        Memory([0; MEMORY_SIZE])
    }

    pub fn with_program(rom: &[u8]) -> Self {
        let mut mem = Memory::new();
        mem.load(rom, 0x00);
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
