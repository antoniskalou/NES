#[derive(Debug)]
pub struct Memory(Vec<u8>);

impl Memory {
    pub fn new(size: usize) -> Self {
        // TODO: figure out a way of using an array, see if we can provide
        // the array size somehow during compile time.
        Memory(vec![0; size])
    }

    pub fn with_program(rom: &[u8]) -> Self {
        let mut mem = Memory::new(rom.len());
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
