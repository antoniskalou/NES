#[derive(Debug)]
pub struct Memory<const N: usize>([u8; N]);

impl<const N: usize> Memory<N> {
    pub fn new() -> Self {
        Memory([0; N])
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

impl<const N: usize> From<&[u8]> for Memory<N> {
    fn from(data: &[u8]) -> Self {
        let mut mem = Memory::new();
        mem.load(data, 0x0);
        mem
    }
}
