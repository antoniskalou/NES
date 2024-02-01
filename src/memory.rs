#[derive(Debug)]
pub struct Memory<const N: usize>([u8; N]);

impl<const N: usize> Memory<N> {
    pub fn new() -> Self {
        Memory([0; N])
    }

    pub fn size(&self) -> usize {
        self.0.len()
    }

    pub fn load(&mut self, src: &[u8], pos: u16) {
        let range = (pos as usize)..(pos as usize) + src.len();
        self.0[range].copy_from_slice(src);
    }

    pub fn read_u8(&self, pos: u16) -> u8 {
        self.0[pos as usize]
    }

    pub fn read_u16(&self, pos: u16) -> u16 {
        let lo = self.read_u8(pos) as u16;
        let hi = self.read_u8(pos + 1) as u16;
        (hi << 8) | (lo as u16)
    }

    pub fn write_u8(&mut self, pos: u16, data: u8) {
        self.0[pos as usize] = data;
    }

    pub fn write_u16(&mut self, pos: u16, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0xFF) as u8;
        self.write_u8(pos, lo);
        self.write_u8(pos + 1, hi);
    }
}

impl<const N: usize> From<&[u8]> for Memory<N> {
    fn from(data: &[u8]) -> Self {
        let mut mem = Memory::new();
        mem.load(data, 0x0);
        mem
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_size() {
        let mem = Memory::<8>::new();
        assert_eq!(mem.size(), 8);
    }

    #[test]
    fn test_load() {
        let mut mem = Memory::<8>::new();
        let src = [0xAA, 0xBB, 0xCC, 0xDD];
        mem.load(&src, 0x2);
        // first 2 bytes should be empty
        assert_eq!(mem.read_u8(0x0), 0x0);
        assert_eq!(mem.read_u8(0x1), 0x0);
        for (i, x) in src.iter().enumerate() {
            assert_eq!(mem.read_u8(0x2 + i as u16), *x);
        }
        // last 2 bytes also empty
        assert_eq!(mem.read_u8(0x6), 0x0);
        assert_eq!(mem.read_u8(0x7), 0x0);
    }

    #[test]
    fn test_read_write_u8() {
        let mut mem = Memory::<8>::new();
        mem.write_u8(0, 0xFF);
        assert_eq!(mem.read_u8(0), 0xFF);
        // next byte shouldn't be affected
        assert_eq!(mem.read_u8(1), 0x00);
    }

    #[test]
    fn test_read_write_u16() {
        let mut mem = Memory::<8>::new();
        mem.write_u16(0, 0xABCD);
        assert_eq!(mem.read_u16(0), 0xABCD);
        assert_eq!(mem.read_u16(1), 0x00AB);
        assert_eq!(mem.read_u16(2), 0x0000);
    }
}
