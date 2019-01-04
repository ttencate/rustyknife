use crate::bits::*;
use crate::zstring::ZString;
use std::fmt;
use std::fmt::{Display, Formatter};
use std::ops::*;

pub struct Bytes(Vec<u8>);

impl Bytes {
    pub fn with_size(size: usize) -> Bytes {
        Bytes(vec![0; size])
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn copy_from(&mut self, other: &Bytes) {
        assert!(self.len() == other.len());
        self.0.copy_from_slice(&other.as_slice());
    }

    pub fn get_u8(&self, addr: ByteAddress) -> Option<u8> {
        Some(*self.0.get(addr.to_index())?)
    }

    pub fn get_u8_mut(&mut self, addr: ByteAddress) -> Option<&mut u8> {
        Some(self.0.get_mut(addr.to_index())?)
    }

    pub fn get_u16(&self, addr: ByteAddress) -> Option<u16> {
        // 2.1
        // In the Z-machine, numbers are usually stored in 2 bytes (in the form
        // most-significant-byte first, then least-significant) and hold any value in the range
        // $0000 to $ffff (0 to 65535 decimal).
        let i = addr.to_index();
        Some((*self.0.get(i)? as u16) << 8 | (*self.0.get(i + 1)? as u16))
    }

    pub fn get_zstring(&self, addr: ByteAddress) -> Option<ZString> {
        // 3.2
        // Text in memory consists of a sequence of 2-byte words. Each word is divided into three 5-bit 'Z-characters', plus 1 bit left over, arranged as
        //
        //    --first byte-------   --second byte---
        //    7    6 5 4 3 2  1 0   7 6 5  4 3 2 1 0
        //    bit  --first--  --second---  --third--
        //
        // The bit is set only on the last 2-byte word of the text, and so marks the end.
        let mut end_addr = addr;
        while !self.get_u16(end_addr)?.bit(BIT15) {
            end_addr += 2;
        }
        end_addr += 2;
        Some(ZString::from(self.get_slice(addr..end_addr)?))
    }

    pub fn get_slice(&self, range: Range<ByteAddress>) -> Option<&[u8]> {
        let s = range.start.to_index();
        let e = range.end.to_index();
        if s <= self.len() && e <= self.len() {
            Some(&self.0[s..e])
        } else {
            None
        }
    }

    pub fn as_slice(&self) -> &[u8] {
        &self.0
    }

    pub fn get_byte_address(&self, addr: ByteAddress) -> Option<ByteAddress> {
        Some(ByteAddress(self.get_u16(addr)?))
    }
}

impl From<Vec<u8>> for Bytes {
    fn from(bytes: Vec<u8>) -> Bytes {
        Bytes(bytes)
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub struct ByteAddress(pub u16);

impl ByteAddress {
    fn to_index(&self) -> usize {
        match self {
            ByteAddress(a) => *a as usize,
        }
    }
}

impl Add<i16> for ByteAddress {
    type Output = ByteAddress;
    fn add(self, offset: i16) -> ByteAddress {
        let mut c = self;
        c += offset;
        c
    }
}

impl AddAssign<i16> for ByteAddress {
    fn add_assign(&mut self, offset: i16) {
        self.0 = (self.0 as i16 + offset) as u16
    }
}

impl Display for ByteAddress {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:}", self.0)
    }
}
