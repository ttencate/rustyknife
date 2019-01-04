use crate::bits::*;
use crate::mem::Version;
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

    pub fn get_u8(&self, addr: Address) -> Option<u8> {
        Some(*self.0.get(addr.to_index())?)
    }

    pub fn get_u8_mut(&mut self, addr: Address) -> Option<&mut u8> {
        Some(self.0.get_mut(addr.to_index())?)
    }

    pub fn get_u16(&self, addr: Address) -> Option<u16> {
        // 2.1
        // In the Z-machine, numbers are usually stored in 2 bytes (in the form
        // most-significant-byte first, then least-significant) and hold any value in the range
        // $0000 to $ffff (0 to 65535 decimal).
        let i = addr.to_index();
        Some((*self.0.get(i)? as u16) << 8 | (*self.0.get(i + 1)? as u16))
    }

    pub fn get_zstring(&self, addr: Address) -> Option<ZString> {
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

    pub fn get_slice(&self, range: Range<Address>) -> Option<&[u8]> {
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
}

impl From<Vec<u8>> for Bytes {
    fn from(bytes: Vec<u8>) -> Bytes {
        Bytes(bytes)
    }
}

// 1.2
// There are three kinds of address in the Z-machine, all of which can be stored in a 2-byte
// number: byte addresses, word addresses and packed addresses.
//
// We could make an enum to represent these, but it's easier to just convert them all to a common
// type upon construction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Address(usize);

impl Address {
    pub const fn from_byte_address(addr: u16) -> Address {
        // 1.2.1
        // A byte address specifies a byte in memory in the range 0 up to the last byte of static
        // memory.
        Address(addr as usize)
    }

    pub fn from_word_address(word_addr: u16) -> Address {
        // 1.2.2
        // A word address specifies an even address in the bottom 128K of memory (by giving the
        // address divided by 2). (Word addresses are used only in the abbreviations table.)
        Address(word_addr as usize * 2)
    }

    pub fn from_packed_address(packed_addr: u16, version: Version) -> Address {
        // 1.2.3
        // ***[1.0] A packed address specifies where a routine or string begins in high memory.
        // Given a packed address P, the formula to obtain the corresponding byte address B is:
        // 
        //   2P           Versions 1, 2 and 3
        //   4P           Versions 4 and 5
        //   4P + 8R_O    Versions 6 and 7, for routine calls
        //   4P + 8S_O    Versions 6 and 7, for print_paddr
        //   8P           Version 8
        // 
        // R_O and S_O are the routine and strings offsets (specified in the header as words at $28
        // and $2a, respectively).
        match version {
            Version::V1 | Version::V2 | Version::V3 => Address(packed_addr as usize * 2)
        }
    }

    fn to_index(self) -> usize {
        self.0
    }
}

impl Add<usize> for Address {
    type Output = Address;
    fn add(self, offset: usize) -> Address {
        Address(self.0 + offset)
    }
}

impl AddAssign<usize> for Address {
    fn add_assign(&mut self, offset: usize) {
        self.0 += offset
    }
}

impl Add<i32> for Address {
    type Output = Address;
    fn add(self, offset: i32) -> Address {
        Address((self.0 as i32 + offset) as usize)
    }
}

impl AddAssign<i32> for Address {
    fn add_assign(&mut self, offset: i32) {
        self.0 = (self.0 as i32 + offset) as usize
    }
}

impl Display for Address {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:}", self.0)
    }
}
