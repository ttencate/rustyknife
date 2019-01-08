use crate::bits::*;
use crate::bytes::{Address, Bytes};
use crate::errors::FormatError;
use crate::version::*;
use std::cell::RefCell;
use std::rc::Rc;

pub struct Header {
    version: Version,
    bytes: Rc<RefCell<Bytes>>,
    actual_checksum: u16,
}

impl Header {
    pub fn new(bytes: Rc<RefCell<Bytes>>) -> Result<Header, FormatError> {
        // Header is 64 bytes, so that's the minimum memory size.
        let size = bytes.borrow().len();
        if size < 64 {
            return Err(FormatError::TooSmall(size));
        }

        // Version number (1 to 6)
        let version = Version::try_from(bytes.borrow().get_u8(Address::from_byte_address(0x0000)).unwrap())?;

        // 1.1.4
        // The maximum permitted length of a story file depends on the Version, as follows:
        // V1-3    V4-5    V6-8
        //  128     256     512
        let max_size = match version {
            V1 | V2 | V3 => 128 * 1024,
        };
        if size > max_size {
            return Err(FormatError::TooBig(size, max_size));
        }

        let mut header = Header {
            version: version,
            bytes: bytes,
            actual_checksum: 0,
        };
        header.actual_checksum = header.compute_checksum()?;

        // High memory begins at the "high memory mark" (the byte address stored in the word at $04
        // in the header) and continues to the end of the story file. The bottom of high memory may
        // overlap with the top of static memory (but not with dynamic memory).
        let high_memory_base = header.high_memory_base();
        let static_memory_base = header.static_memory_base();
        if high_memory_base < static_memory_base {
            return Err(FormatError::MemoryOverlap(static_memory_base, high_memory_base));
        }

        Ok(header)
    }

    pub fn version(&self) -> Version {
        self.version
    }

    pub fn flag(&self, flag: Flag) -> bool {
        self.bytes.borrow().get_u8(flag.addr()).unwrap().bit(flag.bit())
    }

    pub fn set_flag(&mut self, flag: Flag, val: bool) {
        let addr = flag.addr();
        let byte = self.bytes.borrow().get_u8(addr).unwrap();
        self.bytes.borrow_mut().set_u8(addr, byte.set_bit(flag.bit(), val)).unwrap();
    }

    pub fn static_memory_base(&self) -> Address {
        // Base of static memory (byte address)
        Address::from_byte_address(self.bytes.borrow().get_u16(Address::from_byte_address(0x000e)).unwrap())
    }

    pub fn high_memory_base(&self) -> Address {
        // Base of high memory (byte address)
        Address::from_byte_address(self.bytes.borrow().get_u16(Address::from_byte_address(0x0004)).unwrap())
    }

    pub fn initial_program_counter(&self) -> Address {
        // v1-5: Initial value of program counter (byte address)
        match self.version() {
            V1 | V2 | V3 => Address::from_byte_address(self.bytes.borrow().get_u16(Address::from_byte_address(0x0006)).unwrap()),
        }
    }

    pub fn globals_table_addr(&self) -> Address {
        // Location of global variables table (byte address)
        Address::from_byte_address(self.bytes.borrow().get_u16(Address::from_byte_address(0x000c)).unwrap())
    }

    pub fn abbrs_table_addr(&self) -> Address {
        // Location of abbreviations table (byte address)
        Address::from_byte_address(self.bytes.borrow().get_u16(Address::from_byte_address(0x0018)).unwrap())
    }

    pub fn obj_table_addr(&self) -> Address {
        // Location of object table (byte address)
        Address::from_byte_address(self.bytes.borrow().get_u16(Address::from_byte_address(0x000a)).unwrap())
    }

    pub fn dict_table_addr(&self) -> Address {
        // Location of dictionary (byte address)
        Address::from_byte_address(self.bytes.borrow().get_u16(Address::from_byte_address(0x0008)).unwrap())
    }

    fn file_length(&self) -> Result<usize, FormatError> {
        // Length of file
        let size = self.bytes.borrow().get_u16(Address::from_byte_address(0x001a)).unwrap() as usize;
        let num_bytes = self.bytes.borrow().len();
        // Some early Version 3 files do not contain length and checksum data, hence the notation 3+.
        if size == 0 {
            Ok(num_bytes)
        } else {
            // 11.1.6
            // The file length stored at $1a is actually divided by a constant, depending on the
            // Version, to make it fit into a header word. This constant is 2 for Versions 1 to 3,
            // 4 for Versions 4 to 5 or 8 for Versions 6 and later.
            let factor = match self.version() {
                V1 | V2 | V3 => 2
            };
            let file_length = factor * size;
            // It is legal to have more bytes than file_length indicates, but not less.
            if file_length > num_bytes {
                Err(FormatError::InvalidFileLength(file_length, num_bytes))
            } else {
                Ok(file_length)
            }
        }
    }

    pub fn stored_checksum(&self) -> Option<u16> {
        // Checksum of file
        let checksum = self.bytes.borrow().get_u16(Address::from_byte_address(0x001c)).unwrap();
        // Some early Version 3 files do not contain length and checksum data, hence the notation 3+.
        if checksum == 0 { None } else { Some(checksum) }
    }

    pub fn actual_checksum(&self) -> u16 {
        self.actual_checksum
    }

    pub fn compute_checksum(&self) -> Result<u16, FormatError> {
        // Verification counts a (two byte, unsigned) checksum of the file from $0040 onwards (by
        // taking the sum of the values of each byte in the file, modulo $10000) and compares this
        // against the value in the game header, branching if the two values agree. (Early Version
        // 3 games do not have the necessary checksums to make this possible.)
        //
        // The interpreter must stop calculating when the file length (as given in the header) is
        // reached. It is legal for the file to contain more bytes than this, but if so the extra
        // bytes should all be 0. (Some story files are padded out to an exact number of
        // virtual-memory pages.) However, many Infocom story files in fact contain non-zero data
        // in the padding, so interpreters must be sure to exclude the padding from checksum
        // calculations.
        let bytes = self.bytes.borrow();
        let slice = bytes
            .get_slice(Address::from_byte_address(0x0040)..Address::from_index(self.file_length()?))
            .unwrap(); // Unwrap is safe because the file length has been verified.
        let mut checksum: u16 = 0;
        for &byte in slice {
            checksum = checksum.wrapping_add(byte as u16);
        }
        Ok(checksum)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Flag(Address, Bit);

impl Flag {
    fn addr(&self) -> Address {
        self.0
    }

    fn bit(&self) -> Bit {
        self.1
    }
}

// Flags 1 (in Versions 1 to 3):
const FLAGS_1: Address = Address::from_byte_address(0x0001);
// 4: Status line not available?
pub const STATUS_LINE_NOT_AVAILABLE: Flag = Flag(FLAGS_1, BIT4);
// 5: Screen-splitting available?
pub const SCREEN_SPLITTING_AVAILABLE: Flag = Flag(FLAGS_1, BIT5);
// 6: Is a variable-pitch font the default?
pub const VARIABLE_PITCH_FONT_DEFAULT: Flag = Flag(FLAGS_1, BIT6);

// Flags 2:
const FLAGS_2: Address = Address::from_byte_address(0x0010);
// 0: Set when transcripting is on
pub const TRANSCRIPTING_ON: Flag = Flag(FLAGS_2, BIT0);
// 1: Game sets to force printing in fixed-pitch font
pub const FORCE_FIXED_PITCH_FONT: Flag = Flag(FLAGS_2, BIT1);
