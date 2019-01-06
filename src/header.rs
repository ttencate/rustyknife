use crate::bits::*;
use crate::bytes::{Address, Bytes};
use crate::errors::FormatError;
use crate::version::*;

pub struct Header<'a> {
    version: Version,
    bytes: &'a mut Bytes,
}

impl<'a> Header<'a> {
    pub fn new(bytes: &'a mut Bytes) -> Result<Header<'a>, FormatError> {
        // Header is 64 bytes, so that's the minimum memory size.
        let size = bytes.len();
        if size < 64 {
            return Err(FormatError::TooSmall(size));
        }

        // Version number (1 to 6)
        let version = Version::try_from(bytes.get_u8(Address::from_byte_address(0x0000)).unwrap())?;

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

        let header = Header {
            version,
            bytes,
        };

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
        self.bytes.get_u8(flag.addr()).unwrap().bit(flag.bit())
    }

    pub fn set_flag(&mut self, flag: Flag, val: bool) {
        let addr = flag.addr();
        let byte = self.bytes.get_u8(addr).unwrap();
        self.bytes.set_u8(addr, byte.set_bit(flag.bit(), val)).unwrap();
    }

    pub fn static_memory_base(&self) -> Address {
        // Base of static memory (byte address)
        Address::from_byte_address(self.bytes.get_u16(Address::from_byte_address(0x000e)).unwrap())
    }

    pub fn high_memory_base(&self) -> Address {
        // Base of high memory (byte address)
        Address::from_byte_address(self.bytes.get_u16(Address::from_byte_address(0x0004)).unwrap())
    }

    pub fn initial_program_counter(&self) -> Address {
        // v1-5: Initial value of program counter (byte address)
        match self.version() {
            V1 | V2 | V3 => Address::from_byte_address(self.bytes.get_u16(Address::from_byte_address(0x0006)).unwrap()),
        }
    }

    pub fn globals_table_addr(&self) -> Address {
        // Location of global variables table (byte address)
        Address::from_byte_address(self.bytes.get_u16(Address::from_byte_address(0x000c)).unwrap())
    }

    pub fn abbrs_table_addr(&self) -> Address {
        // Location of abbreviations table (byte address)
        Address::from_byte_address(self.bytes.get_u16(Address::from_byte_address(0x0018)).unwrap())
    }

    pub fn obj_table_addr(&self) -> Address {
        // Location of object table (byte address)
        Address::from_byte_address(self.bytes.get_u16(Address::from_byte_address(0x000a)).unwrap())
    }

    // fn story_size(&self) -> usize {
    //     // Length of file
    //     let size = self.bytes.get_u16(Address::from_byte_address(0x001a)).unwrap() as usize;
    //     // Some early Version 3 files do not contain length and checksum data, hence the notation 3+.
    //     if size == 0 {
    //         self.bytes.len()
    //     } else {
    //         // 11.1.6
    //         // The file length stored at $1a is actually divided by a constant, depending on the
    //         // Version, to make it fit into a header word. This constant is 2 for Versions 1 to 3,
    //         // 4 for Versions 4 to 5 or 8 for Versions 6 and later.
    //         size * match self.version() {
    //             V1 | V2 | V3 => 2
    //         }
    //     }
    // }

    // fn checksum(&self) -> Option<u16> {
    //     // Checksum of file
    //     let checksum = self.bytes.get_u16(Address::from_byte_address(0x001c)).unwrap();
    //     // Some early Version 3 files do not contain length and checksum data, hence the notation 3+.
    //     if checksum == 0 { None } else { Some(checksum) }
    // }
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
