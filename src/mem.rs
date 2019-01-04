use crate::bits::*;
use crate::bytes::{ByteAddress, Bytes};
use quick_error::quick_error;

pub struct Memory {
    bytes: Bytes,
}

impl Memory {
    pub fn with_size(size: usize) -> Memory {
        Memory { bytes: Bytes::with_size(size) }
    }

    pub fn from_bytes(bytes: Vec<u8>) -> Result<Memory, FormatError> {
        let bytes = Bytes::from(bytes);

        // Dynamic memory must contain at least 64 bytes.
        let size = bytes.len();
        if size < 64 {
            return Err(FormatError::TooSmall(size));
        }

        let s = Memory { bytes: bytes };

        // Version number (1 to 6)
        let version = s.version_checked()?;

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

        // High memory begins at the "high memory mark" (the byte address stored in the word at $04
        // in the header) and continues to the end of the story file. The bottom of high memory may
        // overlap with the top of static memory (but not with dynamic memory).
        let high_memory_base = s.high_memory_base();
        let static_memory_base = s.static_memory_base();
        if high_memory_base < static_memory_base {
            return Err(FormatError::MemoryOverlap(static_memory_base, high_memory_base));
        }

        Ok(s)
    }

    pub fn bytes(&self) -> &Bytes {
        &self.bytes
    }

    pub fn bytes_mut(&mut self) -> &mut Bytes {
        &mut self.bytes
    }

    fn version_checked(&self) -> Result<Version, FormatError> {
        Version::try_from(self.bytes.get_u8(ByteAddress(0x0000)).unwrap())
    }

    pub fn version(&self) -> Version {
        self.version_checked().unwrap()
    }

    pub fn flag(&self, flag: Flag) -> bool {
        self.bytes.get_u8(flag.addr()).unwrap().bit(flag.bit())
    }

    pub fn set_flag(&mut self, flag: Flag, value: bool) {
        let byte = self.bytes.get_u8_mut(flag.addr()).unwrap();
        *byte = byte.set_bit(flag.bit(), value);
    }

    fn high_memory_base(&self) -> ByteAddress {
        // Base of high memory (byte address)
        self.bytes.get_byte_address(ByteAddress(0x0004)).unwrap()
    }

    pub fn initial_program_counter(&self) -> ByteAddress {
        // v1-5: Initial value of program counter (byte address)
        match self.version() {
            V1 | V2 | V3 => self.bytes.get_byte_address(ByteAddress(0x0006)).unwrap(),
        }
    }

    fn static_memory_base(&self) -> ByteAddress {
        // Base of static memory (byte address)
        self.bytes.get_byte_address(ByteAddress(0x000e)).unwrap()
    }

    fn story_size(&self) -> usize {
        // Length of file
        let size = self.bytes.get_u16(ByteAddress(0x001a)).unwrap() as usize;
        // Some early Version 3 files do not contain length and checksum data, hence the notation 3+.
        if size == 0 {
            self.bytes.len()
        } else {
            // 11.1.6
            // The file length stored at $1a is actually divided by a constant, depending on the
            // Version, to make it fit into a header word. This constant is 2 for Versions 1 to 3,
            // 4 for Versions 4 to 5 or 8 for Versions 6 and later.
            size * match self.version() {
                V1 | V2 | V3 => 2
            }
        }
    }

    fn checksum(&self) -> Option<u16> {
        // Checksum of file
        let checksum = self.bytes.get_u16(ByteAddress(0x001c)).unwrap();
        // Some early Version 3 files do not contain length and checksum data, hence the notation 3+.
        if checksum == 0 { None } else { Some(checksum) }
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum Version {
    V1 = 1,
    V2 = 2,
    V3 = 3,
}

use self::Version::*;

impl Version {
    // When TryFrom is graduated from nightly, we can implement that with the same signature.
    fn try_from(byte: u8) -> Result<Version, FormatError> {
        match byte {
            1 => Ok(Version::V1),
            2 => Ok(Version::V2),
            3 => Ok(Version::V3),
            _ => Err(FormatError::UnsupportedVersion(byte))
        }
    }
}

pub struct Flag(ByteAddress, Bit);

impl Flag {
    fn addr(&self) -> ByteAddress {
        self.0
    }

    fn bit(&self) -> Bit {
        self.1
    }
}

// Flags 1 (in Versions 1 to 3):
const FLAGS_1: ByteAddress = ByteAddress(0x0001);
// 4: Status line not available?
pub const STATUS_LINE_NOT_AVAILABLE: Flag = Flag(FLAGS_1, BIT4);
// 5: Screen-splitting available?
pub const SCREEN_SPLITTING_AVAILABLE: Flag = Flag(FLAGS_1, BIT5);
// 6: Is a variable-pitch font the default?
pub const VARIABLE_PITCH_FONT_DEFAULT: Flag = Flag(FLAGS_1, BIT6);

// Flags 2:
const FLAGS_2: ByteAddress = ByteAddress(0x0010);
// 0: Set when transcripting is on
pub const TRANSCRIPTING_ON: Flag = Flag(FLAGS_2, BIT0);
// 1: Game sets to force printing in fixed-pitch font
pub const FORCE_FIXED_PITCH_FONT: Flag = Flag(FLAGS_2, BIT1);

quick_error! {
    #[derive(Debug)]
    pub enum FormatError {
        TooSmall(size: usize) {
            display("story file is too small ({} bytes)", size)
        }
        TooBig(size: usize, max_size: usize) {
            display("story file is too big ({} > {} bytes)", size, max_size)
        }
        MemoryOverlap(static_memory_base: ByteAddress, high_memory_base: ByteAddress) {
            display("high memory may not overlap with dynamic memory: {:?} < {:?}", static_memory_base, high_memory_base)
        }
        UnsupportedVersion(version_byte: u8) {
            display("story file has version {} which is unsupported", version_byte)
        }
    }
}
