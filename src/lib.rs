use quick_error::quick_error;

enum Address {
    ByteAddress(u16),
}

use self::Address::*;

impl Address {
    fn to_index(&self) -> usize {
        match self {
            ByteAddress(a) => *a as usize,
        }
    }
}

struct Memory(Vec<u8>);

impl Memory {
    fn len(&self) -> usize {
        self.0.len()
    }

    fn get_u8(&self, addr: Address) -> Option<u8> {
        Some(*self.0.get(addr.to_index())?)
    }

    fn get_u16(&self, addr: Address) -> Option<u16> {
        // 2.1
        // In the Z-machine, numbers are usually stored in 2 bytes (in the form
        // most-significant-byte first, then least-significant) and hold any value in the range
        // $0000 to $ffff (0 to 65535 decimal).
        let i = addr.to_index();
        Some((*self.0.get(i)? as u16) << 8 | (*self.0.get(i + 1)? as u16))
    }

    fn get_byte_address(&self, addr: Address) -> Option<Address> {
        Some(Address::ByteAddress(self.get_u16(addr)?))
    }
}

pub struct ZMachine {
    mem: Memory,
}

struct Header<'a>(&'a [u8]);

#[repr(u8)]
#[derive(Debug)]
enum Version {
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

quick_error! {
    #[derive(Debug)]
    pub enum FormatError {
        TooSmall(size: usize) {
            display("story file is too small ({} bytes)", size)
        }
        TooBig(size: usize, max_size: usize) {
            display("story file is too big ({} > {} bytes)", size, max_size)
        }
        UnsupportedVersion(version_byte: u8) {
            display("story file has version {} which is unsupported", version_byte)
        }
        IncorrectLength(expected: usize, actual: usize) {
            display("expected story file length {} bytes but found {} bytes", expected, actual)
        }
    }
}

impl ZMachine {
    pub fn from_bytes(bytes: Vec<u8>) -> Result<ZMachine, FormatError> {
        let z = ZMachine { mem: Memory(bytes) };
        z.check()?;
        Ok(z)
    }

    fn check(&self) -> Result<(), FormatError> {

        let size = self.mem.len();
        if size < 64 {
            return Err(FormatError::TooSmall(size));
        }
        
        let version = self.version_checked()?;

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

        let expected_length = self.length_of_file();
        let actual_length = self.mem.len();
        if expected_length > 0 && actual_length != expected_length {
            return Err(FormatError::IncorrectLength(expected_length, actual_length));
        }

        Ok(())
    }

    fn version_checked(&self) -> Result<Version, FormatError> {
        Version::try_from(self.mem.get_u8(ByteAddress(0x00)).unwrap())
    }

    fn version(&self) -> Version {
        self.version_checked().unwrap()
    }

    fn high_memory_base(&self) -> Address {
        self.mem.get_byte_address(ByteAddress(0x04)).unwrap()
    }

    fn initial_program_counter(&self) -> Address {
        match self.version() {
            V1 | V2 | V3 => self.mem.get_byte_address(ByteAddress(0x06)).unwrap(),
            _ => panic!("version {:?} does not have an initial program counter", self.version()),
        }
    }

    fn dictionary_location(&self) -> Address {
        self.mem.get_byte_address(ByteAddress(0x08)).unwrap()
    }

    fn object_table_location(&self) -> Address {
        self.mem.get_byte_address(ByteAddress(0x0a)).unwrap()
    }

    fn global_variables_table_location(&self) -> Address {
        self.mem.get_byte_address(ByteAddress(0x0c)).unwrap()
    }

    fn static_memory_base(&self) -> Address {
        self.mem.get_byte_address(ByteAddress(0x0e)).unwrap()
    }

    fn abbreviations_table_location(&self) -> Address {
        self.mem.get_byte_address(ByteAddress(0x18)).unwrap()
    }

    fn length_of_file(&self) -> usize {
        // 11.1.6
        // The file length stored at $1a is actually divided by a constant, depending on the
        // Version, to make it fit into a header word. This constant is 2 for Versions 1 to 3, 4
        // for Versions 4 to 5 or 8 for Versions 6 and later.
        self.mem.get_u16(ByteAddress(0x1a)).unwrap() as usize * match self.version() {
            V1 | V2 | V3 => 2
        }
    }

    fn checksum(&self) -> u16 {
        self.mem.get_u16(ByteAddress(0x1c)).unwrap()
    }
}
