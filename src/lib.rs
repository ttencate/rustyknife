use quick_error::quick_error;
use std::ops::{AddAssign, RangeInclusive};

#[cfg(test)]
mod tests;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub struct ByteAddress(u16);

impl ByteAddress {
    fn to_index(&self) -> usize {
        match self {
            ByteAddress(a) => *a as usize,
        }
    }
}

impl AddAssign<i16> for ByteAddress {
    fn add_assign(&mut self, offset: i16) {
        self.0 = self.0.wrapping_add(offset as u16);
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
struct Bit(u8);

impl Bit {
    fn mask(self) -> u8 {
        1 << self.0
    }
}

struct Memory(Vec<u8>);

impl Memory {
    fn len(&self) -> usize {
        self.0.len()
    }

    fn get_u8(&self, addr: ByteAddress) -> Option<u8> {
        Some(*self.0.get(addr.to_index())?)
    }

    fn get_u8_mut(&mut self, addr: ByteAddress) -> Option<&mut u8> {
        Some(self.0.get_mut(addr.to_index())?)
    }

    fn get_u16(&self, addr: ByteAddress) -> Option<u16> {
        // 2.1
        // In the Z-machine, numbers are usually stored in 2 bytes (in the form
        // most-significant-byte first, then least-significant) and hold any value in the range
        // $0000 to $ffff (0 to 65535 decimal).
        let i = addr.to_index();
        Some((*self.0.get(i)? as u16) << 8 | (*self.0.get(i + 1)? as u16))
    }

    fn get_byte_address(&self, addr: ByteAddress) -> Option<ByteAddress> {
        Some(ByteAddress(self.get_u16(addr)?))
    }
}

pub struct StoryFile {
    mem: Memory,
}

struct Header<'a>(&'a [u8]);

#[repr(u8)]
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
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
        MemoryOverlap(static_memory_base: ByteAddress, high_memory_base: ByteAddress) {
            display("high memory may not overlap with dynamic memory: {:?} < {:?}", static_memory_base, high_memory_base)
        }
        UnsupportedVersion(version_byte: u8) {
            display("story file has version {} which is unsupported", version_byte)
        }
    }
}

impl StoryFile {
    pub fn from_bytes(bytes: Vec<u8>) -> Result<StoryFile, FormatError> {
        // Dynamic memory must contain at least 64 bytes.
        let size = bytes.len();
        if size < 64 {
            return Err(FormatError::TooSmall(size));
        }

        let s = StoryFile {
            mem: Memory(bytes),
        };

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

    fn version_checked(&self) -> Result<Version, FormatError> {
        Version::try_from(self.mem.get_u8(ByteAddress(0x0000)).unwrap())
    }

    fn version(&self) -> Version {
        self.version_checked().unwrap()
    }

    fn high_memory_base(&self) -> ByteAddress {
        // Base of high memory (byte address)
        self.mem.get_byte_address(ByteAddress(0x0004)).unwrap()
    }

    fn initial_program_counter(&self) -> ByteAddress {
        // v1-5: Initial value of program counter (byte address)
        match self.version() {
            V1 | V2 | V3 => self.mem.get_byte_address(ByteAddress(0x0006)).unwrap(),
        }
    }

    fn static_memory_base(&self) -> ByteAddress {
        // Base of static memory (byte address)
        self.mem.get_byte_address(ByteAddress(0x000e)).unwrap()
    }

    fn story_size(&self) -> usize {
        // Length of file
        let size = self.mem.get_u16(ByteAddress(0x001a)).unwrap() as usize;
        // Some early Version 3 files do not contain length and checksum data, hence the notation 3+.
        if size == 0 {
            self.mem.len()
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
        let checksum = self.mem.get_u16(ByteAddress(0x001c)).unwrap();
        // Some early Version 3 files do not contain length and checksum data, hence the notation 3+.
        if checksum == 0 { None } else { Some(checksum) }
    }
}

pub struct ZMachine<'a> {
    s: &'a StoryFile,
    dyn_mem: Memory,
    pc: ByteAddress,
}

struct Flag(ByteAddress, Bit);

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
const STATUS_LINE_NOT_AVAILABLE: Flag = Flag(FLAGS_1, Bit(4));
// 5: Screen-splitting available?
const SCREEN_SPLITTING_AVAILABLE: Flag = Flag(FLAGS_1, Bit(5));
// 6: Is a variable-pitch font the default?
const VARIABLE_PITCH_FONT_DEFAULT: Flag = Flag(FLAGS_1, Bit(6));

// Flags 2:
const FLAGS_2: ByteAddress = ByteAddress(0x0010);
// 0: Set when transcripting is on
const TRANSCRIPTING_ON: Flag = Flag(FLAGS_2, Bit(0));
// 1: Game sets to force printing in fixed-pitch font
const FORCE_FIXED_PITCH_FONT: Flag = Flag(FLAGS_2, Bit(1));

fn get_bits(byte: u8, range: RangeInclusive<u8>) -> u8 {
    if range.start() > range.end() {
        return 0;
    }
    let s = *range.start();
    let e = *range.end() + 1;
    assert!(s < 8);
    assert!(e <= 8);
    (byte >> s) & ((1u8 << (e - s)).wrapping_sub(1))
}

#[derive(Debug)]
pub struct ErrorLocation {
    addr: ByteAddress,
    instr_bytes: Vec<u8>,
}

quick_error! {
    #[derive(Debug)]
    pub enum RuntimeError {
        ProgramCounterOutOfRange(loc: ErrorLocation) {
            display("program counter out of range at {:?}", loc)
        }
        InvalidInstruction(opcode: u8, loc: ErrorLocation) {
            display("invalid instruction {:?} at {:?}", opcode, loc)
        }
        TooManyOperands(types: u8, loc: ErrorLocation) {
            display("too many operand types {:#b} at {:?}", types, loc)
        }
        InvalidOperandTypes(types: u8, loc: ErrorLocation) {
            display("invalid operand types {:#b} at {:?}", types, loc)
        }
    }
}

struct InstructionDecoder<'a> {
    version: Version,
    z: &'a ZMachine<'a>,
    start_addr: ByteAddress,
    next_addr: ByteAddress,
}

impl<'a> InstructionDecoder<'a> {
    pub fn new(z: &'a ZMachine<'a>) -> InstructionDecoder<'a> {
        InstructionDecoder {
            version: z.version(),
            z: z,
            start_addr: z.pc,
            next_addr: z.pc,
        }
    }

    pub fn decode(&mut self) -> Result<Instruction, RuntimeError> {
        // 4.1
        // A single Z-machine instruction consists of the following sections (and in the order
        // shown):
        //
        //   Opcode               1 or 2 bytes
        //   (Types of operands)  1 or 2 bytes: 4 or 8 2-bit fields
        //   Operands             Between 0 and 8 of these: each 1 or 2 bytes
        //   (Store variable)     1 byte
        //   (Branch offset)      1 or 2 bytes
        //   (Text to print)      An encoded string (of unlimited length)
        //
        // Bracketed sections are not present in all opcodes. (A few opcodes take both "store" and
        // "branch".)

        // For a more gentle introduction to the instruction encoding:
        // https://ericlippert.com/2016/03/09/canyon-view/
        // https://ericlippert.com/2016/03/11/end-of-rainbow/

        let opcode = self.next_byte().ok_or(RuntimeError::ProgramCounterOutOfRange(self.loc()))?;
        let instruction_form = self.instruction_form(opcode)?;
        let operand_count = self.operand_count(instruction_form, opcode)?;
        let opcode_number = self.read_opcode_number(instruction_form, opcode)?;
        let operand_types = self.read_operand_types(instruction_form, opcode, opcode_number)?;

        let instr = match (operand_count, opcode_number) {
            (OperandCount::Zero, 0x04) => Instruction::Nop,
            _ => return Err(RuntimeError::InvalidInstruction(opcode, self.loc())),
        };

        Ok(instr)
    }

    pub fn next_addr(&self) -> ByteAddress {
        self.next_addr
    }

    fn instruction_form(&self, opcode: u8) -> Result<InstructionForm, RuntimeError> {
        match get_bits(opcode, 6..=7) {
            // 4.3
            // ... If the top two bits of the opcode are $$11 the form is variable; ...
            0b11 => Ok(InstructionForm::Variable),
            // ... if $$10, the form is short.
            0b10 => Ok(InstructionForm::Short),
            0b01 | 0b00 => {
                if opcode == 190 {
                    // If the opcode is 190 ($BE in hexadecimal) and the version is 5 or later, the
                    // form is "extended". ...
                    match self.version {
                        V1 | V2 | V3 => Err(RuntimeError::InvalidInstruction(opcode, self.loc()))
                    }
                } else {
                    // ... Otherwise, the form is "long".
                    Ok(InstructionForm::Long)
                }
            },
            _ => panic!("two bits can never exceed 0b11")
        }
    }

    fn operand_count(&self, instruction_form: InstructionForm, opcode: u8) -> Result<OperandCount, RuntimeError> {
        match instruction_form {
            // 4.3.1
            // In short form, bits 4 and 5 of the opcode byte give an operand type as above. If
            // this is $11 then the operand count is 0OP; otherwise, 1OP.
            InstructionForm::Short => {
                if get_bits(opcode, 4..=5) == 0b11 {
                    Ok(OperandCount::Zero)
                } else {
                    Ok(OperandCount::One)
                }
            }
            // 4.3.2
            // In long form the operand count is always 2OP.
            InstructionForm::Long => Ok(OperandCount::Two),
            // 4.3.3
            // In variable form, if bit 5 is 0 then the count is 2OP; if it is 1, then the count is
            // VAR.
            InstructionForm::Variable => {
                if get_bits(opcode, 5..=5) == 0 {
                    Ok(OperandCount::Two)
                } else {
                    Ok(OperandCount::Var)
                }
            }
            // 4.3.4
            // In extended form, the operand count is VAR.
            InstructionForm::Extended => Ok(OperandCount::Var),
        }
    }

    fn read_opcode_number(&mut self, instruction_form: InstructionForm, opcode: u8) -> Result<u8, RuntimeError> {
        match instruction_form {
            // 4.3.1
            // In short form, ... In either case the opcode number is given in the bottom 4 bits.
            InstructionForm::Short => Ok(get_bits(opcode, 0..=4)),
            // 4.3.2
            // In long form ... The opcode number is given in the bottom 5 bits.
            InstructionForm::Long => Ok(get_bits(opcode, 0..=4)),
            // 4.3.3
            // In variable form ... The opcode number is given in the bottom 5 bits.
            InstructionForm::Variable => Ok(get_bits(opcode, 0..=5)),
            // 4.3.4
            // In extended form, ... The opcode number is given in a second opcode byte.
            InstructionForm::Extended => self.next_byte().ok_or(RuntimeError::ProgramCounterOutOfRange(self.loc())),
        }
    }

    fn read_operand_types(&mut self, instruction_form: InstructionForm, opcode: u8, opcode_number: u8) -> Result<Vec<OperandType>, RuntimeError> {
        // 4.4
        // Next, the types of the operands are specified.
        match instruction_form {
            // 4.4.1
            // In short form, bits 4 and 5 of the opcode give the type.
            InstructionForm::Short => Ok(vec![
                OperandType::from_bits(get_bits(opcode, 4..=5)),
            ]),
            // 4.4.2
            // In long form, bit 6 of the opcode gives the type of the first operand, bit 5 of the
            // second. A value of 0 means a small constant and 1 means a variable. (If a 2OP
            // instruction needs a large constant as operand, then it should be assembled in variable
            // rather than long form.)
            InstructionForm::Long => Ok(vec![
                OperandType::from_bit(get_bits(opcode, 6..=6)),
                OperandType::from_bit(get_bits(opcode, 5..=5)),
            ]),
            // 4.4.3
            // In variable or extended forms, a byte of 4 operand types is given next. This contains 4
            // 2-bit fields: bits 6 and 7 are the first field, bits 0 and 1 the fourth. The values are
            // operand types as above. Once one type has been given as 'omitted', all subsequent ones
            // must be. Example: $$00101111 means large constant followed by variable (and no third or
            // fourth opcode).
            InstructionForm::Extended | InstructionForm::Variable => {
                // 4.4.3.1
                // In the special case of the "double variable" VAR opcodes call_vs2 and call_vn2
                // (opcode numbers 12 and 26), a second byte of types is given, containing the
                // types for the next four operands.
                let num_bytes = if opcode_number == 12 || opcode_number == 26 { 2 } else { 1 };
                let mut types = Vec::with_capacity(4 * num_bytes);
                let mut expect_omitted = false;
                for i in 0..num_bytes {
                    let byte = self.next_byte().ok_or(RuntimeError::ProgramCounterOutOfRange(self.loc()))?;
                    for &start_bit in &[6, 4, 2, 0] {
                        let operand_type = OperandType::from_bits(get_bits(byte, start_bit..=start_bit + 1));
                        match operand_type {
                            OperandType::Omitted => {
                                expect_omitted = true;
                            }
                            _ => {
                                if expect_omitted {
                                    return Err(RuntimeError::InvalidOperandTypes(byte, self.loc()));
                                }
                                types.push(operand_type);
                            }
                        }
                    }
                    if instruction_form == InstructionForm::Extended && types.len() > 2 {
                        return Err(RuntimeError::TooManyOperands(byte, self.loc()));
                    }
                }
                Ok(types)
            },
        }
    }

    fn next_byte(&mut self) -> Option<u8> {
        let b = self.z.get_u8(self.next_addr);
        if b.is_some() {
            // TODO this might overflow even if we never read the next byte!
            self.next_addr += 1;
        }
        b
    }

    fn loc(&self) -> ErrorLocation {
        ErrorLocation {
            addr: self.start_addr,
            instr_bytes: (self.start_addr.to_index()..self.next_addr.to_index())
                .map(|i| self.z.get_u8(ByteAddress(i as u16)).unwrap()).collect(),
        }
    }
}

// 4.2
// There are four 'types' of operand.
enum OperandType {
    LargeConstant,
    SmallConstant,
    Variable,
    Omitted,
}

impl OperandType {
    fn from_bits(bits: u8) -> OperandType {
        // 4.2
        // There are four 'types' of operand. These are often specified by a number stored in 2 binary
        match bits {
            //   $$00    Large constant (0 to 65535)    2 bytes
            0b00 => OperandType::LargeConstant,
            //   $$01    Small constant (0 to 255)      1 byte
            0b01 => OperandType::SmallConstant,
            //   $$10    Variable                       1 byte
            0b10 => OperandType::Variable,
            //   $$11    Omitted altogether             0 bytes
            0b11 => OperandType::Omitted,
            _ => panic!("2-bit value should not be equal to {:}", bits)
        }
    }

    fn from_bit(bit: u8) -> OperandType {
        // 4.4.2
        // In long form, bit 6 of the opcode gives the type of the first operand, bit 5 of the
        // second.
        match bit {
            // A value of 0 means a small constant ...
            0b0 => OperandType::SmallConstant,
            // ... and 1 means a variable.
            0b1 => OperandType::Variable,
            // (If a 2OP instruction needs a large constant as operand, then it should be assembled
            // in variable rather than long form.)
            _ => panic!("1-bit value should not be equal to {:}", bit)
        }
    }
}

// 4.2.2
// Variable number $00 refers to the top of the stack, $01 to $0f mean the local variables of the
// current routine and $10 to $ff mean the global variables. It is illegal to refer to local
// variables which do not exist for the current routine (there may even be none).
enum Variable {
    TopOfStack,
    Local(u8),
    Global(u8),
}

// 4.3
// Each instruction has a form (long, short, extended or variable) ...
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum InstructionForm {
    Long,
    Short,
    Extended,
    Variable,
}

// 4.3 (continued)
// ... and an operand count (0OP, 1OP, 2OP or VAR).
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum OperandCount {
    Zero,
    One,
    Two,
    Var,
}

enum Operand {
    // 4.2.1
    // Large constants, like all 2-byte words of data in the Z-machine, are stored with most
    // significant byte first (e.g. $2478 is stored as $24 followed by $78). A 'large constant' may
    // in fact be a small number.
    LargeConstant(u16),
    // 4.2.3 (part)
    // Some instructions take as an operand a "variable by reference": for instance, inc has one
    // operand, the reference number of a variable to increment. This operand usually has type
    // 'Small constant' (and Inform automatically assembles a line like @inc turns by writing the
    // operand turns as a small constant with value the reference number of the variable turns).
    SmallConstant(u8),
    // 4.2.3
    // The type 'Variable' really means "variable by value".
    Variable(Variable),
}

enum Instruction {
    Nop,
}

impl<'a> ZMachine<'a> {
    pub fn new(s: &StoryFile) -> ZMachine {
        let mut z = ZMachine {
            s: s,
            dyn_mem: Memory(vec![0; s.static_memory_base().to_index()]),
            pc: ByteAddress(0),
        };
        z.restart();
        z
    }

    pub fn restart(&mut self) {
        let dyn_mem_len = self.dyn_mem.len();
        self.dyn_mem.0.copy_from_slice(&self.s.mem.0[0..dyn_mem_len]);
        self.pc = self.s.initial_program_counter();
        self.reset();
    }

    pub fn step(&mut self) -> Result<(), RuntimeError> {
        let (instr, next_pc) = self.decode_next_instr()?;
        self.pc = next_pc;
        Ok(())
    }

    fn reset(&mut self) {
        self.set_flag(STATUS_LINE_NOT_AVAILABLE, false);
        self.set_flag(SCREEN_SPLITTING_AVAILABLE, true);
        self.set_flag(VARIABLE_PITCH_FONT_DEFAULT, true);
        self.set_flag(TRANSCRIPTING_ON, false);
        if self.s.version() >= Version::V3 {
            self.set_flag(FORCE_FIXED_PITCH_FONT, false);
        }

        // Interpreter number
        // 11.1.3
        // Infocom used the interpreter numbers:
        //
        //    1   DECSystem-20     5   Atari ST           9   Apple IIc
        //    2   Apple IIe        6   IBM PC            10   Apple IIgs
        //    3   Macintosh        7   Commodore 128     11   Tandy Color
        //    4   Amiga            8   Commodore 64
        *self.dyn_mem.get_u8_mut(ByteAddress(0x001e)).unwrap() = 6;

        // Interpreter version
        // 11.1.3.1
        // Interpreter versions are conventionally ASCII codes for upper-case letters in Versions 4
        // and 5 (note that Infocom's Version 6 interpreters just store numbers here).
        *self.dyn_mem.get_u8_mut(ByteAddress(0x001f)).unwrap() = 'A' as u8;
    }

    fn flag(&self, flag: Flag) -> bool {
        (self.dyn_mem.get_u8(flag.addr()).unwrap() & flag.bit().mask()) != 0
    }

    fn set_flag(&mut self, flag: Flag, value: bool) {
        let byte = self.dyn_mem.get_u8_mut(flag.addr()).unwrap();
        if value {
            *byte |= flag.bit().mask();
        } else {
            *byte &= !flag.bit().mask();
        }
    }

    fn get_u8(&self, addr: ByteAddress) -> Option<u8> {
        self.dyn_mem.get_u8(addr).or_else(|| self.s.mem.get_u8(addr))
    }

    fn decode_next_instr(&self) -> Result<(Instruction, ByteAddress), RuntimeError> {
        let mut decoder = InstructionDecoder::new(self);
        let instr = decoder.decode()?;
        Ok((instr, decoder.next_addr()))
    }

    fn version(&self) -> Version {
        self.s.version()
    }
}
