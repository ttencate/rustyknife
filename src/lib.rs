mod bits;
mod bytes;
mod errors;
mod mem;
#[cfg(test)]
mod tests;
mod zstring;

use crate::bits::*;
use crate::bytes::ByteAddress;
use crate::mem::*;
use crate::zstring::{ZString, AbbreviationsTable};
use quick_error::quick_error;
use std::fmt;
use std::fmt::{Display, Formatter};

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

        let opcode_byte = self.next_u8()?;
        let instruction_form = self.instruction_form(opcode_byte)?;
        let operand_count = self.operand_count(instruction_form, opcode_byte)?;
        let opcode_number = self.read_opcode_number(instruction_form, opcode_byte)?;
        let opcode = self.find_opcode(operand_count, opcode_number)?;
        let operand_types = self.read_operand_types(instruction_form, opcode_byte, opcode_number)?;
        let operands = self.read_operands(opcode, operand_count, &operand_types)?;
        let store_var = self.read_store_var(opcode)?;
        let branch = self.read_branch(opcode)?;
        let zstring = self.read_zstring(opcode)?;
        let string = if let Some(zstring) = zstring { Some(zstring.decode(&self.z.abbrs_table())?) } else { None };

        Ok(Instruction {
            opcode: opcode,
            operands: operands,
            store_var: store_var,
            branch: branch,
            string: string,
        })
    }

    fn instruction_form(&self, opcode_byte: u8) -> Result<InstructionForm, RuntimeError> {
        match opcode_byte.bits(BIT6..=BIT7) {
            // 4.3
            // ... If the top two bits of the opcode are $$11 the form is variable; ...
            0b11 => Ok(InstructionForm::Variable),
            // ... if $$10, the form is short.
            0b10 => Ok(InstructionForm::Short),
            0b01 | 0b00 => {
                if opcode_byte == 190 {
                    // If the opcode is 190 ($BE in hexadecimal) and the version is 5 or later, the
                    // form is "extended". ...
                    match self.version {
                        Version::V1 | Version::V2 | Version::V3 =>
                            Err(RuntimeError::InvalidInstruction(opcode_byte, self.loc()))
                    }
                } else {
                    // ... Otherwise, the form is "long".
                    Ok(InstructionForm::Long)
                }
            },
            _ => panic!("two bits can never exceed 0b11")
        }
    }

    fn operand_count(&self, instruction_form: InstructionForm, opcode_byte: u8) -> Result<OperandCount, RuntimeError> {
        match instruction_form {
            // 4.3.1
            // In short form, bits 4 and 5 of the opcode byte give an operand type as above. If
            // this is $11 then the operand count is 0OP; otherwise, 1OP.
            InstructionForm::Short => {
                if opcode_byte.bits(BIT4..=BIT5) == 0b11 {
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
                if !opcode_byte.bit(BIT5) {
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

    fn read_opcode_number(&mut self, instruction_form: InstructionForm, opcode_byte: u8) -> Result<u8, RuntimeError> {
        match instruction_form {
            // 4.3.1
            // In short form, ... In either case the opcode number is given in the bottom 4 bits.
            InstructionForm::Short => Ok(opcode_byte.bits(BIT0..=BIT3)),
            // 4.3.2
            // In long form ... The opcode number is given in the bottom 5 bits.
            InstructionForm::Long => Ok(opcode_byte.bits(BIT0..=BIT4)),
            // 4.3.3
            // In variable form ... The opcode number is given in the bottom 5 bits.
            InstructionForm::Variable => Ok(opcode_byte.bits(BIT0..=BIT4)),
            // 4.3.4
            // In extended form, ... The opcode number is given in a second opcode byte.
            InstructionForm::Extended => Ok(self.next_u8()?),
        }
    }

    fn find_opcode(&self, operand_count: OperandCount, opcode_number: u8) -> Result<Opcode, RuntimeError> {
        Ok(match operand_count {
            OperandCount::Two => match opcode_number {
                0x01 => Opcode::Je,
                0x02 => Opcode::Jl,
                0x03 => Opcode::Jg,
                0x04 => Opcode::DecChk,
                0x05 => Opcode::IncChk,
                0x06 => Opcode::Jin,
                0x07 => Opcode::Test,
                0x08 => Opcode::Or,
                0x09 => Opcode::And,
                0x0a => Opcode::TestAttr,
                0x0b => Opcode::SetAttr,
                0x0c => Opcode::ClearAttr,
                0x0d => Opcode::Store,
                0x0e => Opcode::InsertObj,
                0x0f => Opcode::Loadw,
                0x10 => Opcode::Loadb,
                0x11 => Opcode::GetProp,
                0x12 => Opcode::GetPropAddr,
                0x13 => Opcode::GetNextProp,
                0x14 => Opcode::Add,
                0x15 => Opcode::Sub,
                0x16 => Opcode::Mul,
                0x17 => Opcode::Div,
                0x18 => Opcode::Mod,
                _ => return Err(RuntimeError::UnknownOpcode(operand_count, opcode_number, self.loc()))
            }
            OperandCount::One => match opcode_number {
                0x00 => Opcode::Jz,
                0x01 => Opcode::GetSibling,
                0x02 => Opcode::GetChild,
                0x03 => Opcode::GetParent,
                0x04 => Opcode::GetPropLen,
                0x05 => Opcode::Inc,
                0x06 => Opcode::Dec,
                0x07 => Opcode::PrintAddr,
                0x09 => Opcode::RemoveObj,
                0x0a => Opcode::PrintObj,
                0x0b => Opcode::Ret,
                0x0c => Opcode::Jump,
                0x0d => Opcode::PrintPaddr,
                0x0e => Opcode::Load,
                0x0f => Opcode::Not,
                _ => return Err(RuntimeError::UnknownOpcode(operand_count, opcode_number, self.loc()))
            }
            OperandCount::Zero => match opcode_number {
                0x00 => Opcode::Rtrue,
                0x01 => Opcode::Rfalse,
                0x02 => Opcode::Print,
                0x03 => Opcode::PrintRet,
                0x04 => Opcode::Nop,
                0x05 => Opcode::Save,
                0x06 => Opcode::Restore,
                0x07 => Opcode::Restart,
                0x08 => Opcode::RetPopped,
                0x09 => Opcode::Pop,
                0x0a => Opcode::Quit,
                0x0b => Opcode::NewLine,
                0x0c => Opcode::ShowStatus,
                0x0d => Opcode::Verify,
                _ => return Err(RuntimeError::UnknownOpcode(operand_count, opcode_number, self.loc()))
            }
            OperandCount::Var => match opcode_number {
                0x00 => Opcode::Call,
                0x01 => Opcode::Storew,
                0x02 => Opcode::Storeb,
                0x03 => Opcode::PutProp,
                0x04 => Opcode::Sread,
                0x05 => Opcode::PrintChar,
                0x06 => Opcode::PrintNum,
                0x07 => Opcode::Random,
                0x08 => Opcode::Push,
                0x09 => Opcode::Pull,
                0x0a => Opcode::SplitWindow,
                0x0b => Opcode::SetWindow,
                0x13 => Opcode::OutputStream,
                0x14 => Opcode::InputStream,
                _ => return Err(RuntimeError::UnknownOpcode(operand_count, opcode_number, self.loc()))
            }
        })
    }

    fn read_operand_types(&mut self, instruction_form: InstructionForm, opcode_byte: u8, opcode_number: u8) -> Result<Vec<OperandType>, RuntimeError> {
        // 4.4
        // Next, the types of the operands are specified.
        match instruction_form {
            // 4.4.1
            // In short form, bits 4 and 5 of the opcode give the type.
            InstructionForm::Short => Ok(vec![
                OperandType::from_bits(opcode_byte.bits(BIT4..=BIT5)),
            ]),
            // 4.4.2
            // In long form, bit 6 of the opcode gives the type of the first operand, bit 5 of the
            // second. A value of 0 means a small constant and 1 means a variable. (If a 2OP
            // instruction needs a large constant as operand, then it should be assembled in variable
            // rather than long form.)
            InstructionForm::Long => Ok(vec![
                OperandType::from_bit(opcode_byte.bits(BIT6..=BIT6)),
                OperandType::from_bit(opcode_byte.bits(BIT5..=BIT5)),
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
                    let byte = self.next_u8()?;
                    for &start_bit in &[BIT6, BIT4, BIT2, BIT0] {
                        let operand_type = OperandType::from_bits(byte.bits(start_bit..=start_bit + 1));
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
                }
                Ok(types)
            },
        }
    }

    fn read_operands(&mut self, opcode: Opcode, operand_count: OperandCount, operand_types: &Vec<OperandType>) -> Result<Vec<Operand>, RuntimeError> {
        // 4.5
        // The operands are given next. Operand counts of 0OP, 1OP or 2OP require 0, 1 or 2
        // operands to be given, respectively. If the count is VAR, there must be as many operands
        // as there were types other than 'omitted'.
        let mut operands = Vec::with_capacity(operand_types.len());
        for operand_type in operand_types {
            match operand_type {
                OperandType::LargeConstant => operands.push(Operand::LargeConstant(self.next_u16()?)),
                OperandType::SmallConstant => operands.push(Operand::SmallConstant(self.next_u8()?)),
                OperandType::Variable => operands.push(Operand::Variable(Variable::from_byte(self.next_u8()?))),
                OperandType::Omitted => {}
            }
        }
        if let Some(expected_operand_count) = operand_count.count() {
            let actual_operand_count = operands.len();
            if actual_operand_count != expected_operand_count {
                return Err(RuntimeError::InvalidOperandCount(opcode, expected_operand_count, actual_operand_count, self.loc()));
            }
        }
        Ok(operands)
    }

    fn read_store_var(&mut self, opcode: Opcode) -> Result<Option<Variable>, RuntimeError> {
        // 4.6
        // "Store" instructions return a value: e.g., mul multiplies its two operands together.
        // Such instructions must be followed by a single byte giving the variable number of where
        // to put the result.
        if opcode.has_store() {
            Ok(Some(Variable::from_byte(self.next_u8()?)))
        } else {
            Ok(None)
        }
    }

    fn read_branch(&mut self, opcode: Opcode) -> Result<Option<Branch>, RuntimeError> {
        // 4.7
        // Instructions which test a condition are called "branch" instructions.
        if opcode.has_branch() {
            // The branch information is stored in one or two bytes, indicating what to do with the
            // result of the test.
            let first_byte = self.next_u8()?;

            // If bit 7 of the first byte is 0, a branch occurs when the condition was false; if 1,
            // then branch is on true.
            let branch_on_true = first_byte.bit(BIT7);

            let offset = if first_byte.bit(BIT6) {
                // If bit 6 is set, then the branch occupies 1 byte only, and the "offset" is in
                // the range 0 to 63, given in the bottom 6 bits.
                first_byte.bits(BIT0..=BIT5) as i16
            } else {
                // If bit 6 is clear, then the offset is a signed 14-bit number given in bits 0 to
                // 5 of the first byte followed by all 8 of the second.
                let second_byte = self.next_u8()?;
                let unsigned_offset = (((first_byte.bits(BIT0..=BIT5) as u16) << 8) | second_byte as u16) as i16;
                if unsigned_offset & (1i16 << 13) == 0 {
                    unsigned_offset
                } else {
                    unsigned_offset - (1i16 << 14)
                }
            };

            let target = match offset {
                // 4.7.1
                // An offset of 0 means "return false from the current routine", ...
                0 => BranchTarget::ReturnFalse,
                // ... and 1 means "return true from the current routine".
                1 => BranchTarget::ReturnTrue,
                // 4.7.2
                // Otherwise, a branch moves execution to the instruction at address
                // "Address after branch data + Offset - 2".
                _ => BranchTarget::ToAddress(self.next_addr + (offset - 2))
            };

            Ok(Some(Branch {
                on_true: branch_on_true,
                target: target,
            }))
        } else {
            Ok(None)
        }
    }

    fn read_zstring(&mut self, opcode: Opcode) -> Result<Option<ZString>, RuntimeError> {
        if opcode.has_string() {
            // 4.8
            // Two opcodes, print and print_ret, are followed by a text string. This is stored
            // according to the usual rules: in particular execution continues after the last
            // 2-byte word of text (the one with top bit set).
            Ok(Some(self.next_zstring()?))
        } else {
            Ok(None)
        }
    }

    fn next_u8(&mut self) -> Result<u8, RuntimeError> {
        let b = self.z.mem.bytes().get_u8(self.next_addr)
            .ok_or(RuntimeError::ProgramCounterOutOfRange(self.loc()))?;
        // TODO this might overflow even if we never read the next byte!
        self.next_addr += 1;
        Ok(b)
    }

    fn next_u16(&mut self) -> Result<u16, RuntimeError> {
        let w = self.z.mem.bytes().get_u16(self.next_addr)
            .ok_or(RuntimeError::ProgramCounterOutOfRange(self.loc()))?;
        // TODO this might overflow even if we never read the next byte!
        self.next_addr += 2;
        Ok(w)
    }

    fn next_zstring(&mut self) -> Result<ZString, RuntimeError> {
        let s = self.z.mem.bytes().get_zstring(self.next_addr)
            .ok_or(RuntimeError::ProgramCounterOutOfRange(self.loc()))?;
        // TODO this might overflow even if we never read the next byte!
        self.next_addr += s.len() as i16;
        Ok(s)
    }

    fn loc(&self) -> ErrorLocation {
        ErrorLocation {
            start_addr: self.start_addr,
            bytes: self.z.mem.bytes().get_slice(self.start_addr..self.next_addr).unwrap().to_vec(),
        }
    }

    pub fn next_addr(&self) -> ByteAddress {
        self.next_addr
    }
}

#[derive(Debug)]
struct Instruction {
    opcode: Opcode,
    operands: Vec<Operand>,
    store_var: Option<Variable>,
    branch: Option<Branch>,
    string: Option<String>,
}

// 14. Complete table of opcodes
#[derive(Debug, Clone, Copy)]
pub enum Opcode {
    // Two-operand opcodes 2OP
    Je,
    Jl,
    Jg,
    DecChk,
    IncChk,
    Jin,
    Test,
    Or,
    And,
    TestAttr,
    SetAttr,
    ClearAttr,
    Store,
    InsertObj,
    Loadw,
    Loadb,
    GetProp,
    GetPropAddr,
    GetNextProp,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    // One-operand opcodes 1OP
    Jz,
    GetSibling,
    GetChild,
    GetParent,
    GetPropLen,
    Inc,
    Dec,
    PrintAddr,
    RemoveObj,
    PrintObj,
    Ret,
    Jump,
    PrintPaddr,
    Load,
    Not,
    // Zero-operand opcodes 0OP
    Rtrue,
    Rfalse,
    Print,
    PrintRet,
    Nop,
    Save,
    Restore,
    Restart,
    RetPopped,
    Pop,
    Quit,
    NewLine,
    ShowStatus,
    Verify,
    // Variable-operand opcodes VAR
    Call,
    Storew,
    Storeb,
    PutProp,
    Sread,
    PrintChar,
    PrintNum,
    Random,
    Push,
    Pull,
    SplitWindow,
    SetWindow,
    OutputStream,
    InputStream,
    // Extended opcodes EXT
    // None supported at the moment.
}

impl Opcode {
    fn has_store(&self) -> bool {
        match self {
            Opcode::Or | Opcode::And | Opcode::Loadw | Opcode::Loadb | Opcode::GetProp |
                Opcode::GetPropAddr | Opcode::GetNextProp | Opcode::Add | Opcode::Sub | Opcode::Mul
                | Opcode::Div | Opcode::Mod | Opcode::GetSibling | Opcode::GetChild |
                Opcode::GetParent | Opcode::GetPropLen | Opcode::Load | Opcode::Not | Opcode::Call
                | Opcode::Random => true,
            _ => false,
        }
    }

    fn has_branch(&self) -> bool {
        match self {
            Opcode::Je | Opcode::Jl | Opcode::Jg | Opcode::DecChk | Opcode::IncChk | Opcode::Jin |
                Opcode::Test | Opcode::TestAttr | Opcode::Jz | Opcode::GetSibling |
                Opcode::GetChild | Opcode::GetParent | Opcode::Save | Opcode::Restore |
                Opcode::Verify => true,
            _ => false,
        }
    }

    fn has_string(&self) -> bool {
        match self {
            Opcode::Print | Opcode::PrintRet => true,
            _ => false,
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

#[derive(Debug, Clone, Eq, PartialEq)]
enum Variable {
    TopOfStack,
    Local(u8),
    Global(u8),
}

impl Variable {
    fn from_byte(byte: u8) -> Variable {
        // 4.2.2
        match byte {
            // Variable number $00 refers to the top of the stack, ...
            0 => Variable::TopOfStack,
            // ... $01 to $0f mean the local variables of the current routine ...
            0x01..=0x0f => Variable::Local(byte),
            // ... and $10 to $ff mean the global variables.
            _ => Variable::Global(byte),
        }
    }
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
pub enum OperandCount {
    Zero,
    One,
    Two,
    Var,
}

impl OperandCount {
    fn count(&self) -> Option<usize> {
        match self {
            OperandCount::Zero => Some(0),
            OperandCount::One => Some(1),
            OperandCount::Two => Some(2),
            OperandCount::Var => None,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
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

type VarOperands = Vec<Operand>;

#[derive(Debug)]
struct Branch {
    on_true: bool,
    target: BranchTarget,
}

#[derive(Debug)]
enum BranchTarget {
    ReturnFalse,
    ReturnTrue,
    ToAddress(ByteAddress),
}

pub struct ZMachine<'a> {
    story_file: &'a Memory,
    mem: Memory,
    pc: ByteAddress,
}

impl<'a> ZMachine<'a> {
    pub fn new(story_file: &Memory) -> ZMachine {
        let mut z = ZMachine {
            story_file: story_file,
            mem: Memory::with_size(story_file.bytes().len()),
            pc: ByteAddress(0),
        };
        z.restart();
        z
    }

    pub fn restart(&mut self) {
        self.mem.bytes_mut().copy_from(&self.story_file.bytes());
        self.pc = self.mem.initial_program_counter();
        self.reset();
    }

    pub fn step(&mut self) -> Result<(), RuntimeError> {
        let (instr, next_pc) = self.decode_next_instr()?;
        println!("{:?}", instr);
        self.pc = next_pc;
        Ok(())
    }

    fn reset(&mut self) {
        self.mem.set_flag(STATUS_LINE_NOT_AVAILABLE, false);
        self.mem.set_flag(SCREEN_SPLITTING_AVAILABLE, true);
        self.mem.set_flag(VARIABLE_PITCH_FONT_DEFAULT, true);
        self.mem.set_flag(TRANSCRIPTING_ON, false);
        if self.mem.version() >= Version::V3 {
            self.mem.set_flag(FORCE_FIXED_PITCH_FONT, false);
        }

        // Interpreter number
        // 11.1.3
        // Infocom used the interpreter numbers:
        //
        //    1   DECSystem-20     5   Atari ST           9   Apple IIc
        //    2   Apple IIe        6   IBM PC            10   Apple IIgs
        //    3   Macintosh        7   Commodore 128     11   Tandy Color
        //    4   Amiga            8   Commodore 64
        *self.mem.bytes_mut().get_u8_mut(ByteAddress(0x001e)).unwrap() = 6;

        // Interpreter version
        // 11.1.3.1
        // Interpreter versions are conventionally ASCII codes for upper-case letters in Versions 4
        // and 5 (note that Infocom's Version 6 interpreters just store numbers here).
        *self.mem.bytes_mut().get_u8_mut(ByteAddress(0x001f)).unwrap() = b'A';
    }

    fn decode_next_instr(&self) -> Result<(Instruction, ByteAddress), RuntimeError> {
        let mut decoder = InstructionDecoder::new(self);
        let instr = decoder.decode()?;
        Ok((instr, decoder.next_addr()))
    }

    fn version(&self) -> Version {
        self.mem.version()
    }

    fn abbrs_table(&self) -> AbbreviationsTable {
        AbbreviationsTable()
    }
}

impl<'a> Display for ZMachine<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "pc: {:}", self.pc)
    }
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
        InvalidOperandCount(opcode: Opcode, expected: usize, actual: usize, loc: ErrorLocation) {
            display("invalid operand count for opcode {:?}: expected {:?} but got {:?} at {:?}",
                    opcode, expected, actual, loc)
        }
        InvalidOperandTypes(types: u8, loc: ErrorLocation) {
            display("invalid operand types {:#b} at {:?}", types, loc)
        }
        UnknownOpcode(operand_count: OperandCount, opcode_number: u8, loc: ErrorLocation) {
            display("unknown {:?} opcode {:?} at {:?}", operand_count, opcode_number, loc)
        }
    }
}

#[derive(Debug)]
pub struct ErrorLocation {
    start_addr: ByteAddress,
    bytes: Vec<u8>,
}
