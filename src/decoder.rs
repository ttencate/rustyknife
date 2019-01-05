use crate::errors::{ErrorLocation, RuntimeError};
use crate::bits::*;
use crate::bytes::Address;
use crate::instr::*;
use crate::mem::*;

pub struct InstructionDecoder<'a> {
    mem: &'a Memory,
    start_addr: Address,
    next_addr: Address,
}

impl<'a> InstructionDecoder<'a> {
    pub fn new(mem: &'a Memory, pc: Address) -> InstructionDecoder<'a> {
        InstructionDecoder {
            mem: mem,
            start_addr: pc,
            next_addr: pc,
        }
    }

    pub fn decode(&mut self) -> Result<(Instruction, ErrorLocation), RuntimeError> {
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
        let operand_types = self.read_operand_types(instruction_form, opcode_byte, opcode_number)?;

        let instr = match operand_count {
            OperandCount::Two => {
                let left = self.read_operand(operand_types[0])?;
                let right = self.read_operand(operand_types[1])?;
                match opcode_number {
                    0x01 => Instruction::Je(left, right, self.read_branch()?),
                    0x02 => Instruction::Jl(left, right, self.read_branch()?),
                    0x03 => Instruction::Jg(left, right, self.read_branch()?),
                    0x04 => Instruction::DecChk(left, right, self.read_branch()?),
                    0x05 => Instruction::IncChk(left, right, self.read_branch()?),
                    0x06 => Instruction::Jin(left, right, self.read_branch()?),
                    0x07 => Instruction::Test(left, right, self.read_branch()?),
                    0x08 => Instruction::Or(left, right, self.read_store_var()?),
                    0x09 => Instruction::And(left, right, self.read_store_var()?),
                    0x0a => Instruction::TestAttr(left, right, self.read_branch()?),
                    0x0b => Instruction::SetAttr(left, right),
                    0x0c => Instruction::ClearAttr(left, right),
                    0x0d => Instruction::Store(left, right),
                    0x0e => Instruction::InsertObj(left, right),
                    0x0f => Instruction::Loadw(left, right, self.read_store_var()?),
                    0x10 => Instruction::Loadb(left, right, self.read_store_var()?),
                    0x11 => Instruction::GetProp(left, right, self.read_store_var()?),
                    0x12 => Instruction::GetPropAddr(left, right, self.read_store_var()?),
                    0x13 => Instruction::GetNextProp(left, right, self.read_store_var()?),
                    0x14 => Instruction::Add(left, right, self.read_store_var()?),
                    0x15 => Instruction::Sub(left, right, self.read_store_var()?),
                    0x16 => Instruction::Mul(left, right, self.read_store_var()?),
                    0x17 => Instruction::Div(left, right, self.read_store_var()?),
                    0x18 => Instruction::Mod(left, right, self.read_store_var()?),
                    _ => return Err(RuntimeError::UnknownOpcode(operand_count, opcode_number, self.loc()))
                }
            }
            OperandCount::One => {
                let operand = self.read_operand(operand_types[0])?;
                match opcode_number {
                    0x00 => Instruction::Jz(operand, self.read_branch()?),
                    // For these two, we are relying on left-to-right evaluation order of
                    // arguments. According to https://github.com/rust-lang/rust/issues/15300 this
                    // should be safe; it's just not documented.
                    0x01 => Instruction::GetSibling(operand, self.read_store_var()?, self.read_branch()?),
                    0x02 => Instruction::GetChild(operand, self.read_store_var()?, self.read_branch()?),
                    0x03 => Instruction::GetParent(operand, self.read_store_var()?),
                    0x04 => Instruction::GetPropLen(operand, self.read_store_var()?),
                    0x05 => Instruction::Inc(operand),
                    0x06 => Instruction::Dec(operand),
                    0x07 => Instruction::PrintAddr(operand),
                    0x09 => Instruction::RemoveObj(operand),
                    0x0a => Instruction::PrintObj(operand),
                    0x0b => Instruction::Ret(operand),
                    0x0c => Instruction::Jump(operand),
                    0x0d => Instruction::PrintPaddr(operand),
                    0x0e => Instruction::Load(operand, self.read_store_var()?),
                    0x0f => Instruction::Not(operand, self.read_store_var()?),
                    _ => return Err(RuntimeError::UnknownOpcode(operand_count, opcode_number, self.loc()))
                }
            }
            OperandCount::Zero => {
                match opcode_number {
                    0x00 => Instruction::Rtrue(),
                    0x01 => Instruction::Rfalse(),
                    0x02 => Instruction::Print(self.read_string()?),
                    0x03 => Instruction::PrintRet(self.read_string()?),
                    0x04 => Instruction::Nop(),
                    0x05 => Instruction::Save(self.read_branch()?),
                    0x06 => Instruction::Restore(self.read_branch()?),
                    0x07 => Instruction::Restart(),
                    0x08 => Instruction::RetPopped(),
                    0x09 => Instruction::Pop(),
                    0x0a => Instruction::Quit(),
                    0x0b => Instruction::NewLine(),
                    0x0c => Instruction::ShowStatus(),
                    0x0d => Instruction::Verify(self.read_branch()?),
                    _ => return Err(RuntimeError::UnknownOpcode(operand_count, opcode_number, self.loc()))
                }
            }
            OperandCount::Var => {
                let var_operands = self.read_var_operands(operand_count, &operand_types)?;
                match opcode_number {
                    0x00 => Instruction::Call(var_operands, self.read_store_var()?),
                    0x01 => Instruction::Storew(var_operands),
                    0x02 => Instruction::Storeb(var_operands),
                    0x03 => Instruction::PutProp(var_operands),
                    0x04 => Instruction::Sread(var_operands),
                    0x05 => Instruction::PrintChar(var_operands),
                    0x06 => Instruction::PrintNum(var_operands),
                    0x07 => Instruction::Random(var_operands, self.read_store_var()?),
                    0x08 => Instruction::Push(var_operands),
                    0x09 => Instruction::Pull(var_operands),
                    0x0a => Instruction::SplitWindow(var_operands),
                    0x0b => Instruction::SetWindow(var_operands),
                    0x13 => Instruction::OutputStream(var_operands),
                    0x14 => Instruction::InputStream(var_operands),
                    _ => return Err(RuntimeError::UnknownOpcode(operand_count, opcode_number, self.loc()))
                }
            }
        };
        Ok((instr, self.loc()))
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
                    match self.mem.version() {
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
                for _ in 0..num_bytes {
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

    fn read_operand(&mut self, operand_type: OperandType) -> Result<Operand, RuntimeError> {
        Ok(match operand_type {
            OperandType::LargeConstant => Operand::LargeConstant(self.next_u16()?),
            OperandType::SmallConstant => Operand::SmallConstant(self.next_u8()?),
            OperandType::Variable => Operand::Variable(Variable::from_byte(self.next_u8()?)),
            OperandType::Omitted => panic!("cannot read an omitted operand")
        })
    }

    fn read_var_operands(&mut self, operand_count: OperandCount, operand_types: &Vec<OperandType>) -> Result<VarOperands, RuntimeError> {
        // 4.5
        // The operands are given next. Operand counts of 0OP, 1OP or 2OP require 0, 1 or 2
        // operands to be given, respectively. If the count is VAR, there must be as many operands
        // as there were types other than 'omitted'.
        let mut operands = Vec::with_capacity(operand_types.len());
        for &operand_type in operand_types {
            if operand_type != OperandType::Omitted {
                operands.push(self.read_operand(operand_type)?);
            }
        }
        if let Some(expected_operand_count) = operand_count.count() {
            let actual_operand_count = operands.len();
            if actual_operand_count != expected_operand_count {
                return Err(RuntimeError::InvalidOperandCount(expected_operand_count, actual_operand_count, self.loc()));
            }
        }
        Ok(VarOperands::from(operands))
    }

    fn read_store_var(&mut self) -> Result<Variable, RuntimeError> {
        // 4.6
        // "Store" instructions return a value: e.g., mul multiplies its two operands together.
        // Such instructions must be followed by a single byte giving the variable number of where
        // to put the result.
        Ok(Variable::from_byte(self.next_u8()?))
    }

    fn read_branch(&mut self) -> Result<Branch, RuntimeError> {
        // 4.7
        // Instructions which test a condition are called "branch" instructions.

        // The branch information is stored in one or two bytes, indicating what to do with the
        // result of the test.
        let first_byte = self.next_u8()?;

        // If bit 7 of the first byte is 0, a branch occurs when the condition was false; if 1,
        // then branch is on true.
        let cond = first_byte.bit(BIT7);

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
            _ => BranchTarget::ToAddress(self.next_addr + (offset as i32 - 2))
        };

        Ok(Branch::new(cond, target))
    }

    fn read_string(&mut self) -> Result<String, RuntimeError> {
        // 4.8
        // Two opcodes, print and print_ret, are followed by a text string. This is stored
        // according to the usual rules: in particular execution continues after the last
        // 2-byte word of text (the one with top bit set).
        self.next_string()
    }

    fn next_u8(&mut self) -> Result<u8, RuntimeError> {
        let b = self.mem.bytes().get_u8(self.next_addr)
            .or(Err(RuntimeError::ProgramCounterOutOfRange(self.loc())))?;
        self.next_addr += 1;
        Ok(b)
    }

    fn next_u16(&mut self) -> Result<u16, RuntimeError> {
        let w = self.mem.bytes().get_u16(self.next_addr)
            .or(Err(RuntimeError::ProgramCounterOutOfRange(self.loc())))?;
        self.next_addr += 2;
        Ok(w)
    }

    fn next_string(&mut self) -> Result<String, RuntimeError> {
        let zstring = self.mem.bytes().get_zstring(self.next_addr)
            .or(Err(RuntimeError::ProgramCounterOutOfRange(self.loc())))?;
        self.next_addr += zstring.len();
        zstring.decode(self.mem.version(), &self.mem.abbrs_table())
    }

    fn loc(&self) -> ErrorLocation {
        ErrorLocation {
            start_addr: self.start_addr,
            bytes: self.mem.bytes().get_slice(self.start_addr..self.next_addr).unwrap().to_vec(),
        }
    }

    pub fn next_addr(&self) -> Address {
        self.next_addr
    }
}

// 4.2
// There are four 'types' of operand.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum OperandType {
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

// 4.3
// Each instruction has a form (long, short, extended or variable) ...
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum InstructionForm {
    Long,
    Short,
    #[allow(dead_code)] // Only used in v5 and above, but partially implemented already.
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
