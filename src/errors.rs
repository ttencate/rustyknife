use crate::decoder::OperandCount;
use crate::instr::Opcode;
use crate::bytes::ByteAddress;
use quick_error::quick_error;

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
    pub start_addr: ByteAddress,
    pub bytes: Vec<u8>,
}
