use crate::bytes::Address;
use crate::decoder::OperandCount;
use crate::instr::{Instruction, Global, Local};
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
        InvalidOperandCount(expected: usize, actual: usize, loc: ErrorLocation) {
            display("invalid operand count: expected {:?} but got {:?} at {:?}",
                    expected, actual, loc)
        }
        InvalidOperandTypes(types: u8, loc: ErrorLocation) {
            display("invalid operand types {:#b} at {:?}", types, loc)
        }
        UnknownOpcode(operand_count: OperandCount, opcode_number: u8, loc: ErrorLocation) {
            display("unknown {:?} opcode {:?} at {:?}", operand_count, opcode_number, loc)
        }
        NotEnoughOperands(instr: Instruction, loc: ErrorLocation) {
            display("not enough arguments to {:?} instruction at {:?}", instr, loc)
        }
        StackEmpty {
            display("attempt to read top of stack while the stack was empty")
        }
        InvalidLocal(local: Local) {
            display("local variable {:?} does not exist", local)
        }
        InvalidGlobal(global: Global) {
            display("global variable {:?} does not exist", global)
        }
        InvalidRoutineHeader(addr: Address) {
            display("invalid routine header at {:}", addr)
        }
    }
}

#[derive(Debug)]
pub struct ErrorLocation {
    pub start_addr: Address,
    pub bytes: Vec<u8>,
}