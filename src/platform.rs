use crate::bytes::Address;
use crate::instr::Instruction;

pub struct InterpreterMetadata {
    pub interpreter_number: u8,
    pub interpreter_version: u8,
    pub standard_version_major: u8,
    pub standard_version_minor: u8,
}

pub trait Platform {
    fn interpreter_metadata(&self) -> InterpreterMetadata {
        InterpreterMetadata {
            interpreter_number: 6, // IBM PC
            interpreter_version: b'A', // traditionally uses upper-case letters
            standard_version_major: 1,
            standard_version_minor: 1,
        }
    }

    fn print(&mut self, string: &str);

    fn next_instr(&mut self, _pc: Address, _call_stack_depth: usize, _instr: &Instruction) {
    }
}
