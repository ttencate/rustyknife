use crate::bytes::Address;
use crate::instr::Instruction;

pub trait Platform {

    fn print(&mut self, string: &str);

    fn next_instr(&mut self, _pc: Address, _call_stack_depth: usize, _instr: &Instruction) {
    }
}
