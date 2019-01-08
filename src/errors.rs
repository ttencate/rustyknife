use crate::bytes::Address;
use crate::decoder::OperandCount;
use crate::instr::{Global, Local};
use crate::obj::{Attribute, Object, Property};
use quick_error::quick_error;

quick_error! {
    #[derive(Debug)]
    pub enum FormatError {
        TooSmall(size: usize) {
            display("story file is too small ({} bytes)", size)
        }
        TooBig(size: usize, max_size: usize) {
            display("story file is too big ({} > {} bytes)", size, max_size)
        }
        MemoryOverlap(static_memory_base: Address, high_memory_base: Address) {
            display("high memory may not overlap with dynamic memory: {} < {}", static_memory_base, high_memory_base)
        }
        GlobalsTableOutOfRange(globals_table: Address) {
            display("globals table is outside memory: {}", globals_table)
        }
        DictionaryTableOutOfRange(dictionary_table: Address) {
            display("dictionary table is outside memory: {}", dictionary_table)
        }
        UnsupportedVersion(version_byte: u8) {
            display("story file has version {} which is unsupported", version_byte)
        }
        InvalidFileLength(file_length: usize, num_bytes: usize) {
            display("file length {} indicated in header is more than number of bytes {} in the file",
                    file_length, num_bytes)
        }
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
        InvalidOperandTypes(types: u8, loc: ErrorLocation) {
            display("invalid operand types {:#b} at {:?}", types, loc)
        }
        UnknownOpcode(operand_count: OperandCount, opcode_number: u8, loc: ErrorLocation) {
            display("unknown {:?} opcode {:?} at {:?}", operand_count, opcode_number, loc)
        }
        NotEnoughOperands(idx: usize, num_operands: usize) {
            display("cannot get operand {} of {}", idx, num_operands)
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
        InvalidVariable(var: u16) {
            display("invalid indirect variable reference {}", var)
        }
        InvalidRoutineHeader(addr: Address) {
            display("invalid routine header at {}", addr)
        }
        StackOverflow {
            display("stack overflow")
        }
        CallStackOverflow {
            display("call stack overflow")
        }
        StackUnderflow {
            display("stack underflow")
        }
        CallStackUnderflow {
            display("call stack underflow")
        }
        ReadOnlyMemory(addr: Address) {
            display("cannot write to read-only memory at {}", addr)
        }
        AddressOutOfRange(addr: Address) {
            display("address {} out of range", addr)
        }
        InvalidObject(obj: Object) {
            display("no such object {:?}", obj)
        }
        InvalidProperty(prop: Property) {
            display("invalid property number {:?}", prop)
        }
        InvalidAttribute(attr: Attribute) {
            display("invalid attribute number {:?}", attr)
        }
        PropertyNotFound(obj: Object, prop: Property) {
            display("property {:?} not found on object {:?}", prop, obj)
        }
        ObjectCorrupt(obj: Object) {
            display("object {:?} is corrupt", obj)
        }
        InvalidPropertySize(prop_size: u8) {
            display("expected property size 1 or 2, but was {}", prop_size)
        }
        AbbreviationInAbbreviationsTable(idx: usize) {
            display("string {} in the abbreviations table contained an abbreviation", idx)
        }
        InvalidCharacterCode(char_code: u16) {
            display("attempt to decode invalid ZSCII character code {}", char_code)
        }
        DivisionByZero {
            display("division by zero")
        }
        InvalidPropertyAddress(addr: Address) {
            display("invalid property address {}", addr)
        }
        BufferTooSmall(len: u16, min_len: u16) {
            display("buffer too small: {} < {}", len, min_len)
        }
        DictionaryTableCorrupt {
            display("dictionary table corrupt")
        }
    }
}

#[derive(Debug)]
pub struct ErrorLocation {
    pub start_addr: Address,
    pub bytes: Vec<u8>,
}
