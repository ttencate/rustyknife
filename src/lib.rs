#![recursion_limit="128"] // quick_error barfs otherwise.

mod bits;
mod bytes;
mod decoder;
mod errors;
mod header;
mod globals;
mod instr;
mod mem;
mod obj;
mod platform;
mod version;
mod zmachine;
mod zstring;

#[cfg(test)]
mod tests;

pub use crate::bytes::Address;
pub use crate::instr::Instruction;
pub use crate::mem::Memory;
pub use crate::platform::Platform;
pub use crate::zmachine::ZMachine;
