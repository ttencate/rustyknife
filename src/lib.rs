// TODO Split this crate into two: one lib and one bin
#![recursion_limit="128"] // quick_error barfs otherwise.

mod bits;
mod bytes;
mod decoder;
mod dict;
mod errors;
mod header;
mod globals;
mod instr;
mod mem;
mod obj;
mod platform;
mod random;
mod version;
mod zmachine;
mod zstring;

pub use crate::bytes::Address;
pub use crate::instr::Instruction;
pub use crate::mem::Memory;
pub use crate::platform::{InterpreterMetadata, Platform, Progress, StatusLine};
pub use crate::zmachine::ZMachine;
