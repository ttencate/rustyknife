#![recursion_limit="128"] // quick_error barfs otherwise.

mod bits;
mod bytes;
mod decoder;
mod errors;
mod instr;
mod mem;
mod obj;
mod zmachine;
mod zstring;

#[cfg(test)]
mod tests;

pub use crate::mem::Memory;
pub use crate::zmachine::ZMachine;
