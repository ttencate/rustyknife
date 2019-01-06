use crate::bytes::{Address, Bytes};
use crate::instr::Global;
use crate::errors::{FormatError, RuntimeError};
use crate::version::Version;

pub struct GlobalsTable<'a> {
    version: Version,
    bytes: &'a mut Bytes,
    base_addr: Address,
}

impl<'a> GlobalsTable<'a> {
    pub fn new(version: Version, bytes: &'a mut Bytes, base_addr: Address) -> Result<GlobalsTable<'a>, FormatError> {
        // It may be legal to have the globals table outside the address range, as long as it's
        // never used. But more likely, this is a bug somewhere.
        bytes.get_u16(base_addr).or(Err(FormatError::GlobalsTableOutOfRange(base_addr)))?;
        Ok(GlobalsTable {
            version,
            bytes,
            base_addr,
        })
    }

    pub fn get(&self, global: Global) -> Result<u16, RuntimeError> {
        self.bytes.get_u16(self.addr(global))
            .or(Err(RuntimeError::InvalidGlobal(global)))
    }

    pub fn set(&mut self, global: Global, val: u16) -> Result<(), RuntimeError> {
        self.bytes.set_u16(self.addr(global), val)
            .or(Err(RuntimeError::InvalidGlobal(global)))
    }

    fn addr(&self, global: Global) -> Address {
        self.base_addr + global.index() * 2
    }
}
