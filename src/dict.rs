use crate::bytes::{Address, Bytes};
use crate::errors::{FormatError, RuntimeError};
use crate::version::Version;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct DictionaryTable {
    version: Version,
    bytes: Rc<RefCell<Bytes>>,
    base_addr: Address,
}

impl DictionaryTable {
    pub fn new(version: Version, bytes: Rc<RefCell<Bytes>>, base_addr: Address) -> Result<Self, FormatError> {
        // It may be legal to have the dictionary table outside the address range, as long as it's
        // never used. But more likely, this is a bug somewhere.
        bytes.borrow().get_u16(base_addr).or(Err(FormatError::DictionaryTableOutOfRange(base_addr)))?;
        Ok(DictionaryTable {
            version: version,
            bytes: bytes,
            base_addr: base_addr,
        })
    }

    pub fn words(&self, text: String) -> WordIter {
        WordIter {} // TODO
    }
}

#[derive(Debug, Clone)]
pub struct Word {
    addr: Address,
    len: u8,
    start_idx: u8,
}

impl Word {
    pub fn addr(&self) -> Address {
        self.addr
    }

    pub fn len(&self) -> u8 {
        self.len
    }

    pub fn start_idx(&self) -> u8 {
        self.start_idx
    }
}

#[derive(Debug, Clone)]
pub struct WordIter {
}

impl Iterator for WordIter {
    type Item = Option<Word>;
    fn next(&mut self) -> Option<Option<Word>> {
        None // TODO
    }
}
