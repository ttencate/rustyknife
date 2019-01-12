use crate::bytes::{Address, Bytes};
use crate::errors::{FormatError, RuntimeError};
use crate::version::*;
use crate::zstring::ZString;
use std::cell::RefCell;
use std::collections::HashSet;
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

    pub fn words(&self, text: Vec<u8>) -> Result<WordIter, RuntimeError> {
        let split_chars = self.split_chars()?;
        let (entry_length, num_entries) = self.entry_length_and_count()?;
        let entry_table = EntryTable {
            version: self.version,
            bytes: self.bytes.clone(),
            base_addr: self.entry_length_addr()? + 3,
            entry_length: entry_length as usize,
            num_entries: num_entries as usize,
        };
        Ok(WordIter {
            split_chars: split_chars,
            entry_table: entry_table,
            text: text,
            next_idx: 0,
        })
    }

    fn split_chars(&self) -> Result<HashSet<u8>, RuntimeError> {
        // 13.2
        // The table begins with a short header:
        // 
        //   n     list of keyboard input codes   entry-length  number-of-entries
        //  byte  ------n bytes-----------------      byte         2-byte word
        //
        // The keyboard input codes are "word-separators": typically (and under Inform mandatorily)
        // these are the ZSCII codes for full stop, comma and double-quote. Note that a space
        // character (32) should never be a word-separator.
        let n = self.bytes.borrow().get_u8(self.base_addr)? as usize;
        let mut split_chars = HashSet::with_capacity(n);
        for &byte in self.bytes.borrow().get_slice(self.base_addr + 1..self.base_addr + 1 + n)? {
            split_chars.insert(byte);
        }
        Ok(split_chars)
    }

    fn entry_length_addr(&self) -> Result<Address, RuntimeError> {
        let n = self.bytes.borrow().get_u8(self.base_addr)? as usize;
        Ok(self.base_addr + 1 + n)
    }

    fn entry_length_and_count(&self) -> Result<(u8, u16), RuntimeError> {
        // The "entry length" is the length of each word's entry in the dictionary table. (It must
        // be at least 4 in Versions 1 to 3, and at least 6 in later Versions.)
        let addr = self.entry_length_addr()?;
        let entry_length = self.bytes.borrow().get_u8(addr)?;
        let entry_count = self.bytes.borrow().get_u16(addr + 1)?;
        match self.version {
            V1 | V2 | V3 => if entry_length < 4 {
                return Err(RuntimeError::DictionaryTableCorrupt);
            }
        }
        Ok((entry_length, entry_count))
    }
}

#[derive(Debug, Clone)]
struct EntryTable {
    version: Version,
    bytes: Rc<RefCell<Bytes>>,
    base_addr: Address,
    entry_length: usize,
    num_entries: usize,
}

// TODO introduce ZsciiChar type, wrapping u8

impl EntryTable {
    fn find_word(&self, word: &[u8]) -> Result<Option<Address>, RuntimeError> {
        if self.num_entries == 0 {
            return Ok(None)
        }

        // Truncate the word to the dictionary word length so we can compare for equality.
        let word = &word[..std::cmp::min(word.len(), self.decoded_word_len())];

        // Binary search
        let mut left = 0;
        let mut right = self.num_entries - 1;
        while left <= right {
            let mid = (left + right) / 2;
            // Rather than encoding the word into a ZString, which does not have a unique
            // representation, it's both easier and more robust (though slower) to decode each
            // dictionary entry instead.
            let entry_vec = self.decode_entry(mid)?;
            let entry: &[u8] = &entry_vec;
            if entry < word {
                left = mid + 1;
            } else if entry > word {
                right = mid - 1;
            } else { // entry == word
                return Ok(Some(self.entry_addr(mid)));
            }
        }
        Ok(None)
    }

    fn entry_addr(&self, idx: usize) -> Address {
        self.base_addr + self.entry_length * idx
    }

    fn encoded_word_len(&self) -> usize {
        match self.version {
            V1 | V2 | V3 => 4
        }
    }

    fn decoded_word_len(&self) -> usize {
        match self.version {
            V1 | V2 | V3 => 6
        }
    }

    fn decode_entry(&self, idx: usize) -> Result<Vec<u8>, RuntimeError> {
        let addr = self.entry_addr(idx);
        let bytes = self.bytes.borrow();
        let slice = bytes.get_slice(addr..addr + self.encoded_word_len())?.clone();
        let string = ZString::from(slice).decode(self.version, None)?;
        Ok(string.into_bytes())
    }
}

#[derive(Debug, Clone)]
pub struct WordIter {
    split_chars: HashSet<u8>,
    entry_table: EntryTable,
    text: Vec<u8>,
    next_idx: usize,
}

impl WordIter {
    fn is_space_char(&self, byte: u8) -> bool {
        byte == b' '
    }

    fn is_split_char(&self, byte: u8) -> bool {
        self.split_chars.contains(&byte)
    }

    fn is_word_char(&self, byte: u8) -> bool {
        byte != b' ' && !self.is_split_char(byte)
    }

    fn done(&self) -> bool {
        self.next_idx >= self.text.len()
    }
}

impl Iterator for WordIter {
    type Item = Result<WordRef, RuntimeError>;
    fn next(&mut self) -> Option<Result<WordRef, RuntimeError>> {
        // 13.6.1
        // First, the text is broken up into words. Spaces divide up words and are otherwise
        // ignored. Word separators also divide words, but each one of them is considered a word in
        // its own right. Thus, the erratically-spaced text "fred,go fishing" is divided into four
        // words:
        // 
        // fred / , / go / fishing
        while !self.done() && self.is_space_char(self.text[self.next_idx]) {
            self.next_idx += 1;
        }
        if self.done() {
            return None;
        }
        let start_idx = self.next_idx;
        self.next_idx += 1;
        if !self.is_split_char(self.text[start_idx]) {
            while !self.done() && self.is_word_char(self.text[self.next_idx]) {
                self.next_idx += 1;
            }
        }
        // TODO refactor so we only return word slices here, let caller do the lookup
        let word = &self.text[start_idx..self.next_idx];
        match self.entry_table.find_word(word) {
            Ok(addr) => Some(Ok(WordRef {
                addr: addr,
                len: (self.next_idx - start_idx) as u8,
                start_idx: (start_idx + 1) as u8, // + 1 because the text buffer length byte is 0
            })),
            Err(err) => Some(Err(err)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct WordRef {
    addr: Option<Address>,
    start_idx: u8,
    len: u8,
}

impl WordRef {
    pub fn addr(&self) -> Option<Address> {
        self.addr
    }

    pub fn start_idx(&self) -> u8 {
        self.start_idx
    }

    pub fn len(&self) -> u8 {
        self.len
    }
}
