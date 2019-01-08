use crate::bits::*;
use crate::bytes::{Address, Bytes};
use crate::errors::{FormatError, RuntimeError};
use crate::version::*;
use std::cell::RefCell;
use std::rc::Rc;

pub struct ZString(Vec<u8>);

impl From<&[u8]> for ZString {
    fn from(bytes: &[u8]) -> ZString {
        ZString(bytes.to_vec())
    }
}

impl ZString {
    pub fn len(&self) -> usize {
        self.0.len()
    }

    fn num_zchars(&self) -> usize {
        self.0.len() * 3 / 2
    }

    // TODO make this a method on AbbreviationsTable instead?
    pub fn decode(&self, version: Version, abbrs_table: &AbbreviationsTable) -> Result<String, RuntimeError> {
        ZStringDecoder::new(version, Some(abbrs_table)).decode(self)
    }
}

#[derive(Debug, Clone)]
pub struct AbbreviationsTable {
    version: Version,
    bytes: Rc<RefCell<Bytes>>,
    base_addr: Address,
}

impl AbbreviationsTable {
    pub fn new(version: Version, bytes: Rc<RefCell<Bytes>>, base_addr: Address) -> Result<AbbreviationsTable, FormatError> {
        // TODO check that the address is in range
        Ok(AbbreviationsTable {
            version: version,
            bytes: bytes,
            base_addr: base_addr,
        })
    }

    pub fn get_zstring(&self, idx: usize) -> Result<ZString, RuntimeError> {
        // 3.3
        // If z is the first Z-character (1, 2 or 3) and x the subsequent one, then the interpreter
        // must look up entry 32(z-1)+x in the abbreviations table and print the string at that
        // word address.
        let addr = Address::from_word_address(self.bytes.borrow().get_u16(self.base_addr + 2 * idx)?);
        self.bytes.borrow().get_zstring(addr)
    }
}

#[derive(Debug, Clone, Copy)]
struct ZChar(u8);

struct ZStringDecoder<'a> {
    version: Version,
    abbrs_table: Option<&'a AbbreviationsTable>,
}

impl<'a> ZStringDecoder<'a> {
    fn new(version: Version, abbrs_table: Option<&'a AbbreviationsTable>) -> ZStringDecoder<'a> {
        ZStringDecoder {
            version: version,
            abbrs_table: abbrs_table,
        }
    }

    fn decode(&self, zstring: &ZString) -> Result<String, RuntimeError> {
        // 3.2.1
        // There are three 'alphabets', A0 (lower case), A1 (upper case) and A2 (punctuation)
        // and during printing one of these is current at any given time. Initially A0 is
        // current. The meaning of a Z-character may depend on which alphabet is current.
        let mut cur_alphabet = Alphabet::A0;

        let mut out = String::with_capacity(zstring.num_zchars());
        let mut iter = ZCharIterator::new(zstring);
        while let Some(zchar) = iter.next() {
            match (self.version, zchar.0, cur_alphabet) {
                // 3.2.2
                // In Versions 1 and 2, ... The Z-characters 2 and 3 are called 'shift'
                // characters and change the alphabet for the next character only. The new
                // alphabet depends on what the current one is:
                // 
                //              from A0  from A1  from A2
                //   Z-char 2      A1       A2       A0
                //   Z-char 3      A2       A0       A1
                (V1, 2, _) | (V2, 2, _) => {
                    cur_alphabet = cur_alphabet.next();
                }
                (V1, 3, _) | (V2, 3, _) => {
                    cur_alphabet = cur_alphabet.prev();
                }

                // 3.2.3
                // In Versions 3 and later, the current alphabet is always A0 unless changed for 1
                // character only: Z-characters 4 and 5 are shift characters. Thus 4 means "the
                // next character is in A1" and 5 means "the next is in A2". There are no shift
                // lock characters.
                (V3, 4, _) => {
                    cur_alphabet = Alphabet::A1;
                }
                (V3, 5, _) => {
                    cur_alphabet = Alphabet::A2;
                }

                // 3.3
                // In Versions 3 and later, Z-characters 1, 2 and 3 represent abbreviations, sometimes
                // also called 'synonyms' (for traditional reasons): the next Z-character indicates
                // which abbreviation string to print. If z is the first Z-character (1, 2 or 3) and x
                // the subsequent one, then the interpreter must look up entry 32(z-1)+x in the
                // abbreviations table and print the string at that word address. In Version 2,
                // Z-character 1 has this effect (but 2 and 3 do not, so there are only 32
                // abbreviations).
                (V3, 1, _) | (V3, 2, _) | (V3, 3, _) | (V2, 1, _)=> {
                    if let Some(next_char) = iter.next() {
                        out.push_str(&self.abbreviation(32 * (zchar.0 as usize - 1) + next_char.0 as usize)?);
                    }
                }

                // 3.4
                // Z-character 6 from A2 means that the two subsequent Z-characters specify a ten-bit
                // ZSCII character code: the next Z-character gives the top 5 bits and the one after
                // the bottom 5.
                (_, 6, Alphabet::A2) => {
                    // 3.6.1
                    // It is legal for the string to end while a multi-Z-character construction is
                    // incomplete: for instance, after only the top half of an ASCII value has been
                    // given. The partial construction is simply ignored. (This can happen in
                    // printing dictionary words which have been guillotined to the dictionary
                    // resolution of 6 or 9 Z-characters.)
                    if let Some(top) = iter.next() {
                        if let Some(bottom) = iter.next() {
                            if let Some(c) = zscii((top.0 as u16) << 5 | bottom.0 as u16)? {
                                out.push(c);
                            }
                        }
                    }
                    if self.version >= V3 {
                        cur_alphabet = Alphabet::A0;
                    }
                }

                // 3.5.1
                // The Z-character 0 is printed as a space (ZSCII 32).
                (_, 0, _) => {
                    out.push(' ');
                }

                // 3.5.2
                // In Version 1, Z-character 1 is printed as a new-line (ZSCII 13).
                (V1, 1, _) => {
                    out.push('\n');
                }

                // 3.5
                // The remaining Z-characters are translated into ZSCII character codes using the
                // "alphabet table".
                _ => {
                    out.push(cur_alphabet.get(zchar.0, self.version));
                    // The spec is unclear about what happens to the alphabet shift in v3 or later
                    // if it's not immediately followed by an alphabet table character. The
                    // simplest is to just let the shift remain in effect until an actual alphabet
                    // table character is encountered.
                    if self.version >= V3 {
                        cur_alphabet = Alphabet::A0;
                    }
                }
            }
        }
        Ok(out)
    }

    fn abbreviation(&self, idx: usize) -> Result<String, RuntimeError> {
        if let Some(abbrs_table) = self.abbrs_table {
            let zstring = abbrs_table.get_zstring(idx)?;
            // 3.3.1
            // Abbreviation string-printing follows all the rules of this section except that an
            // abbreviation string must not itself use abbreviations and must not end with an
            // incomplete multi-Z-character construction (see S 3.6.1 below).
            ZStringDecoder::new(self.version, None).decode(&zstring)
        } else {
            Err(RuntimeError::AbbreviationInAbbreviationsTable(idx))
        }
    }
}

pub fn zscii(idx: u16) -> Result<Option<char>, RuntimeError> {
    // 3.8
    // The character set of the Z-machine is called ZSCII (Zork Standard Code for Information
    // Interchange; pronounced to rhyme with "xyzzy"). ZSCII codes are 10-bit unsigned values
    // between 0 and 1023. Story files may only legally use the values which are defined below.
    // Note that some values are defined only for input and some only for output.
    match idx {
        // 3.8.2.1
        // ZSCII code 0 ("null") is defined for output but has no effect in any output stream.
        // (It is also used as a value meaning "no character" when reporting terminating
        // character codes, but is not formally defined for input.)
        0 => Ok(None),
        // 3.8.2.5
        // ZSCII code 13 ("carriage return") is defined for input and output.
        13 => Ok(Some('\n')),
        // 3.8.3
        // ZSCII codes between 32 ("space") and 126 ("tilde") are defined for input and output,
        // and agree with standard ASCII (as well as all of the ISO 8859 character sets and
        // Unicode).
        32..=126 => Ok(Some(idx as u8 as char)),
        // 3.8.5
        // The block of codes between 155 and 251 are the "extra characters" and are used
        // differently by different story files. Some will need accented Latin characters (such
        // as French E-acute), others unusual punctuation (Spanish question mark), others new
        // alphabets (Cyrillic or Hebrew); still others may want dingbat characters,
        // mathematical or musical symbols, and so on.
        155..=251 => Ok(Some(DEFAULT_UNICODE_TABLE[idx as usize - 155])),
        _ => Err(RuntimeError::InvalidCharacterCode(idx)),
    }
}

// Table 1: default Unicode translations (see S 3.8.5.3)
const DEFAULT_UNICODE_TABLE: &[char] = &[
    'ä', 'ö', 'ü', 'Ä', 'Ö', 'Ü', 'ß', '»', '«', 'ë', 'ï', 'ÿ', 'Ë', 'Ï', 'á', 'é', 'í', 'ó', 'ú',
    'ý', 'Á', 'É', 'Í', 'Ó', 'Ú', 'Ý', 'à', 'è', 'ì', 'ò', 'ù', 'À', 'È', 'Ì', 'Ò', 'Ù', 'â', 'ê',
    'î', 'ô', 'û', 'Â', 'Ê', 'Î', 'Ô', 'Û', 'å', 'Å', 'ø', 'Ø', 'ã', 'ñ', 'õ', 'Ã', 'Ñ', 'Õ', 'æ',
    'Æ', 'ç', 'Ç', 'þ', 'ð', 'Þ', 'Ð', '£', 'œ', 'Œ', '¡', '¿'
];

struct ZCharIterator<'a> {
    data: std::slice::Iter<'a, u8>,
    chars: [u8; 3],
    next_char: usize,
}

impl<'a> ZCharIterator<'a> {
    fn new(zs: &'a ZString) -> ZCharIterator<'a> {
        ZCharIterator { data: zs.0.iter(), chars: [0; 3], next_char: 0 }
    }
}

impl<'a> Iterator for ZCharIterator<'a> {
    type Item = ZChar;
    fn next(&mut self) -> Option<ZChar> {
        // 3.2
        // Text in memory consists of a sequence of 2-byte words. Each word is divided into three
        // 5-bit 'Z-characters', plus 1 bit left over, arranged as
        // 
        //    --first byte-------   --second byte---
        //    7    6 5 4 3 2  1 0   7 6 5  4 3 2 1 0
        //    bit  --first--  --second---  --third--
        // 
        // The bit is set only on the last 2-byte word of the text, and so marks the end.
        if self.next_char == 0 {
            let fst = self.data.next()?;
            let snd = self.data.next()?;
            self.chars[0] = fst.bits(BIT2..=BIT6);
            self.chars[1] = fst.bits(BIT0..=BIT1) << 3 | snd.bits(BIT5..=BIT7);
            self.chars[2] = snd.bits(BIT0..=BIT4);
        }
        let zchar = ZChar(self.chars[self.next_char]);
        self.next_char = (self.next_char + 1) % 3;
        Some(zchar)
    }
}

#[derive(Debug, Clone, Copy)]
enum Alphabet {
    A0,
    A1,
    A2,
}

impl Alphabet {
    fn next(self) -> Alphabet {
        match self {
            Alphabet::A0 => Alphabet::A1,
            Alphabet::A1 => Alphabet::A2,
            Alphabet::A2 => Alphabet::A0,
        }
    }

    fn prev(self) -> Alphabet {
        match self {
            Alphabet::A0 => Alphabet::A2,
            Alphabet::A1 => Alphabet::A0,
            Alphabet::A2 => Alphabet::A1,
        }
    }

    fn get(self, zchar: u8, version: Version) -> char {
        // 3.5.3
        // In Versions 2 to 4, the alphabet table for converting Z-characters into ZSCII character codes is
        // as follows:
        // 
        //    Z-char 6789abcdef0123456789abcdef
        // current   --------------------------
        //   A0      abcdefghijklmnopqrstuvwxyz
        //   A1      ABCDEFGHIJKLMNOPQRSTUVWXYZ
        //   A2       ^0123456789.,!?_#'"/\-:()
        //           --------------------------
        //
        // (Character 6 in A2 is printed as a space here, but is not translated using the alphabet table:
        // see S 3.4 above. Character 7 in A2, written here as a circumflex ^, is a new-line.) For example,
        // in alphabet A1 the Z-character 12 is translated as a capital G (ZSCII character code 71).
        const A0: &[char; 32] = &[
            ' ', ' ', ' ', ' ', ' ', ' ', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j',
            'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z'
        ];
        const A1: &[char; 32] = &[
            ' ', ' ', ' ', ' ', ' ', ' ', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J',
            'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z'
        ];
        const A2: &[char; 32] = &[
            ' ', ' ', ' ', ' ', ' ', ' ', ' ', '\n', '0', '1', '2', '3', '4', '5', '6', '7',
            '8', '9', '.', ',', '!', '?', '_', '#', '\'', '"', '/', '\\', '-', ':', '(', ')'
        ];

        // 3.5.4
        // Version 1 has a slightly different A2 row in its alphabet table (new-line is not needed, making
        // room for the < character):
        // 
        //           6789abcdef0123456789abcdef
        //           --------------------------
        //   A2       0123456789.,!?_#'"/\<-:()
        //           --------------------------
        const A2_V1: &[char; 32] = &[
            ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '1', '2', '3', '4', '5', '6', '7', '8',
            '9', '.', ',', '!', '?', '_', '#', '\'', '"', '/', '\\', '<', '-', ':', '(', ')'
        ];

        match (version, self) {
            (_, Alphabet::A0) => A0[zchar as usize],
            (_, Alphabet::A1) => A1[zchar as usize],
            (V1, Alphabet::A2) => A2_V1[zchar as usize],
            (_, Alphabet::A2) => A2[zchar as usize],
        }
    }
}
