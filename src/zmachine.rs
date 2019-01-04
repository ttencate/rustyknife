use crate::bytes::ByteAddress;
use crate::decoder::InstructionDecoder;
use crate::errors::RuntimeError;
use crate::instr::Instruction;
use crate::mem::*;
use std::fmt;
use std::fmt::{Display, Formatter};

pub struct ZMachine<'a> {
    story_file: &'a Memory,
    mem: Memory,
    pc: ByteAddress,
}

impl<'a> ZMachine<'a> {
    pub fn new(story_file: &Memory) -> ZMachine {
        let mut z = ZMachine {
            story_file: story_file,
            mem: Memory::with_size(story_file.bytes().len()),
            pc: ByteAddress(0),
        };
        z.restart();
        z
    }

    pub fn restart(&mut self) {
        self.mem.bytes_mut().copy_from(&self.story_file.bytes());
        self.pc = self.mem.initial_program_counter();
        self.reset();
    }

    pub fn step(&mut self) -> Result<(), RuntimeError> {
        let (instr, next_pc) = self.decode_next_instr()?;
        println!("{:?}", instr);
        self.pc = next_pc;
        Ok(())
    }

    fn reset(&mut self) {
        self.mem.set_flag(STATUS_LINE_NOT_AVAILABLE, false);
        self.mem.set_flag(SCREEN_SPLITTING_AVAILABLE, true);
        self.mem.set_flag(VARIABLE_PITCH_FONT_DEFAULT, true);
        self.mem.set_flag(TRANSCRIPTING_ON, false);
        if self.mem.version() >= Version::V3 {
            self.mem.set_flag(FORCE_FIXED_PITCH_FONT, false);
        }

        // Interpreter number
        // 11.1.3
        // Infocom used the interpreter numbers:
        //
        //    1   DECSystem-20     5   Atari ST           9   Apple IIc
        //    2   Apple IIe        6   IBM PC            10   Apple IIgs
        //    3   Macintosh        7   Commodore 128     11   Tandy Color
        //    4   Amiga            8   Commodore 64
        *self.mem.bytes_mut().get_u8_mut(ByteAddress(0x001e)).unwrap() = 6;

        // Interpreter version
        // 11.1.3.1
        // Interpreter versions are conventionally ASCII codes for upper-case letters in Versions 4
        // and 5 (note that Infocom's Version 6 interpreters just store numbers here).
        *self.mem.bytes_mut().get_u8_mut(ByteAddress(0x001f)).unwrap() = b'A';
    }

    fn decode_next_instr(&self) -> Result<(Instruction, ByteAddress), RuntimeError> {
        let mut decoder = InstructionDecoder::new(&self.mem, self.pc);
        let instr = decoder.decode()?;
        Ok((instr, decoder.next_addr()))
    }

    fn version(&self) -> Version {
        self.mem.version()
    }
}

impl<'a> Display for ZMachine<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "pc: {:}", self.pc)
    }
}

