use crate::bytes::Address;
use crate::instr::Instruction;

// 8.2
// In Versions 1 to 3, a status line should be printed by the interpreter, as follows. In Version 3, it must set bit 4 of 'Flags 1' in the header if it is unable to produce a status line.
pub struct StatusLine {
    // 8.2.2
    // The short name of the object whose number is in the first global variable should be printed
    // on the left hand side of the line.
    pub location: String,
    // 8.2.3
    // If there is room, the right hand side of the status line should display:
    pub progress: Progress,
}

pub enum Progress {
    // 8.2.3.1
    // For "score games": the score and number of turns, held in the values of the second and third
    // global variables respectively. The score may be assumed to be in the range -99 to 999
    // inclusive, and the turn number in the range 0 to 9999.
    Score { score: i16, turns: u16 },
    // 8.2.3.2
    // For "time games": the time, in the form hours:minutes (held in the second and third
    // globals). The time may be given on a 24-hour clock or the number of hours may be reduced
    // modulo 12 (but if so, "AM" or "PM" should be appended). Either way the player should be able
    // to see the difference between 4am and 4pm, for example. The hours global may be assumed to
    // be in the range 0 to 23 and the minutes global in the range 0 to 59.
    Time { hours: u16, minutes: u16 },
}

pub trait Platform {
    fn print(&mut self, string: &str);

    fn update_status_line(&mut self, _status_line: &StatusLine) {
    }

    fn read_line(&mut self, max_len_hint: usize) -> String;

    fn next_instr(&mut self, _pc: Address, _call_stack_depth: usize, _instr: &Instruction) {
    }
}
