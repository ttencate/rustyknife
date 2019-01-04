use crate::bytes::Address;
use crate::decoder::InstructionDecoder;
use crate::errors::{ErrorLocation, RuntimeError};
use crate::instr::*;
use crate::mem::*;
use std::fmt;
use std::fmt::{Display, Formatter};

pub struct ZMachine<'a> {
    story_file: &'a Memory,
    mem: Memory,
    pc: Address,
    call_stack: Vec<StackFrame>,
}

impl<'a> ZMachine<'a> {
    pub fn new(story_file: &Memory) -> ZMachine {
        // 5.5
        // In all other Versions, the word at $06 contains the byte address of the first
        // instruction to execute. The Z-machine starts in an environment with no local variables
        // from which, again, a return is illegal.
        let mut z = ZMachine {
            story_file: story_file,
            mem: Memory::with_size(story_file.bytes().len()),
            pc: Address::from_byte_address(0),
            call_stack: Vec::with_capacity(32),
        };
        z.restart();
        z
    }

    pub fn restart(&mut self) {
        self.mem.bytes_mut().copy_from(&self.story_file.bytes());
        self.call_stack.clear();
        self.call_stack.push(StackFrame::root());
        self.pc = self.mem.initial_program_counter();
        self.reset();
    }

    pub fn step(&mut self) -> Result<(), RuntimeError> {
        let mut decoder = InstructionDecoder::new(&self.mem, self.pc);
        let (instr, loc) = decoder.decode()?;
        let next_pc = decoder.next_addr();

        println!("{:}  {:?}", self.pc, instr);
        self.pc = self.exec_instr(instr, loc)?.unwrap_or(next_pc);
        Ok(())
    }

    fn exec_instr(&mut self, instr: Instruction, loc: ErrorLocation) -> Result<Option<Address>, RuntimeError> {
        match &instr {
            // Instruction::Je(left, right, branch) =>
            // Instruction::Jl(left, right, branch) =>
            // Instruction::Jg(left, right, branch) =>
            // Instruction::DecChk(left, right, branch) =>
            // Instruction::IncChk(left, right, branch) =>
            // Instruction::Jin(left, right, branch) =>
            // Instruction::Test(left, right, branch) =>
            // Instruction::Or(left, right, store) =>
            // Instruction::And(left, right, store) =>
            // Instruction::TestAttr(left, right, branch) =>
            // Instruction::SetAttr(left, right) =>
            // Instruction::ClearAttr(left, right) =>
            // Instruction::store(left, right) =>
            // Instruction::InsertObj(left, right) =>
            // Instruction::Loadw(left, right, store) =>
            // Instruction::Loadb(left, right, store) =>
            // Instruction::GetProp(left, right, store) =>
            // Instruction::GetPropAddr(left, right, store) =>
            // Instruction::GetNextProp(left, right, store) =>
            // Instruction::Add(left, right, store) =>
            // Instruction::Sub(left, right, store) =>
            // Instruction::Mul(left, right, store) =>
            // Instruction::Div(left, right, store) =>
            // Instruction::Mod(left, right, store) =>
            // Instruction::Jz(operand, branch) =>
            // Instruction::GetSibling(operand, store, branch) =>
            // Instruction::GetChild(operand, store, branch) =>
            // Instruction::GetParent(operand, store) =>
            // Instruction::GetPropLen(operand, store) =>
            // Instruction::Inc(operand) =>
            // Instruction::Dec(operand) =>
            // Instruction::PrintAddr(operand) =>
            // Instruction::RemoveObj(operand) =>
            // Instruction::PrintObj(operand) =>
            // Instruction::Ret(operand) =>
            // Instruction::Jump(operand) =>
            // Instruction::PrintPaddr(operand) =>
            // Instruction::Load(operand, store) =>
            // Instruction::Not(operand, store) =>
            // Instruction::Rtrue() =>
            // Instruction::Rfalse() =>
            // Instruction::Print(String) =>
            // Instruction::PrintRet(String) =>
            // Instruction::Nop() =>
            // Instruction::Save(branch) =>
            // Instruction::Restore(branch) =>
            // Instruction::Restart() =>
            // Instruction::RetPopped() =>
            // Instruction::Pop() =>
            // Instruction::Quit() =>
            // Instruction::NewLine() =>
            // Instruction::ShowStatus() =>
            // Instruction::Verify(branch) =>
            Instruction::Call(var_operands, store) => {
                self.call(
                    *var_operands.get(0).ok_or(RuntimeError::NotEnoughOperands(instr.clone(), loc))?,
                    &var_operands[1..],
                    *store)?;
            }
            // Instruction::Storew(var_operands) =>
            // Instruction::Storeb(var_operands) =>
            // Instruction::PutProp(var_operands) =>
            // Instruction::Sread(var_operands) =>
            // Instruction::PrintChar(var_operands) =>
            // Instruction::PrintNum(var_operands) =>
            // Instruction::Random(var_operands, store) =>
            // Instruction::Push(var_operands) =>
            // Instruction::Pull(var_operands) =>
            // Instruction::SplitWindow(var_operands) =>
            // Instruction::SetWindow(var_operands) =>
            // Instruction::OutputStream(var_operands) =>
            // Instruction::InputStream(var_operands) =>
            _ => panic!("TODO implement instruction {:?}", instr)
        }
        Ok(None)
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
        *self.mem.bytes_mut().get_u8_mut(Address::from_byte_address(0x001e)).unwrap() = 6;

        // Interpreter version
        // 11.1.3.1
        // Interpreter versions are conventionally ASCII codes for upper-case letters in Versions 4
        // and 5 (note that Infocom's Version 6 interpreters just store numbers here).
        *self.mem.bytes_mut().get_u8_mut(Address::from_byte_address(0x001f)).unwrap() = b'A';
    }

    fn call(&mut self, dest: Operand, args: &[Operand], store: Store) -> Result<(), RuntimeError> {
        // 6.4
        // Routine calls occur in the following circumstances: when one of the call... opcodes is
        // executed; in Versions 4 and later, when timed keyboard input is being monitored; in
        // Versions 5 and later, when a sound effect finishes; in Version 6, when the game begins
        // (to call the "main" routine); in Version 6, when a "newline interrupt" occurs.
        //
        // 6.4.1
        // A routine call may have any number of arguments, from 0 to 3 (in Versions 1 to
        // 3) or 0 to 7 (Versions 4 and later). All routines return a value (though sometimes this
        // value is thrown away afterward: for example by opcodes in the form call_vn*).
        // 
        // 6.4.2
        // Routine calls preserve local variables and the stack (except when the return value is
        // stored in a local variable or onto the top of the stack).
        // 
        // 6.4.3
        // A routine call to packed address 0 is legal: it does nothing and returns false (0).
        // Otherwise it is illegal to call a packed address where no routine is present.
        // 
        // 6.4.4.1
        // It is legal for there to be more arguments than local variables (any spare arguments are
        // thrown away) or for there to be fewer.
        // 
        // 6.4.5
        // The return value of a routine can be any Z-machine number. Returning 'false' means
        // returning 0; returning 'true' means returning 1.

        // 6.4.4
        // When a routine is called, its local variables are created with initial values taken from
        // the routine header (Versions 1 to 4) or with initial value 0 (Versions 5 and later).
        let (mut frame, next_pc) = StackFrame::from_routine_header(
            &self.mem, Address::from_packed_address(self.eval(dest)?, self.version()), store)?;

        // Next, the arguments are written into the local variables (argument 1 into local 1 and so
        // on).
        for i in 0..(std::cmp::min(args.len(), frame.num_locals())) {
            frame.set_local(Local::from_index(i), self.eval(args[i])?)?;
        }

        self.call_stack.push(frame);
        self.pc = next_pc;

        Ok(())
    }

    fn eval(&self, operand: Operand) -> Result<u16, RuntimeError> {
        match operand {
            Operand::LargeConstant(c) => Ok(c),
            Operand::SmallConstant(c) => Ok(c as u16),
            Operand::Variable(var) => match var {
                Variable::TopOfStack => self.call_stack_top().stack_top(),
                Variable::Local(local) => self.call_stack_top().local(local),
                Variable::Global(global) => self.mem.global(global)
                    .ok_or(RuntimeError::InvalidGlobal(global)),
            }
        }
    }

    fn version(&self) -> Version {
        self.mem.version()
    }

    fn call_stack_top(&self) -> &StackFrame {
        self.call_stack.last().unwrap()
    }
}

impl<'a> Display for ZMachine<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "pc: {:}", self.pc)
    }
}

struct StackFrame {
    stack: Vec<u16>,
    locals: Vec<u16>,
    store: Store,
}

impl StackFrame {
    fn root() -> StackFrame {
        StackFrame {
            stack: vec![],
            locals: vec![],
            store: Variable::TopOfStack, // Unused.
        }
    }

    fn from_routine_header(mem: &Memory, addr: Address, store: Store) -> Result<(StackFrame, Address), RuntimeError> {
        // 5.1
        // A routine is required to begin at an address in memory which can be represented by a
        // packed address (for instance, in Version 5 it must occur at a byte address which is
        // divisible by 4).
        let mut addr = addr;

        // 6.3.1
        // The stack is considered as empty at the start of each routine: it is illegal to pull
        // values from it unless values have first been pushed on.
        let stack = vec![];

        // 5.2
        // A routine begins with one byte indicating the number of local variables it has (between
        // 0 and 15 inclusive).
        let num_locals = mem.bytes().get_u8(addr)
            .ok_or(RuntimeError::InvalidRoutineHeader(addr))?
            as usize;
        if num_locals > 15 {
            return Err(RuntimeError::InvalidRoutineHeader(addr));
        }
        addr += 1;

        let mut locals = vec![0; num_locals];
        match mem.version() {
            // 5.2.1
            // In Versions 1 to 4, that number of 2-byte words follows, giving initial values for
            // these local variables.
            Version::V1 | Version::V2 | Version::V3 => {
                for i in 0..num_locals as usize {
                    locals[i] = mem.bytes().get_u16(addr)
                        .ok_or(RuntimeError::InvalidRoutineHeader(addr))?;
                    addr += 2;
                }
            }
            // In Versions 5 and later, the initial values are all zero.
        }
        
        // 5.3
        // Execution of instructions begins from the byte after this header information. There is
        // no formal 'end-marker' for a routine (it is simply assumed that execution eventually
        // results in a return taking place).

        let frame = StackFrame {
            stack: stack,
            locals: locals,
            store: store,
        };
        Ok((frame, addr))
    }

    fn stack_top(&self) -> Result<u16, RuntimeError> {
        Ok(*self.stack.last().ok_or(RuntimeError::StackEmpty)?)
    }

    fn num_locals(&self) -> usize {
        self.locals.len()
    }

    fn local(&self, local: Local) -> Result<u16, RuntimeError> {
        Ok(*self.locals.get(local.index()).ok_or(RuntimeError::InvalidLocal(local))?)
    }

    fn set_local(&mut self, local: Local, value: u16) -> Result<(), RuntimeError> {
        *self.locals.get_mut(local.index()).ok_or(RuntimeError::InvalidLocal(local))? = value;
        Ok(())
    }
}
