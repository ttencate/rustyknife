use crate::bytes::{Address, Bytes};
use crate::decoder::InstructionDecoder;
use crate::errors::{FormatError, RuntimeError};
use crate::header;
use crate::instr::*;
use crate::mem::Memory;
use crate::obj::*;
use crate::platform::Platform;
use crate::version::*;
use crate::zstring;
use std::fmt;
use std::fmt::{Display, Formatter};

const STACK_SIZE_LIMIT: usize = 0x10000;
const CALL_STACK_SIZE_LIMIT: usize = 0x10000;

pub struct ZMachine<'a, P> where P: Platform {
    platform: &'a mut P,
    orig_bytes: Bytes,
    mem: Memory,
    pc: Address,
    call_stack: Vec<StackFrame>,
}

impl<'a, P> ZMachine<'a, P> where P: Platform {
    pub fn new(platform: &'a mut P, story_file: Vec<u8>) -> Result<ZMachine<'a, P>, FormatError> {
        // 5.5
        // In all other Versions, the word at $06 contains the byte address of the first
        // instruction to execute. The Z-machine starts in an environment with no local variables
        // from which, again, a return is illegal.
        let bytes = Bytes::from(story_file);
        let mem = Memory::wrap(bytes.clone())?;
        let mut z = ZMachine {
            platform: platform,
            orig_bytes: bytes,
            mem: mem,
            pc: Address::from_byte_address(0),
            call_stack: Vec::with_capacity(32),
        };
        z.restart();
        Ok(z)
    }

    pub fn restart(&mut self) {
        self.mem.bytes_mut().copy_from(&self.orig_bytes);
        self.call_stack.clear();
        self.call_stack.push(StackFrame::root());
        self.pc = self.mem.header().initial_program_counter();
        self.reset();
    }

    pub fn step(&mut self) -> Result<(), RuntimeError> {
        let mut decoder = InstructionDecoder::new(&self.mem, self.pc);
        let (instr, _loc) = decoder.decode()?;
        self.pc = decoder.next_addr();

        self.platform.next_instr(self.pc, self.call_stack.len() - 1, &instr);
        // TODO in case of any error, annotate it with location somehow
        self.exec_instr(instr)
    }

    fn exec_instr(&mut self, instr: Instruction) -> Result<(), RuntimeError> {
        match instr {
            Instruction::Je(var_operands, branch) => {
                // je
                // 2OP:1 1 je a b c d ?(label)
                // Jump if a is equal to any of the subsequent operands. (Thus @je a never jumps
                // and @je a b jumps if a = b.)
                // je with just 1 operand is not permitted.
                let a = self.eval(var_operands.get(0)?)?;
                let mut cond = false;
                for i in 1..var_operands.len() {
                    if a == self.eval(var_operands.get(i)?)? {
                        cond = true;
                    }
                }
                self.cond_branch(cond, branch)
            }
            // Instruction::Jl(var_operands, branch) =>
            Instruction::Jg(var_operands, branch) => {
                // jg
                // 2OP:3 3 jg a b ?(label)
                // Jump if a > b (using a signed 16-bit comparison).
                let a = self.eval(var_operands.get(0)?)? as i16;
                let b = self.eval(var_operands.get(1)?)? as i16;
                self.cond_branch(a > b, branch)
            }
            // Instruction::DecChk(var_operands, branch) =>
            Instruction::IncChk(var_operands, branch) => {
                // inc_chk
                // 2OP:5 5 inc_chk (variable) value ?(label)
                // Increment variable, and branch if now greater than value.
                let variable = self.variable(self.eval(var_operands.get(0)?)?)?;
                let value = self.eval(var_operands.get(1)?)?;
                let new_val = self.eval_var(variable)?.wrapping_add(1);
                self.store(variable, new_val)?;
                self.cond_branch(new_val > value, branch)
            }
            Instruction::Jin(var_operands, branch) => {
                // jin
                // 2OP:6 6 jin obj1 obj2 ?(label)
                // Jump if object a is a direct child of b, i.e., if parent of a is b.
                let a = Object::from_number(self.eval(var_operands.get(0)?)?);
                let b = Object::from_number(self.eval(var_operands.get(1)?)?);
                let parent_of_a = self.mem.obj_table().get_parent(a)?;
                self.cond_branch(parent_of_a == b, branch)
            }
            // Instruction::Test(var_operands, branch) =>
            // Instruction::Or(var_operands, store) =>
            Instruction::And(var_operands, store) => {
                // and
                // 2OP:9 9 and a b -> (result)
                // Bitwise AND.
                let a = self.eval(var_operands.get(0)?)?;
                let b = self.eval(var_operands.get(1)?)?;
                self.store(store, a & b)
            }
            Instruction::TestAttr(var_operands, branch) => {
                // test_attr
                // 2OP:10 A test_attr object attribute ?(label)
                // Jump if object has attribute.
                let object = Object::from_number(self.eval(var_operands.get(0)?)?);
                let attribute = Attribute::from_number(self.eval(var_operands.get(1)?)? as u8);
                let cond = self.mem.obj_table().get_attr(object, attribute)?;
                self.cond_branch(cond, branch)
            }
            Instruction::SetAttr(var_operands) => {
                // set_attr
                // 2OP:11 B set_attr object attribute
                // Make object have the attribute numbered attribute.
                let object = Object::from_number(self.eval(var_operands.get(0)?)?);
                let attribute = Attribute::from_number(self.eval(var_operands.get(1)?)? as u8);
                self.mem.obj_table_mut().set_attr(object, attribute, true)
            }
            // Instruction::ClearAttr(var_operands) =>
            Instruction::Store(var_operands) => {
                // store
                // 2OP:13 D store (variable) value
                // Set the VARiable referenced by the operand to value.
                let variable = self.variable(self.eval(var_operands.get(0)?)?)?;
                let value = self.eval(var_operands.get(1)?)?;
                self.store(variable, value)
            }
            Instruction::InsertObj(var_operands) => {
                // insert_obj
                // 2OP:14 E insert_obj object destination
                // Moves object O to become the first child of the destination object D. (Thus,
                // after the operation the child of D is O, and the sibling of O is whatever was
                // previously the child of D.) All children of O move with it. (Initially O can be
                // at any point in the object tree; it may legally have parent zero.)
                let object = Object::from_number(self.eval(var_operands.get(0)?)?);
                let destination = Object::from_number(self.eval(var_operands.get(1)?)?);
                self.mem.obj_table_mut().insert_obj(object, destination)
            }
            Instruction::Loadw(var_operands, store) => {
                // loadw
                // 2OP:15 F loadw array word-index -> (result)
                // Stores array-->word-index (i.e., the word at address array+2*word-index, which
                // must lie in static or dynamic memory).
                let array = self.eval(var_operands.get(0)?)?;
                let word_index = self.eval(var_operands.get(1)?)?;
                let addr = Address::from_byte_address(array + 2 * word_index);
                let val = self.mem.bytes().get_u16(addr)?;
                self.store(store, val)
            }
            Instruction::Loadb(var_operands, store) => {
                // loadb
                // 2OP:16 10 loadb array byte-index -> (result)
                // Stores array->byte-index (i.e., the byte at address array+byte-index, which must
                // lie in static or dynamic memory).
                let array = self.eval(var_operands.get(0)?)?;
                let byte_index = self.eval(var_operands.get(1)?)?;
                let addr = Address::from_byte_address(array + byte_index);
                let val = self.mem.bytes().get_u8(addr)?;
                self.store(store, val as u16)
            }
            Instruction::GetProp(var_operands, store) => {
                // get_prop
                // 2OP:17 11 get_prop object property -> (result)
                // Read property from object (resulting in the default value if it had no such
                // declared property). If the property has length 1, the value is only that byte.
                // If it has length 2, the first two bytes of the property are taken as a word
                // value. It is illegal for the opcode to be used if the property has length
                // greater than 2, and the result is unspecified.
                let object = Object::from_number(self.eval(var_operands.get(0)?)?);
                let property = Property::from_number(self.eval(var_operands.get(1)?)? as u8);
                let val = self.mem.obj_table().get_prop(object, property)?;
                self.store(store, val)
            }
            // Instruction::GetPropAddr(var_operands, store) =>
            // Instruction::GetNextProp(var_operands, store) =>
            Instruction::Add(var_operands, store) => {
                // add
                // 2OP:20 14 add a b -> (result)
                // Signed 16-bit addition.
                let a = self.eval(var_operands.get(0)?)?;
                let b = self.eval(var_operands.get(1)?)?;
                self.store(store, a.wrapping_add(b))
            }
            Instruction::Sub(var_operands, store) => {
                // sub
                // 2OP:21 15 sub a b -> (result)
                // Signed 16-bit subtraction.
                let a = self.eval(var_operands.get(0)?)?;
                let b = self.eval(var_operands.get(1)?)?;
                self.store(store, a.wrapping_sub(b))
            }
            // Instruction::Mul(left, right, store) =>
            // Instruction::Div(left, right, store) =>
            // Instruction::Mod(left, right, store) =>
            Instruction::Jz(operand, branch) => {
                // jz
                // 1OP:128 0 jz a ?(label)
                // Jump if a = 0.
                self.cond_branch(self.eval(operand)? == 0, branch)
            }
            // Instruction::GetSibling(operand, store, branch) =>
            // Instruction::GetChild(operand, store, branch) =>
            Instruction::GetParent(operand, store) => {
                // get_parent
                // 1OP:131 3 get_parent object -> (result)
                // Get parent object (note that this has no "branch if exists" clause).
                let object = Object::from_number(self.eval(operand)?);
                let parent = self.mem.obj_table().get_parent(object)?;
                self.store(store, parent.number())
            }
            // Instruction::GetPropLen(operand, store) =>
            Instruction::Inc(operand) => {
                // inc
                // 1OP:133 5 inc (variable)
                // Increment variable by 1. (This is signed, so -1 increments to 0.)
                let variable = self.variable(self.eval(operand)?)?;
                let new_val = self.eval_var(variable)?.wrapping_add(1);
                self.store(variable, new_val)
            }
            // Instruction::Dec(operand) =>
            // Instruction::PrintAddr(operand) =>
            // Instruction::RemoveObj(operand) =>
            Instruction::PrintObj(operand) => {
                // print_obj
                // 1OP:138 A print_obj object
                // Print short name of object (the Z-encoded string in the object header, not a
                // property). If the object number is invalid, the interpreter should halt with a
                // suitable error message.
                let object = Object::from_number(self.eval(operand)?);
                let name = self.mem.obj_table().get_name(object)?;
                self.platform.print(&name);
                Ok(())
            }
            Instruction::Ret(operand) => {
                // ret
                // 1OP:139 B ret value
                // Returns from the current routine with the value given.
                self.ret(self.eval(operand)?)
            }
            Instruction::Jump(operand) => {
                // jump
                // 1OP:140 C jump ?(label)
                //
                // Jump (unconditionally) to the given label. (This is not a branch instruction and
                // the operand is a 2-byte signed offset to apply to the program counter.) It is
                // legal for this to jump into a different routine (which should not change the
                // routine call state), although it is considered bad practice to do so and the Txd
                // disassembler is confused by it.
                // 
                // The destination of the jump opcode is:
                // Address after instruction + Offset - 2
                // This is analogous to the calculation for branch offsets.
                self.pc += (self.eval(operand)? as i16 - 2) as i32;
                Ok(())
            }
            Instruction::PrintPaddr(operand) => {
                // print_paddr
                // 1OP:141 D print_paddr packed-address-of-string
                // Print the (Z-encoded) string at the given packed address in high memory.
                let addr = Address::from_packed_address(self.eval(operand)?, self.version());
                let zstring = self.mem.bytes().get_zstring(addr)?;
                let string = zstring.decode(self.version(), &self.mem.abbrs_table())?;
                self.platform.print(&string);
                Ok(())
            }
            // Instruction::Load(operand, store) =>
            // Instruction::Not(operand, store) =>
            Instruction::Rtrue() => {
                // rtrue
                // 0OP:176 0 rtrue
                // Return true (i.e., 1) from the current routine.
                self.ret(1)
            }
            // Instruction::Rfalse() =>
            Instruction::Print(string) => {
                self.platform.print(&string);
                Ok(())
            }
            // Instruction::PrintRet(String) =>
            // Instruction::Nop() =>
            // Instruction::Save(branch) =>
            // Instruction::Restore(branch) =>
            // Instruction::Restart() =>
            // Instruction::RetPopped() =>
            // Instruction::Pop() =>
            // Instruction::Quit() =>
            Instruction::NewLine() => {
                self.platform.print("\n");
                Ok(())
            }
            // Instruction::ShowStatus() =>
            // Instruction::Verify(branch) =>
            Instruction::Call(var_operands, store) => {
                // call
                // VAR:224 0 1 call routine ...up to 3 args... -> (result)
                // The only call instruction in Version 3, Inform reads this as call_vs in higher
                // versions: it calls the routine with 0, 1, 2 or 3 arguments as supplied and
                // stores the resulting return value. (When the address 0 is called as a routine,
                // nothing happens and the return value is false.)
                let routine = var_operands.get(0)?;
                let args = var_operands.get_slice(1..var_operands.len())?;
                self.call(routine, args, store)
            }
            Instruction::Storew(var_operands) => {
                // storew
                // VAR:225 1 storew array word-index value
                // array-->word-index = value, i.e. stores the given value in the word at address
                // array+2*word-index (which must lie in dynamic memory). (See loadw.)
                let array = self.eval(var_operands.get(0)?)?;
                let word_index = self.eval(var_operands.get(1)?)?;
                let value = self.eval(var_operands.get(2)?)?;
                self.store_u16(Address::from_byte_address(array + 2 * word_index), value)
            }
            // Instruction::Storeb(var_operands) =>
            Instruction::PutProp(var_operands) => {
                // put_prop
                // VAR:227 3 put_prop object property value
                // Writes the given value to the given property of the given object. If the
                // property does not exist for that object, the interpreter should halt with a
                // suitable error message. If the property length is 1, then the interpreter should
                // store only the least significant byte of the value. (For instance, storing -1
                // into a 1-byte property results in the property value 255.) As with get_prop the
                // property length must not be more than 2: if it is, the behaviour of the opcode
                // is undefined.
                let obj = self.eval(var_operands.get(0)?)?;
                let prop = self.eval(var_operands.get(1)?)?;
                let val = self.eval(var_operands.get(2)?)?;
                self.mem.obj_table_mut().set_prop(Object::from_number(obj), Property::from_number(prop as u8), val)
            }
            // Instruction::Sread(var_operands) =>
            Instruction::PrintChar(var_operands) => {
                // print_char
                // VAR:229 5 print_char output-character-code
                // Print a ZSCII character. The operand must be a character code defined in ZSCII
                // for output (see S 3). In particular, it must certainly not be negative or larger
                // than 1023.
                let output_character_code = self.eval(var_operands.get(0)?)?;
                let character = zstring::zscii(output_character_code as usize)
                    .ok_or(RuntimeError::InvalidCharacterCode(output_character_code))?;
                self.platform.print(&character.to_string());
                Ok(())
            }
            Instruction::PrintNum(var_operands) => {
                // print_num
                // VAR:230 6 print_num value
                // Print (signed) number in decimal.
                let value = self.eval(var_operands.get(0)?)?;
                self.platform.print(&format!("{}", value as i16));
                Ok(())
            }
            // Instruction::Random(var_operands, store) =>
            Instruction::Push(var_operands) => {
                // push
                // VAR:232 8 push value
                // Pushes value onto the game stack.
                let value = self.eval(var_operands.get(0)?)?;
                self.frame_mut().push(value)
            }
            Instruction::Pull(var_operands) => {
                // pull
                // VAR:233 9 1 pull (variable)
                // 6 pull stack -> (result)
                // Pulls value off a stack. (If the stack underflows, the interpreter should halt
                // with a suitable error message.) In Version 6, the stack in question may be
                // specified as a user one: otherwise it is the game stack.
                let variable = self.variable(self.eval(var_operands.get(0)?)?)?;
                let value = self.frame_mut().pull()?;
                self.store(variable, value)
            }
            // Instruction::SplitWindow(var_operands) =>
            // Instruction::SetWindow(var_operands) =>
            // Instruction::OutputStream(var_operands) =>
            // Instruction::InputStream(var_operands) =>
            _ => panic!("TODO implement instruction {:?}", instr)
        }
    }

    fn reset(&mut self) {
        self.mem.header_mut().set_flag(header::STATUS_LINE_NOT_AVAILABLE, false);
        self.mem.header_mut().set_flag(header::SCREEN_SPLITTING_AVAILABLE, true);
        self.mem.header_mut().set_flag(header::VARIABLE_PITCH_FONT_DEFAULT, true);
        self.mem.header_mut().set_flag(header::TRANSCRIPTING_ON, false);
        if self.mem.version() >= V3 {
            self.mem.header_mut().set_flag(header::FORCE_FIXED_PITCH_FONT, false);
        }

        // TODO move these into a helper in the Header

        // Interpreter number
        // 11.1.3
        // Infocom used the interpreter numbers:
        //
        //    1   DECSystem-20     5   Atari ST           9   Apple IIc
        //    2   Apple IIe        6   IBM PC            10   Apple IIgs
        //    3   Macintosh        7   Commodore 128     11   Tandy Color
        //    4   Amiga            8   Commodore 64
        self.mem.bytes_mut().set_u8(Address::from_byte_address(0x001e), 6).unwrap();

        // Interpreter version
        // 11.1.3.1
        // Interpreter versions are conventionally ASCII codes for upper-case letters in Versions 4
        // and 5 (note that Infocom's Version 6 interpreters just store numbers here).
        self.mem.bytes_mut().set_u8(Address::from_byte_address(0x001f), b'A').unwrap();
    }

    fn call(&mut self, routine: Operand, args: &[Operand], store: Store) -> Result<(), RuntimeError> {
        // 6.4
        // Routine calls occur in the following circumstances: when one of the call... opcodes is
        // executed; in Versions 4 and later, when timed keyboard input is being monitored; in
        // Versions 5 and later, when a sound effect finishes; in Version 6, when the game begins
        // (to call the "main" routine); in Version 6, when a "newline interrupt" occurs.

        // 6.4.3
        // A routine call to packed address 0 is legal: it does nothing and returns false (0).
        // Otherwise it is illegal to call a packed address where no routine is present.
        let routine = Address::from_packed_address(self.eval(routine)?, self.version());
        if routine == Address::from_packed_address(0, self.version()) {
            return self.ret(0);
        }
        
        // 6.4.4
        // When a routine is called, its local variables are created with initial values taken from
        // the routine header (Versions 1 to 4) or with initial value 0 (Versions 5 and later). ...
        let (mut frame, next_pc) = StackFrame::from_routine_header(&self.mem, routine, store, self.pc)?;

        // ... Next, the arguments are written into the local variables (argument 1 into local 1
        // and so on).
        //
        // 6.4.4.1
        // It is legal for there to be more arguments than local variables (any spare arguments are
        // thrown away) or for there to be fewer.
        for i in 0..(std::cmp::min(args.len(), frame.num_locals())) {
            frame.set_local(Local::from_index(i), self.eval(args[i])?)?;
        }

        if self.call_stack.len() >= CALL_STACK_SIZE_LIMIT {
            return Err(RuntimeError::CallStackOverflow);
        }
        self.call_stack.push(frame);
        self.pc = next_pc;
        Ok(())
    }

    fn ret(&mut self, val: u16) -> Result<(), RuntimeError> {
        if self.call_stack.len() == 1 {
            return Err(RuntimeError::CallStackUnderflow);
        }

        self.pc = self.frame().return_addr;
        let store = self.frame().store;
        self.call_stack.pop();

        // 6.4.1
        // ... All routines return a value (though sometimes this value is thrown away afterward:
        // for example by opcodes in the form call_vn*).
        // 6.4.5
        // The return value of a routine can be any Z-machine number. Returning 'false' means
        // returning 0; returning 'true' means returning 1.
        self.store(store, val)?;

        Ok(())
    }

    fn cond_branch(&mut self, cond: bool, branch: Branch) -> Result<(), RuntimeError> {
        if branch.matches_cond(cond) {
            match branch.target() {
                BranchTarget::ReturnFalse => self.ret(0),
                BranchTarget::ReturnTrue => self.ret(1),
                BranchTarget::ToAddress(addr) => {
                    self.pc = addr;
                    Ok(())
                }
            }
        } else {
            Ok(())
        }
    }

    fn eval(&self, operand: Operand) -> Result<u16, RuntimeError> {
        match operand {
            Operand::LargeConstant(c) => Ok(c),
            Operand::SmallConstant(c) => Ok(c as u16),
            Operand::Variable(var) => self.eval_var(var),
        }
    }

    fn eval_var(&self, var: Variable) -> Result<u16, RuntimeError> {
        match var {
            Variable::TopOfStack => self.frame().stack_top(),
            Variable::Local(local) => self.frame().local(local),
            Variable::Global(global) => self.mem.globals().get(global),
        }
    }

    fn variable(&self, val: u16) -> Result<Variable, RuntimeError> {
        // 4.2.3
        // ... Some instructions take as an operand a "variable by reference": for instance, inc
        // has one operand, the reference number of a variable to increment. This operand usually
        // has type 'Small constant' (and Inform automatically assembles a line like @inc turns by
        // writing the operand turns as a small constant with value the reference number of the
        // variable turns).
        if val < 0x100 {
            Ok(Variable::from_byte(val as u8))
        } else {
            Err(RuntimeError::InvalidVariable(val))
        }
    }

    fn store(&mut self, store: Store, val: u16) -> Result<(), RuntimeError> {
        match store {
            // 6.3
            // Writing to the stack pointer (variable number $00) pushes a value onto the stack;
            Variable::TopOfStack => self.frame_mut().push(val),
            Variable::Local(local) => self.frame_mut().set_local(local, val),
            Variable::Global(global) => self.mem.globals_mut().set(global, val),
        }
    }

    fn store_u16(&mut self, addr: Address, val: u16) -> Result<(), RuntimeError> {
        // TODO writability check
        self.mem.bytes_mut().set_u16(addr, val)
    }

    fn version(&self) -> Version {
        self.mem.version()
    }

    fn frame(&self) -> &StackFrame {
        self.call_stack.last().unwrap()
    }

    fn frame_mut(&mut self) -> &mut StackFrame {
        self.call_stack.last_mut().unwrap()
    }
}

impl<'a, P> Display for ZMachine<'a, P> where P: Platform {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "pc: {:}", self.pc)
    }
}

struct StackFrame {
    stack: Vec<u16>,
    locals: Vec<u16>,
    store: Store,
    return_addr: Address,
}

impl StackFrame {
    fn root() -> StackFrame {
        StackFrame {
            stack: vec![],
            locals: vec![],
            store: Variable::TopOfStack, // Unused.
            return_addr: Address::from_byte_address(0), // Unused.
        }
    }

    fn from_routine_header(mem: &Memory, routine: Address, store: Store, return_addr: Address) -> Result<(StackFrame, Address), RuntimeError> {
        // 5.1
        // A routine is required to begin at an address in memory which can be represented by a
        // packed address (for instance, in Version 5 it must occur at a byte address which is
        // divisible by 4).
        let mut addr = routine;

        // 6.3.1
        // The stack is considered as empty at the start of each routine: it is illegal to pull
        // values from it unless values have first been pushed on.
        let stack = vec![];

        // 5.2
        // A routine begins with one byte indicating the number of local variables it has (between
        // 0 and 15 inclusive).
        let num_locals = mem.bytes().get_u8(addr)
            .or(Err(RuntimeError::InvalidRoutineHeader(addr)))?
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
            V1 | V2 | V3 => {
                for i in 0..num_locals as usize {
                    locals[i] = mem.bytes().get_u16(addr)
                        .or(Err(RuntimeError::InvalidRoutineHeader(addr)))?;
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
            return_addr: return_addr,
        };
        Ok((frame, addr))
    }

    fn stack_top(&self) -> Result<u16, RuntimeError> {
        Ok(*self.stack.last().ok_or(RuntimeError::StackEmpty)?)
    }

    fn push(&mut self, value: u16) -> Result<(), RuntimeError> {
        if self.stack.len() >= STACK_SIZE_LIMIT {
            return Err(RuntimeError::StackOverflow);
        }
        self.stack.push(value);
        Ok(())
    }

    fn pull(&mut self) -> Result<u16, RuntimeError> {
        self.stack.pop().ok_or(RuntimeError::StackUnderflow)
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
