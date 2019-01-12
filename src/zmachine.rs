use crate::bytes::{Address, Bytes};
use crate::decoder::InstructionDecoder;
use crate::errors::{FormatError, RuntimeError};
use crate::header;
use crate::instr::*;
use crate::mem::Memory;
use crate::obj::*;
use crate::platform::Platform;
use crate::random::Random;
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
    random: Random,
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
            random: Random::new(),
        };
        z.random.seed_unpredictably();
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

    pub fn run(&mut self) -> Result<(), RuntimeError> {
        while self.step()? {
        }
        Ok(())
    }

    fn step(&mut self) -> Result<bool, RuntimeError> {
        let mut decoder = InstructionDecoder::new(&self.mem, self.pc);
        let (instr, _loc) = decoder.decode()?;
        self.pc = decoder.next_addr();

        self.platform.next_instr(self.pc, self.call_stack.len() - 1, &instr);

        if let Instruction::Quit() = instr {
            return Ok(false);
        }
        // TODO in case of any error, annotate it with location somehow
        self.exec_instr(instr)?;
        Ok(true)
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
            Instruction::Jl(var_operands, branch) => {
                // jl
                // 2OP:2 2 jl a b ?(label)
                // Jump if a < b (using a signed 16-bit comparison).
                let a = self.eval(var_operands.get(0)?)? as i16;
                let b = self.eval(var_operands.get(1)?)? as i16;
                self.cond_branch(a < b, branch)
            }
            Instruction::Jg(var_operands, branch) => {
                // jg
                // 2OP:3 3 jg a b ?(label)
                // Jump if a > b (using a signed 16-bit comparison).
                let a = self.eval(var_operands.get(0)?)? as i16;
                let b = self.eval(var_operands.get(1)?)? as i16;
                self.cond_branch(a > b, branch)
            }
            Instruction::DecChk(var_operands, branch) => {
                // dec_chk
                // 2OP:4 4 dec_chk (variable) value ?(label)
                // Decrement variable, and branch if it is now less than the given value.
                let variable = self.eval(var_operands.get(0)?)?;
                let variable = self.variable(variable)?;
                let value = self.eval(var_operands.get(1)?)? as i16;
                let new_val = self.eval_var(variable)?.wrapping_sub(1) as i16;
                self.store(variable, new_val as u16)?;
                self.cond_branch(new_val < value, branch)
            }
            Instruction::IncChk(var_operands, branch) => {
                // inc_chk
                // 2OP:5 5 inc_chk (variable) value ?(label)
                // Increment variable, and branch if now greater than value.
                let variable = self.eval(var_operands.get(0)?)?;
                let variable = self.variable(variable)?;
                let value = self.eval(var_operands.get(1)?)? as i16;
                let new_val = self.eval_var(variable)?.wrapping_add(1) as i16;
                self.store(variable, new_val as u16)?;
                self.cond_branch(new_val > value, branch)
            }
            Instruction::Jin(var_operands, branch) => {
                // jin
                // 2OP:6 6 jin obj1 obj2 ?(label)
                // Jump if object a is a direct child of b, i.e., if parent of a is b.
                let a = Object::from_number(self.eval(var_operands.get(0)?)?);
                let b = Object::from_number(self.eval(var_operands.get(1)?)?);
                let cond = if let Some(a_ref) = self.mem.obj_table().get_obj_ref(a)? {
                    a_ref.parent()? == b
                } else {
                    b.is_null()
                };
                self.cond_branch(cond, branch)
            }
            Instruction::Test(var_operands, branch) => {
                // test
                // 2OP:7 7 test bitmap flags ?(label)
                // Jump if all of the flags in bitmap are set (i.e. if bitmap & flags == flags).
                let bitmap = self.eval(var_operands.get(0)?)?;
                let flags = self.eval(var_operands.get(1)?)?;
                self.cond_branch(bitmap & flags == flags, branch)
            }
            Instruction::Or(var_operands, store) => {
                // or
                // 2OP:8 8 or a b -> (result)
                // Bitwise OR.
                let a = self.eval(var_operands.get(0)?)?;
                let b = self.eval(var_operands.get(1)?)?;
                self.store(store, a | b)
            }
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
                let cond = if let Some(obj_ref) = self.mem.obj_table_mut().get_obj_ref(object)? {
                    obj_ref.attr(attribute)?
                } else {
                    false
                };
                self.cond_branch(cond, branch)
            }
            Instruction::SetAttr(var_operands) => {
                // set_attr
                // 2OP:11 B set_attr object attribute
                // Make object have the attribute numbered attribute.
                let object = Object::from_number(self.eval(var_operands.get(0)?)?);
                let attribute = Attribute::from_number(self.eval(var_operands.get(1)?)? as u8);
                if let Some(mut obj_ref) = self.mem.obj_table_mut().get_obj_ref(object)? {
                    obj_ref.set_attr(attribute, true)
                } else {
                    Ok(())
                }
            }
            Instruction::ClearAttr(var_operands) => {
                // clear_attr
                // 2OP:12 C clear_attr object attribute
                // Make object not have the attribute numbered attribute.
                let object = Object::from_number(self.eval(var_operands.get(0)?)?);
                let attribute = Attribute::from_number(self.eval(var_operands.get(1)?)? as u8);
                if let Some(mut obj_ref) = self.mem.obj_table_mut().get_obj_ref(object)? {
                    obj_ref.set_attr(attribute, false)
                } else {
                    Ok(())
                }
            }
            Instruction::Store(var_operands) => {
                // store
                // 2OP:13 D store (variable) value
                // Set the VARiable referenced by the operand to value.
                let variable = self.eval(var_operands.get(0)?)?;
                let variable = self.variable(variable)?;
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
                if !destination.is_null() {
                    if let Some(mut obj_ref) = self.mem.obj_table_mut().get_obj_ref(object)? {
                        obj_ref.insert_into(destination)
                    } else {
                        Ok(())
                    }
                } else {
                    Ok(())
                }
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
                let val = if let Some(obj_ref) = self.mem.obj_table().get_obj_ref(object)? {
                    if let Some(prop_ref) = obj_ref.get_prop_ref(property)? {
                        prop_ref.get()?
                    } else {
                        // 12.2
                        // ... When the game attempts to read the value of property n for an object
                        // which does not provide property n, the n-th entry in this table is the
                        // resulting value.
                        self.mem.obj_table().get_prop_default(property)?
                    }
                } else {
                    0
                };
                self.store(store, val)
            }
            Instruction::GetPropAddr(var_operands, store) => {
                // get_prop_addr
                // 2OP:18 12 get_prop_addr object property -> (result)
                // Get the byte address (in dynamic memory) of the property data for the given
                // object's property. This must return 0 if the object hasn't got the property.
                let object = Object::from_number(self.eval(var_operands.get(0)?)?);
                let property = Property::from_number(self.eval(var_operands.get(1)?)? as u8);
                let addr = if let Some(obj_ref) = self.mem.obj_table().get_obj_ref(object)? {
                    if let Some(prop_ref) = obj_ref.get_prop_ref(property)? {
                        prop_ref.addr()
                    } else {
                        Address::null()
                    }
                } else {
                    Address::null()
                };
                self.store(store, addr.to_byte_address())
            }
            Instruction::GetNextProp(var_operands, store) => {
                // get_next_prop
                // 2OP:19 13 get_next_prop object property -> (result)
                // Gives the number of the next property provided by the quoted object. This may be
                // zero, indicating the end of the property list; if called with zero, it gives the
                // first property number present. It is illegal to try to find the next property of
                // a property which does not exist, and an interpreter should halt with an error
                // message (if it can efficiently check this condition).
                let object = Object::from_number(self.eval(var_operands.get(0)?)?);
                let property = Property::from_number(self.eval(var_operands.get(1)?)? as u8);
                let next_prop = if let Some(obj_ref) = self.mem.obj_table().get_obj_ref(object)? {
                    let mut iter = obj_ref.iter_props()?;
                    if !property.is_null() {
                        while let Some(res) = iter.next() {
                            if res?.prop() == property {
                                break;
                            }
                        }
                    }
                    if let Some(res) = iter.next() {
                        res?.prop()
                    } else {
                        Property::null()
                    }
                } else {
                    Property::null()
                };
                self.store(store, next_prop.to_number() as u16)
            }
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
            Instruction::Mul(var_operands, store) => {
                // mul
                // 2OP:22 16 mul a b -> (result)
                // Signed 16-bit multiplication.
                let a = self.eval(var_operands.get(0)?)? as i16;
                let b = self.eval(var_operands.get(1)?)? as i16;
                self.store(store, a.wrapping_mul(b) as u16)
            }
            Instruction::Div(var_operands, store) => {
                // div
                // 2OP:23 17 div a b -> (result)
                // Signed 16-bit division. Division by zero should halt the interpreter with a
                // suitable error message.
                let a = self.eval(var_operands.get(0)?)? as i16;
                let b = self.eval(var_operands.get(1)?)? as i16;
                if b == 0 {
                    return Err(RuntimeError::DivisionByZero);
                }
                self.store(store, a.wrapping_div(b) as u16)
            }
            Instruction::Mod(var_operands, store) => {
                // mod
                // 2OP:24 18 mod a b -> (result)
                // Remainder after signed 16-bit division. Division by zero should halt the
                // interpreter with a suitable error message.
                let a = self.eval(var_operands.get(0)?)? as i16;
                let b = self.eval(var_operands.get(1)?)? as i16;
                if b == 0 {
                    return Err(RuntimeError::DivisionByZero);
                }
                self.store(store, a.wrapping_rem(b) as u16)
            }
            Instruction::Jz(operand, branch) => {
                // jz
                // 1OP:128 0 jz a ?(label)
                // Jump if a = 0.
                let a = self.eval(operand)?;
                self.cond_branch(a == 0, branch)
            }
            Instruction::GetSibling(operand, store, branch) => {
                // get_sibling
                // 1OP:129 1 get_sibling object -> (result) ?(label)
                // Get next object in tree, branching if this exists, i.e. is not 0.
                let object = Object::from_number(self.eval(operand)?);
                let sibling = if let Some(obj_ref) = self.mem.obj_table().get_obj_ref(object)? {
                    obj_ref.sibling()?
                } else {
                    Object::null()
                };
                self.store(store, sibling.number())?;
                self.cond_branch(!sibling.is_null(), branch)
            }
            Instruction::GetChild(operand, store, branch) => {
                // get_child
                // 1OP:130 2 get_child object -> (result) ?(label)
                // Get first object contained in given object, branching if this exists, i.e. is
                // not nothing (i.e., is not 0).
                let object = Object::from_number(self.eval(operand)?);
                let child = if let Some(obj_ref) = self.mem.obj_table().get_obj_ref(object)? {
                    obj_ref.child()?
                } else {
                    Object::null()
                };
                self.store(store, child.number())?;
                self.cond_branch(!child.is_null(), branch)
            }
            Instruction::GetParent(operand, store) => {
                // get_parent
                // 1OP:131 3 get_parent object -> (result)
                // Get parent object (note that this has no "branch if exists" clause).
                let object = Object::from_number(self.eval(operand)?);
                let parent = if let Some(obj_ref) = self.mem.obj_table().get_obj_ref(object)? {
                    obj_ref.parent()?
                } else {
                    Object::null()
                };
                self.store(store, parent.number())
            }
            Instruction::GetPropLen(operand, store) => {
                // get_prop_len
                // 1OP:132 4 get_prop_len property-address -> (result)
                // Get length of property data (in bytes) for the given object's property. It is
                // illegal to try to find the property length of a property which does not exist
                // for the given object, and an interpreter should halt with an error message (if
                // it can efficiently check this condition).
                // @get_prop_len 0 must return 0. This is required by some Infocom games and files
                // generated by old versions of Inform.
                let prop_addr = Address::from_byte_address(self.eval(operand)?);
                let len = if prop_addr == Address::from_byte_address(0) {
                    0
                } else {
                    self.mem.obj_table().get_prop_len(prop_addr)?
                };
                self.store(store, len as u16)
            }
            Instruction::Inc(operand) => {
                // inc
                // 1OP:133 5 inc (variable)
                // Increment variable by 1. (This is signed, so -1 increments to 0.)
                let variable = self.eval(operand)?;
                let variable = self.variable(variable)?;
                let new_val = self.eval_var(variable)?.wrapping_add(1);
                self.store(variable, new_val)
            }
            Instruction::Dec(operand) => {
                // dec
                // 1OP:134 6 dec (variable)
                // Decrement variable by 1. This is signed, so 0 decrements to -1.
                let variable = self.eval(operand)?;
                let variable = self.variable(variable)?;
                let new_val = self.eval_var(variable)?.wrapping_sub(1);
                self.store(variable, new_val)
            }
            Instruction::PrintAddr(operand) => {
                // print_addr
                // 1OP:135 7 print_addr byte-address-of-string
                // Print (Z-encoded) string at given byte address, in dynamic or static memory.
                let addr = Address::from_byte_address(self.eval(operand)?);
                let zstring = self.mem.bytes().get_zstring(addr)?;
                let string = zstring.decode(self.version(), Some(&self.mem.abbrs_table()))?;
                self.platform.print(&string);
                Ok(())
            }
            Instruction::RemoveObj(operand) => {
                // remove_obj
                // 1OP:137 9 remove_obj object
                // Detach the object from its parent, so that it no longer has any parent. (Its
                // children remain in its possession.)
                let object = Object::from_number(self.eval(operand)?);
                if let Some(mut obj_ref) = self.mem.obj_table_mut().get_obj_ref(object)? {
                    obj_ref.remove_from_parent()
                } else {
                    Ok(())
                }
            }
            Instruction::PrintObj(operand) => {
                // print_obj
                // 1OP:138 A print_obj object
                // Print short name of object (the Z-encoded string in the object header, not a
                // property). If the object number is invalid, the interpreter should halt with a
                // suitable error message.
                let object = Object::from_number(self.eval(operand)?);
                let name = if let Some(obj_ref) = self.mem.obj_table().get_obj_ref(object)? {
                    obj_ref.name()?
                } else {
                    "".to_string()
                };
                self.platform.print(&name);
                Ok(())
            }
            Instruction::Ret(operand) => {
                // ret
                // 1OP:139 B ret value
                // Returns from the current routine with the value given.
                let value = self.eval(operand)?;
                self.ret(value)
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
                let offset = self.eval(operand)? as i16;
                self.pc += (offset - 2) as i32;
                Ok(())
            }
            Instruction::PrintPaddr(operand) => {
                // print_paddr
                // 1OP:141 D print_paddr packed-address-of-string
                // Print the (Z-encoded) string at the given packed address in high memory.
                let addr = Address::from_packed_address(self.eval(operand)?, self.version());
                let zstring = self.mem.bytes().get_zstring(addr)?;
                let string = zstring.decode(self.version(), Some(&self.mem.abbrs_table()))?;
                self.platform.print(&string);
                Ok(())
            }
            Instruction::Load(operand, store) => {
                // load
                // 1OP:142 E load (variable) -> (result)
                // The value of the variable referred to by the operand is stored in the result.
                // (Inform doesn't use this; see the notes to S 14.)
                let variable = self.eval(operand)?;
                let variable = self.variable(variable)?;
                let value = self.eval_var(variable)?;
                self.store(store, value)
            }
            Instruction::Not(operand, store) => {
                // not
                // 1OP:143 F 1/4 not value -> (result)
                // VAR:248 18 5/6 not value -> (result)
                // Bitwise NOT (i.e., all 16 bits reversed). Note that in Versions 3 and 4 this is
                // a 1OP instruction, reasonably since it has 1 operand, but in later Versions it
                // was moved into the extended set to make room for call_1n.
                let value = self.eval(operand)?;
                self.store(store, !value)
            }
            Instruction::Rtrue() => {
                // rtrue
                // 0OP:176 0 rtrue
                // Return true (i.e., 1) from the current routine.
                self.ret(1)
            }
            Instruction::Rfalse() => {
                // rfalse
                // 0OP:177 1 rfalse
                // Return false (i.e., 0) from the current routine.
                self.ret(0)
            }
            Instruction::Print(string) => {
                self.platform.print(&string);
                Ok(())
            }
            Instruction::PrintRet(string) => {
                // print_ret
                // 0OP:179 3 print_ret <literal-string>
                // Print the quoted (literal) Z-encoded string, then print a new-line and then
                // return true (i.e., 1).
                self.platform.print(&string);
                self.platform.print("\n");
                self.ret(1)
            }
            Instruction::Nop() => {
                // nop
                // 0OP:180 4 1/- nop
                // Probably the official "no operation" instruction, which, appropriately, was
                // never operated (in any of the Infocom datafiles): it may once have been a
                // breakpoint.
                Ok(())
            }
            // Instruction::Save(branch) =>
            // Instruction::Restore(branch) =>
            // Instruction::Restart() =>
            Instruction::RetPopped() => {
                // ret_popped
                // 0OP:184 8 ret_popped
                // Pops top of stack and returns that. (This is equivalent to ret sp, but is one
                // byte cheaper.)
                let value = self.frame_mut().pull()?;
                self.ret(value)
            }
            Instruction::Pop() => {
                // pop
                // 0OP:185 9 1 pop
                // Throws away the top item on the stack. (This was useful to lose unwanted routine
                // call results in early Versions.)
                self.frame_mut().pull().and(Ok(()))
            }
            Instruction::Quit() => {
                // This should not happen, because the caller already checked.
                Ok(())
            }
            Instruction::NewLine() => {
                self.platform.print("\n");
                Ok(())
            }
            // Instruction::ShowStatus() =>
            Instruction::Verify(branch) => {
                // verify
                // 0OP:189 D 3 verify ?(label)
                // Verification counts a (two byte, unsigned) checksum of the file from $0040
                // onwards (by taking the sum of the values of each byte in the file, modulo
                // $10000) and compares this against the value in the game header, branching if the
                // two values agree. (Early Version 3 games do not have the necessary checksums to
                // make this possible.)
                // The interpreter must stop calculating when the file length (as given in the
                // header) is reached. It is legal for the file to contain more bytes than this,
                // but if so the extra bytes should all be 0. (Some story files are padded out to
                // an exact number of virtual-memory pages.) However, many Infocom story files in
                // fact contain non-zero data in the padding, so interpreters must be sure to
                // exclude the padding from checksum calculations.
                let expected_checksum = self.mem.header().stored_checksum();
                let cond = match expected_checksum {
                    Some(expected_checksum) => expected_checksum == self.mem.header().actual_checksum(),
                    None => true,
                };
                self.cond_branch(cond, branch)
            }
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
            Instruction::Storeb(var_operands) => {
                // storeb
                // VAR:226 2 storeb array byte-index value
                // array->byte-index = value, i.e. stores the given value in the byte at address
                // array+byte-index (which must lie in dynamic memory). (See loadb.)
                let array = self.eval(var_operands.get(0)?)?;
                let byte_index = self.eval(var_operands.get(1)?)?;
                let value = self.eval(var_operands.get(2)?)?;
                self.store_u8(Address::from_byte_address(array + byte_index), value as u8)
            }
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
                let object = Object::from_number(self.eval(var_operands.get(0)?)?);
                let property = Property::from_number(self.eval(var_operands.get(1)?)? as u8);
                let value = self.eval(var_operands.get(2)?)?;
                if let Some(obj_ref) = self.mem.obj_table().get_obj_ref(object)? {
                    if let Some(mut prop_ref) = obj_ref.get_prop_ref(property)? {
                        prop_ref.set(value)
                    } else {
                        Err(RuntimeError::PropertyNotFound(object, property))
                    }
                } else {
                    Ok(())
                }
            }
            Instruction::Sread(var_operands) => {
                // read
                // VAR:228 4 1 sread text parse
                //
                // (Note that Inform internally names the read opcode as aread in Versions 5 and
                // later and sread in Versions 3 and 4.)
                //
                // This opcode reads a whole command from the keyboard (no prompt is automatically
                // displayed). It is legal for this to be called with the cursor at any position on
                // any window.
                let text = Address::from_byte_address(self.eval(var_operands.get(0)?)?);
                let parse = Address::from_byte_address(self.eval(var_operands.get(1)?)?);
                self.read(text, parse)
            }
            Instruction::PrintChar(var_operands) => {
                // print_char
                // VAR:229 5 print_char output-character-code
                // Print a ZSCII character. The operand must be a character code defined in ZSCII
                // for output (see S 3). In particular, it must certainly not be negative or larger
                // than 1023.
                let output_character_code = self.eval(var_operands.get(0)?)?;
                if let Some(character) = zstring::zscii(output_character_code)? {
                    self.platform.print(&character.to_string());
                }
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
            Instruction::Random(var_operands, store) => {
                // random
                // VAR:231 7 random range -> (result)
                // If range is positive, returns a uniformly random number between 1 and range. If
                // range is negative, the random number generator is seeded to that value and the
                // return value is 0. Most interpreters consider giving 0 as range illegal (because
                // they attempt a division with remainder by the range), but correct behaviour is
                // to reseed the generator in as random a way as the interpreter can (e.g. by using
                // the time in milliseconds).
                // (Some version 3 games, such as 'Enchanter' release 29, had a debugging verb
                // #random such that typing, say, #random 14 caused a call of random with -14.)
                let range = self.eval(var_operands.get(0)?)? as i16;
                let val = if range < 0 {
                    self.random.seed(range as u16);
                    0
                } else if range == 0 {
                    self.random.seed_unpredictably();
                    0
                } else {
                    // Assuming that range is inclusive because we start from 1. The spec doesn't
                    // say. Note that we can safely add 1 because we know that range <= 0x7fff.
                    self.random.get(1..range as u16 + 1)
                };
                self.store(store, val)
            }
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
                let variable = self.eval(var_operands.get(0)?)?;
                let variable = self.variable(variable)?;
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

        let int_meta = self.platform.interpreter_metadata();

        // Interpreter number
        // 11.1.3
        // Infocom used the interpreter numbers:
        //
        //    1   DECSystem-20     5   Atari ST           9   Apple IIc
        //    2   Apple IIe        6   IBM PC            10   Apple IIgs
        //    3   Macintosh        7   Commodore 128     11   Tandy Color
        //    4   Amiga            8   Commodore 64
        self.mem.bytes_mut().set_u8(Address::from_byte_address(0x001e), int_meta.interpreter_number).unwrap();

        // Interpreter version
        // 11.1.3.1
        // Interpreter versions are conventionally ASCII codes for upper-case letters in Versions 4
        // and 5 (note that Infocom's Version 6 interpreters just store numbers here).
        self.mem.bytes_mut().set_u8(Address::from_byte_address(0x001f), int_meta.interpreter_version).unwrap();

        // Standard revision number
        // 11.1.5
        // If an interpreter obeys Revision n.m of this document perfectly, as far as anyone knows,
        // then byte $32 should be written with n and byte $33 with m. If it is an earlier
        // (non-standard) interpreter, it should leave these bytes as 0.
        self.mem.bytes_mut().set_u8(Address::from_byte_address(0x0032), int_meta.standard_version_major).unwrap();
        self.mem.bytes_mut().set_u8(Address::from_byte_address(0x0033), int_meta.standard_version_minor).unwrap();
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

    fn eval(&mut self, operand: Operand) -> Result<u16, RuntimeError> {
        match operand {
            Operand::LargeConstant(c) => Ok(c),
            Operand::SmallConstant(c) => Ok(c as u16),
            Operand::Variable(var) => self.eval_var(var),
        }
    }

    fn eval_var(&mut self, var: Variable) -> Result<u16, RuntimeError> {
        match var {
            Variable::PushPullStack => self.frame_mut().pull(),
            Variable::ReadWriteTopOfStack => self.frame_mut().top(),
            Variable::Local(local) => self.frame().local(local),
            Variable::Global(global) => self.mem.globals().get(global),
        }
    }

    fn store(&mut self, store: Store, val: u16) -> Result<(), RuntimeError> {
        match store {
            Variable::PushPullStack => self.frame_mut().push(val),
            Variable::ReadWriteTopOfStack => self.frame_mut().set_top(val),
            Variable::Local(local) => self.frame_mut().set_local(local, val),
            Variable::Global(global) => self.mem.globals_mut().set(global, val),
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
            Ok(Variable::from_byte(val as u8, true))
        } else {
            Err(RuntimeError::InvalidVariable(val))
        }
    }

    fn store_u8(&mut self, addr: Address, val: u8) -> Result<(), RuntimeError> {
        // TODO writability check
        self.mem.bytes_mut().set_u8(addr, val)
    }

    fn store_u16(&mut self, addr: Address, val: u16) -> Result<(), RuntimeError> {
        // TODO writability check
        self.mem.bytes_mut().set_u16(addr, val)
    }

    fn read(&mut self, text: Address, parse: Address) -> Result<(), RuntimeError> {
        match self.version() {
            // In Versions 1 to 3, the status line is automatically redisplayed first.
            V1 | V2 | V3 => {
                self.platform.update_status_line();
            }
        }

        let max_text_len = match self.version() {
            // In Versions 1 to 4, byte 0 of the text-buffer should initially contain the maximum
            // number of letters which can be typed, minus 1 (the interpreter should not accept
            // more than this).
            V1 | V2 | V3 => {
                self.mem.bytes().get_u8(text)? as u16 + 1
            }
            // In Versions 5 and later, ...
        };

        // Initially, byte 0 of the parse-buffer should hold the maximum number of textual words
        // which can be parsed. (If this is n, the buffer must be at least 2 + 4*n bytes long to
        // hold the results of the analysis.)
        let max_words = self.mem.bytes().get_u8(parse)?;
        let max_parse_len = 2 + 4 * max_words as u16;

        // (Interpreters are asked to halt with a suitable error message if the text or
        // parse buffers have length of less than 3 or 6 bytes, respectively: this
        // sometimes occurs due to a previous array being overrun, causing bugs which are
        // very difficult to find.)
        if max_text_len < 3 {
            return Err(RuntimeError::BufferTooSmall(max_text_len, 3));
        }
        if max_parse_len < 6 {
            return Err(RuntimeError::BufferTooSmall(max_parse_len, 6));
        }

        // A sequence of characters is read in from the current input stream until a carriage
        // return (or, in Versions 5 and later, any terminating character) is found.
        let raw_input = self.platform.read_line(max_text_len as usize);
        let input = raw_input.to_lowercase();
        let mut write_addr = text + 1;
        match self.version() {
            V1 | V2 | V3 => {
                // The text typed is reduced to lower case (so that it can tidily be printed back
                // by the program if need be) and stored in bytes 1 onward, with a zero terminator
                // (but without any other terminator, such as a carriage return code). (This means
                // that if byte 0 contains n then the buffer must contain n+1 bytes, which makes it
                // a string array of length n in Inform terminology.)
                let mut bytes_mut = self.mem.bytes_mut();
                for c in input.chars().take(max_text_len as usize) {
                    let byte = if c <= 0xff as char { c as u8 } else { b'?' };
                    bytes_mut.set_u8(write_addr, byte)?;
                    write_addr += 1;
                }
                bytes_mut.set_u8(write_addr, 0)?;
            }
        }
        let input = self.mem.bytes().get_slice(text + 1..write_addr)?.to_vec();

        // Next, lexical analysis is performed on the text (...).

        // The interpreter divides the text into words and looks them up in the dictionary,
        // as described in S 13. The number of words is written in byte 1 and one 4-byte
        // block is written for each word, from byte 2 onwards (except that it should stop
        // before going beyond the maximum number of words specified). Each block consists
        // of the byte address of the word in the dictionary, if it is in the dictionary,
        // or 0 if it isn't; followed by a byte giving the number of letters in the word;
        // and finally a byte giving the position in the text-buffer of the first letter of
        // the word.
        let mut num_words = 0;
        let mut parse_addr = parse + 2;
        for word in self.mem.dict_table().words(input)? {
            let word = word?;
            num_words += 1;
            if num_words <= max_words {
                // println!("{:?}", word);
                self.mem.bytes_mut().set_u16(parse_addr, word.addr().map(|a| a.to_byte_address()).unwrap_or(0))?;
                self.mem.bytes_mut().set_u8(parse_addr + 2, word.len())?;
                self.mem.bytes_mut().set_u8(parse_addr + 3, word.start_idx())?;
                parse_addr += 4;
            }
        }
        self.mem.bytes_mut().set_u8(parse + 1, num_words)?;

        Ok(())
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
            store: Variable::PushPullStack, // Unused.
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

    fn push(&mut self, val: u16) -> Result<(), RuntimeError> {
        if self.stack.len() >= STACK_SIZE_LIMIT {
            return Err(RuntimeError::StackOverflow);
        }
        self.stack.push(val);
        Ok(())
    }

    fn pull(&mut self) -> Result<u16, RuntimeError> {
        self.stack.pop().ok_or(RuntimeError::StackUnderflow)
    }

    fn top(&self) -> Result<u16, RuntimeError> {
        self.stack.last().map(|v| *v).ok_or(RuntimeError::StackUnderflow)
    }

    fn set_top(&mut self, val: u16) -> Result<(), RuntimeError> {
        *self.stack.last_mut().ok_or(RuntimeError::StackUnderflow)? = val;
        Ok(())
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
