use crate::bytes::Address;
use crate::errors::RuntimeError;
use std::ops::Range;

// Instruction does not implement Copy because it potentially contains big strings (the Print and
// PrintRet opcodes).
#[derive(Debug, Clone)]
pub enum Instruction {
    // 14. Complete table of opcodes
    // Two-operand opcodes 2OP
    // Note that these don't necessarily have two operands, because they can also appear in VAR
    // form.
    Je(VarOperands, Branch),
    Jl(VarOperands, Branch),
    Jg(VarOperands, Branch),
    DecChk(VarOperands, Branch),
    IncChk(VarOperands, Branch),
    Jin(VarOperands, Branch),
    Test(VarOperands, Branch),
    Or(VarOperands, Store),
    And(VarOperands, Store),
    TestAttr(VarOperands, Branch),
    SetAttr(VarOperands),
    ClearAttr(VarOperands),
    Store(VarOperands),
    InsertObj(VarOperands),
    Loadw(VarOperands, Store),
    Loadb(VarOperands, Store),
    GetProp(VarOperands, Store),
    GetPropAddr(VarOperands, Store),
    GetNextProp(VarOperands, Store),
    Add(VarOperands, Store),
    Sub(VarOperands, Store),
    Mul(VarOperands, Store),
    Div(VarOperands, Store),
    Mod(VarOperands, Store),
    // One-operand opcodes 1OP
    Jz(Operand, Branch),
    GetSibling(Operand, Store, Branch),
    GetChild(Operand, Store, Branch),
    GetParent(Operand, Store),
    GetPropLen(Operand, Store),
    Inc(Operand),
    Dec(Operand),
    PrintAddr(Operand),
    RemoveObj(Operand),
    PrintObj(Operand),
    Ret(Operand),
    Jump(Operand),
    PrintPaddr(Operand),
    Load(Operand, Store),
    Not(Operand, Store),
    // Zero-operand opcodes 0OP
    Rtrue(),
    Rfalse(),
    Print(String),
    PrintRet(String),
    Nop(),
    Save(Branch),
    Restore(Branch),
    Restart(),
    RetPopped(),
    Pop(),
    Quit(),
    NewLine(),
    ShowStatus(),
    Verify(Branch),
    // Variable-operand opcodes VAR
    Call(VarOperands, Store),
    Storew(VarOperands),
    Storeb(VarOperands),
    PutProp(VarOperands),
    Sread(VarOperands),
    PrintChar(VarOperands),
    PrintNum(VarOperands),
    Random(VarOperands, Store),
    Push(VarOperands),
    Pull(VarOperands),
    SplitWindow(VarOperands),
    SetWindow(VarOperands),
    OutputStream(VarOperands),
    InputStream(VarOperands),
    // Extended opcodes EXT
    // None supported at the moment.
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Local(u8);

impl Local {
    pub fn from_index(idx: usize) -> Local {
        Local((idx + 1) as u8)
    }

    pub fn index(self) -> usize {
        self.0 as usize - 1
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Global(u8);

impl Global {
    pub fn from_index(index: usize) -> Global {
        Global(index as u8 + 0x10)
    }

    pub fn index(self) -> usize {
        self.0 as usize - 0x10
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Variable {
    // 6.3
    // Writing to the stack pointer (variable number $00) pushes a value onto the stack; reading
    // from it pulls a value off.
    PushPullStack,
    // 6.3.4
    // In the seven opcodes that take indirect variable references (inc, dec, inc_chk, dec_chk,
    // load, store, pull), an indirect reference to the stack pointer does not push or pull the top
    // item of the stack - it is read or written in place.
    ReadWriteTopOfStack,
    Local(Local),
    Global(Global),
}

impl Variable {
    pub fn from_byte(byte: u8, indirect: bool) -> Variable {
        // 4.2.2
        match byte {
            // Variable number $00 refers to the top of the stack, ...
            0 => if indirect {
                Variable::ReadWriteTopOfStack
            } else {
                Variable::PushPullStack
            },
            // ... $01 to $0f mean the local variables of the current routine ...
            0x01..=0x0f => Variable::Local(Local(byte)),
            // ... and $10 to $ff mean the global variables.
            _ => Variable::Global(Global(byte)),
        }
    }
}

pub type Store = Variable;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Operand {
    // 4.2.1
    // Large constants, like all 2-byte words of data in the Z-machine, are stored with most
    // significant byte first (e.g. $2478 is stored as $24 followed by $78). A 'large constant' may
    // in fact be a small number.
    LargeConstant(u16),
    // 4.2.3 (part)
    // Some instructions take as an operand a "variable by reference": for instance, inc has one
    // operand, the reference number of a variable to increment. This operand usually has type
    // 'Small constant' (and Inform automatically assembles a line like @inc turns by writing the
    // operand turns as a small constant with value the reference number of the variable turns).
    SmallConstant(u8),
    // 4.2.3
    // The type 'Variable' really means "variable by value".
    Variable(Variable),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct VarOperands(Vec<Operand>);

impl VarOperands {
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn get(&self, idx: usize) -> Result<Operand, RuntimeError> {
        if idx < self.len() {
            Ok(self.0[idx])
        } else {
            Err(RuntimeError::NotEnoughOperands(idx, self.len()))
        }
    }

    pub fn get_slice(&self, range: Range<usize>) -> Result<&[Operand], RuntimeError> {
        if range.start < self.len() && range.end <= self.len() || range.start == range.end {
            Ok(&self.0[range])
        } else {
            Err(RuntimeError::NotEnoughOperands(range.end - 1, self.len()))
        }
    }
}

impl From<Vec<Operand>> for VarOperands {
    fn from(operands: Vec<Operand>) -> VarOperands {
        VarOperands(operands)
    }
}

#[derive(Debug, Clone)]
pub struct Branch(bool, BranchTarget);

impl Branch {
    pub fn new(cond: bool, target: BranchTarget) -> Branch {
        Branch(cond, target)
    }

    pub fn matches_cond(&self, cond: bool) -> bool {
        cond == self.0
    }

    pub fn target(&self) -> BranchTarget {
        self.1
    }
}

#[derive(Debug, Clone, Copy)]
pub enum BranchTarget {
    ReturnFalse,
    ReturnTrue,
    ToAddress(Address),
}
