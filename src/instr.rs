use crate::bytes::Address;

// Instruction does not implement Copy because it potentially contains big strings (the Print and
// PrintRet opcodes).
#[derive(Debug, Clone)]
pub enum Instruction {
    // 14. Complete table of opcodes
    // Two-operand opcodes 2OP
    Je(Operand, Operand, Branch),
    Jl(Operand, Operand, Branch),
    Jg(Operand, Operand, Branch),
    DecChk(Operand, Operand, Branch),
    IncChk(Operand, Operand, Branch),
    Jin(Operand, Operand, Branch),
    Test(Operand, Operand, Branch),
    Or(Operand, Operand, Store),
    And(Operand, Operand, Store),
    TestAttr(Operand, Operand, Branch),
    SetAttr(Operand, Operand),
    ClearAttr(Operand, Operand),
    Store(Operand, Operand),
    InsertObj(Operand, Operand),
    Loadw(Operand, Operand, Store),
    Loadb(Operand, Operand, Store),
    GetProp(Operand, Operand, Store),
    GetPropAddr(Operand, Operand, Store),
    GetNextProp(Operand, Operand, Store),
    Add(Operand, Operand, Store),
    Sub(Operand, Operand, Store),
    Mul(Operand, Operand, Store),
    Div(Operand, Operand, Store),
    Mod(Operand, Operand, Store),
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
    pub fn index(self) -> usize {
        self.0 as usize - 0x10
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Variable {
    TopOfStack,
    Local(Local),
    Global(Global),
}

impl Variable {
    pub fn from_byte(byte: u8) -> Variable {
        // 4.2.2
        match byte {
            // Variable number $00 refers to the top of the stack, ...
            0 => Variable::TopOfStack,
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

pub type VarOperands = Vec<Operand>;

#[derive(Debug, Clone)]
pub struct Branch {
    pub on_true: bool,
    pub target: BranchTarget,
}

#[derive(Debug, Clone)]
pub enum BranchTarget {
    ReturnFalse,
    ReturnTrue,
    ToAddress(Address),
}