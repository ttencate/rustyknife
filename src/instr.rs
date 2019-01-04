use crate::bytes::ByteAddress;

#[derive(Debug)]
pub struct Instruction {
    pub opcode: Opcode,
    pub operands: Vec<Operand>,
    pub store_var: Option<Variable>,
    pub branch: Option<Branch>,
    pub string: Option<String>,
}

// 14. Complete table of opcodes
#[derive(Debug, Clone, Copy)]
pub enum Opcode {
    // Two-operand opcodes 2OP
    Je,
    Jl,
    Jg,
    DecChk,
    IncChk,
    Jin,
    Test,
    Or,
    And,
    TestAttr,
    SetAttr,
    ClearAttr,
    Store,
    InsertObj,
    Loadw,
    Loadb,
    GetProp,
    GetPropAddr,
    GetNextProp,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    // One-operand opcodes 1OP
    Jz,
    GetSibling,
    GetChild,
    GetParent,
    GetPropLen,
    Inc,
    Dec,
    PrintAddr,
    RemoveObj,
    PrintObj,
    Ret,
    Jump,
    PrintPaddr,
    Load,
    Not,
    // Zero-operand opcodes 0OP
    Rtrue,
    Rfalse,
    Print,
    PrintRet,
    Nop,
    Save,
    Restore,
    Restart,
    RetPopped,
    Pop,
    Quit,
    NewLine,
    ShowStatus,
    Verify,
    // Variable-operand opcodes VAR
    Call,
    Storew,
    Storeb,
    PutProp,
    Sread,
    PrintChar,
    PrintNum,
    Random,
    Push,
    Pull,
    SplitWindow,
    SetWindow,
    OutputStream,
    InputStream,
    // Extended opcodes EXT
    // None supported at the moment.
}

impl Opcode {
    pub fn has_store(&self) -> bool {
        match self {
            Opcode::Or | Opcode::And | Opcode::Loadw | Opcode::Loadb | Opcode::GetProp |
                Opcode::GetPropAddr | Opcode::GetNextProp | Opcode::Add | Opcode::Sub | Opcode::Mul
                | Opcode::Div | Opcode::Mod | Opcode::GetSibling | Opcode::GetChild |
                Opcode::GetParent | Opcode::GetPropLen | Opcode::Load | Opcode::Not | Opcode::Call
                | Opcode::Random => true,
            _ => false,
        }
    }

    pub fn has_branch(&self) -> bool {
        match self {
            Opcode::Je | Opcode::Jl | Opcode::Jg | Opcode::DecChk | Opcode::IncChk | Opcode::Jin |
                Opcode::Test | Opcode::TestAttr | Opcode::Jz | Opcode::GetSibling |
                Opcode::GetChild | Opcode::GetParent | Opcode::Save | Opcode::Restore |
                Opcode::Verify => true,
            _ => false,
        }
    }

    pub fn has_string(&self) -> bool {
        match self {
            Opcode::Print | Opcode::PrintRet => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Variable {
    TopOfStack,
    Local(u8),
    Global(u8),
}

impl Variable {
    pub fn from_byte(byte: u8) -> Variable {
        // 4.2.2
        match byte {
            // Variable number $00 refers to the top of the stack, ...
            0 => Variable::TopOfStack,
            // ... $01 to $0f mean the local variables of the current routine ...
            0x01..=0x0f => Variable::Local(byte),
            // ... and $10 to $ff mean the global variables.
            _ => Variable::Global(byte),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
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

#[derive(Debug)]
pub struct Branch {
    pub on_true: bool,
    pub target: BranchTarget,
}

#[derive(Debug)]
pub enum BranchTarget {
    ReturnFalse,
    ReturnTrue,
    ToAddress(ByteAddress),
}
