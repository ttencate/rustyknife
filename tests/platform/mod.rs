use rustyknife::*;
use std::mem;

pub struct TestPlatform {
    trace: bool,
    output: String,
}

impl TestPlatform {
    pub fn new() -> Self {
        TestPlatform {
            trace: false,
            output: String::new(),
        }
    }

    #[allow(dead_code)]
    pub fn enable_trace(&mut self) {
        self.trace = true;
    }

    #[allow(dead_code)]
    pub fn take_output(&mut self) -> String {
        let mut output = String::new();
        mem::swap(&mut self.output, &mut output);
        output
    }
}

impl Platform for TestPlatform {
    fn interpreter_metadata(&self) -> InterpreterMetadata {
        // These are configured to match the expected output of the CZECH test suite.
        InterpreterMetadata {
            interpreter_number: 0,
            interpreter_version: 0,
            standard_version_major: 1,
            standard_version_minor: 0,
        }
    }

    fn print(&mut self, string: &str) {
        self.output += string;
    }

    fn next_instr(&mut self, pc: Address, call_stack_depth: usize, instr: &Instruction) {
        if self.trace {
            eprintln!("{:6}  {:}{:?}", pc, "  ".repeat(call_stack_depth), instr);
        }
    }
}
