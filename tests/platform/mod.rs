use difference::Changeset;
use rustyknife::*;
use std::collections::VecDeque;
use std::mem;

pub struct TestPlatform {
    trace: bool,
    inputs: VecDeque<String>,
    output: String,
}

#[allow(dead_code)]
impl TestPlatform {
    pub fn new() -> Self {
        TestPlatform {
            trace: false,
            inputs: VecDeque::new(),
            output: String::new(),
        }
    }

    pub fn enable_trace(&mut self) {
        self.trace = true;
    }

    pub fn add_input(&mut self, line: &str) {
        self.inputs.push_back(line.to_string());
    }

    pub fn add_inputs(&mut self, lines: &[&str]) {
        for line in lines {
            self.inputs.push_back(line.to_string());
        }
    }

    pub fn take_output(&mut self) -> String {
        let mut output = String::new();
        mem::swap(&mut self.output, &mut output);
        output
    }

    pub fn expect_output(&mut self, expected_output: &str) {
        let actual_output = self.take_output();
        let diff = Changeset::new(&actual_output, &expected_output, "");
        assert_eq!(actual_output, expected_output);
        assert!(actual_output == expected_output,
            "Actual output did not match expected output. Difference (green = expected, red = actual):\n\n{}\n", diff);
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

    fn read_line(&mut self, _max_len_hint: usize) -> String {
        self.inputs.pop_front().expect("more inputs were read than were provided")
    }

    fn next_instr(&mut self, pc: Address, call_stack_depth: usize, instr: &Instruction) {
        if self.trace {
            eprintln!("{:6}  {:}{:?}", pc, "  ".repeat(call_stack_depth), instr);
        }
    }
}
