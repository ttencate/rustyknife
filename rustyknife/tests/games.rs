use difference::Changeset;
use rustyknife::*;
use std::collections::VecDeque;
use std::fs;
use std::mem;

#[test]
fn test_strictz() {
    let mut platform = TestPlatform::new();
    let data = fs::read("tests/strictz/strictz.z3").unwrap();
    
    // platform.enable_trace();
    platform.add_input("N");

    let mut z = ZMachine::new(&mut platform, data).unwrap();
    if let Err(err) = z.run() {
        panic!("{}\nOutput:\n{}", err, platform.take_output());
    }
    let expected_output = String::from_utf8(fs::read("tests/strictz/strictz.out3").unwrap()).unwrap();
    platform.expect_output(&expected_output);
}

#[test]
fn test_czech() {
    let mut platform = TestPlatform::new();
    let data = fs::read("tests/czech/czech.z3").unwrap();

    // platform.enable_trace();
    // println!("{}", Memory::wrap(data.clone().into()).unwrap().obj_table().to_tree_string().unwrap());
    let mut z = ZMachine::new(&mut platform, data).unwrap();
    z.set_interpreter_metadata(InterpreterMetadata {
        interpreter_number: 0,
        interpreter_version: 0,
        standard_version_major: 1,
        standard_version_minor: 0,
    });
    z.restart();

    if let Err(err) = z.run() {
        panic!("{}\nOutput:\n{}", err, platform.take_output());
    }
    let expected_output = String::from_utf8(fs::read("tests/czech/czech.out3").unwrap()).unwrap();
    platform.expect_output(&expected_output);
}

#[test]
fn test_zork1() {
    let mut platform = TestPlatform::new();
    let data = fs::read("tests/zork1/zork1.z3").unwrap();

    platform.add_inputs(&[
        &"open mailbox",
        &"take leaflet and read it",
        &"go north",
        &"e",
        &"open window and enter",
        &"up",
        &"down",
        &"take bottle and sack",
        &"open sack",
        &"inventory",
        &"west",
        &"move rug and open trap door",
        &"take sword and turn on lamp",
        &"go down" /* and realise that you left the lamp behind */,
        &"quit",
        &"y"]);

    let mut z = ZMachine::new(&mut platform, data).unwrap();
    if let Err(err) = z.run() {
        panic!("{}\nOutput:\n{}", err, platform.take_output());
    }
    let expected_output = String::from_utf8(fs::read("tests/zork1/zork1.out3").unwrap()).unwrap();
    platform.expect_output(&expected_output);
}

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
        assert!(actual_output == expected_output,
            "Actual output did not match expected output. Difference (green = expected, red = actual):\n\n{}\n", diff);
    }
}

impl Platform for TestPlatform {
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
