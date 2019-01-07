use rustyknife::*;

pub struct TestPlatform {
    trace: bool,
}

impl TestPlatform {
    pub fn new() -> Self {
        TestPlatform {
            trace: false,
        }
    }

    #[allow(dead_code)]
    pub fn enable_trace(&mut self) {
        self.trace = true;
    }
}

impl Platform for TestPlatform {
    fn print(&mut self, string: &str) {
        print!("{}", string);
    }

    fn next_instr(&mut self, pc: Address, call_stack_depth: usize, instr: &Instruction) {
        if self.trace {
            eprintln!("{:6}  {:}{:?}", pc, "  ".repeat(call_stack_depth), instr);
        }
    }
}
