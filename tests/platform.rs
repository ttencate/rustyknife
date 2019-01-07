use rustyknife::*;

pub struct TestPlatform {}

impl TestPlatform {
    pub fn new() -> Self {
        TestPlatform {}
    }
}

impl Platform for TestPlatform {
    fn print(&mut self, string: &str) {
        // TODO probably need to disable line buffering
        print!("{}", string);
    }
}
