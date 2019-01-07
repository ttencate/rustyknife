mod platform;

use crate::platform::TestPlatform;
use rustyknife::*;
use std::fs;

#[test]
fn test_czech() {
    let mut platform = TestPlatform::new();
    // platform.enable_trace();
    let data = fs::read("tests/czech/czech.z3").unwrap();
    let mut z = ZMachine::new(&mut platform, data).unwrap();
    loop {
        z.step().unwrap();
    }
}
