use crate::platform::TestPlatform;
use rustyknife::*;
use std::fs;

mod platform;

#[test]
fn test_zork1() {
    let mut platform = TestPlatform::new();
    let data = fs::read("tests/zork1/zork1.z3").unwrap();
    let mut z = ZMachine::new(&mut platform, data).unwrap();
    loop {
        z.step().unwrap();
    }
}
