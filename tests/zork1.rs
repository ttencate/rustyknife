mod platform;

use crate::platform::TestPlatform;
use rustyknife::*;
use std::fs;

#[test]
fn test_zork1() {
    let mut platform = TestPlatform::new();
    let data = fs::read("tests/zork1/zork1.z3").unwrap();
    let mut _z = ZMachine::new(&mut platform, data).unwrap();
    // TODO check some input and output here
    // loop {
    //     z.step().unwrap();
    // }
}
