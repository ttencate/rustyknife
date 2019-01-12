mod platform;

use crate::platform::TestPlatform;
use rustyknife::*;
use std::fs;

#[test]
#[ignore]
fn test_zork1() {
    let mut platform = TestPlatform::new();
    let data = fs::read("tests/zork1/zork1.z3").unwrap();

    platform.add_input("look");
    platform.add_input("quit");
    let mut z = ZMachine::new(&mut platform, data).unwrap();
    if let Err(err) = z.run() {
        panic!("{}\nOutput:\n{}", err, platform.take_output());
    }
    platform.expect_output(&"");
}
