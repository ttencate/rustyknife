mod platform;

use crate::platform::TestPlatform;
use rustyknife::*;
use std::fs;

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
