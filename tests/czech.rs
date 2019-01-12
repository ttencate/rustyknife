mod platform;

use crate::platform::TestPlatform;
use rustyknife::*;
use std::fs;

#[test]
fn test_czech() {
    let mut platform = TestPlatform::new();
    let data = fs::read("tests/czech/czech.z3").unwrap();
    // platform.enable_trace();
    // println!("{}", Memory::wrap(data.clone().into()).unwrap().obj_table().to_tree_string().unwrap());
    let mut z = ZMachine::new(&mut platform, data).unwrap();

    if let Err(err) = z.run() {
        panic!("{}\nOutput:\n{}", err, platform.take_output());
    }
    let expected_output = String::from_utf8(fs::read("tests/czech/czech.out3").unwrap()).unwrap();
    platform.expect_output(&expected_output);
}
