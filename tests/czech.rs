mod platform;

use difference::Changeset;
use crate::platform::TestPlatform;
use rustyknife::*;
use std::fs;

#[test]
fn test_czech() {
    let mut platform = TestPlatform::new();
    let data = fs::read("tests/czech/czech.z3").unwrap();
    // platform.enable_trace();
    println!("{}", Memory::wrap(data.clone().into()).unwrap().obj_table().to_tree_string().unwrap());
    let mut z = ZMachine::new(&mut platform, data).unwrap();
    if let Err(err) = z.run() {
        panic!("{}\nOutput:\n{}", err, platform.take_output());
    }

    let actual_output = platform.take_output();
    let expected_output = String::from_utf8(fs::read("tests/czech/czech.out3").unwrap()).unwrap();
    let diff = Changeset::new(&actual_output, &expected_output, "");
    assert_eq!(actual_output, expected_output);
    assert!(actual_output == expected_output,
        "CZECH output did not match expected output. Difference (green = expected, red = actual):\n\n{}\n", diff);
}
