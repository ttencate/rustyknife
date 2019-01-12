mod platform;

use crate::platform::TestPlatform;
use rustyknife::*;
use std::fs;

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
