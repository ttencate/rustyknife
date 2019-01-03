use crate::{StoryFile, ZMachine};
use std::fs;

#[test]
fn test_zork1() {
    let f = fs::read("games/zork1.z3").unwrap();
    let s = StoryFile::from_bytes(f).unwrap();
    let mut z = ZMachine::new(&s);
    loop {
        z.step().unwrap();
    }
}
