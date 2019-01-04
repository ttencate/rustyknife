use crate::{Memory, ZMachine};
use std::fs;

#[test]
fn test_zork1() {
    let f = fs::read("games/zork1.z3").unwrap();
    let s = Memory::from_bytes(f).unwrap();
    let mut z = ZMachine::new(&s);
    loop {
        z.step().unwrap();
    }
}
