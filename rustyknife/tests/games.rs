#![feature(unsized_locals)]

use difference::Changeset;
use rustyknife::*;
use std::fs;

fn make_zmachine(filename: &str) -> ZMachine {
    let data = fs::read(filename).unwrap();
    ZMachine::new(data).unwrap()
}

fn run_zmachine(mut zmachine: ZMachine, inputs: &[&str]) -> String {
    let mut input = inputs.iter();

    let mut output = String::new();

    let mut continuation = zmachine.start();
    loop {
        match continuation {
            Ok(cont) => match cont {
                Continuation::Step(next) => {
                    continuation = next();
                }
                Continuation::UpdateStatusLine(_status_line, next) => {
                    continuation = next();
                }
                Continuation::Print(string, next) => {
                    output += &string;
                    continuation = next();
                }
                Continuation::ReadLine(next) => {
                    let line = input.next().unwrap();
                    continuation = next(&line);
                }
                Continuation::Quit => {
                    break;
                }
            }
            Err(err) => {
                panic!("Z-machine generated a runtime error: {}\nOutput so far:\n{}",
                       err, output);
            }
        }
    }

    output
}

fn read_output(filename: &str) -> String {
    String::from_utf8(fs::read(filename).unwrap()).unwrap().replace("\r\n", "\n")
}

fn assert_eq_with_diff(actual: &str, expected: &str) {
    let diff = Changeset::new(&actual, &expected, "");
    assert!(actual == expected,
        "Actual output did not match expected output. Difference (green = expected, red = actual):\n\n{}\n", diff);
}

#[test]
fn test_strictz() {
    let zmachine = make_zmachine("tests/strictz/strictz.z3");

    let output = run_zmachine(zmachine, &[&"N"]);

    assert_eq_with_diff(&output, &read_output("tests/strictz/strictz.out3"));
}

#[test]
fn test_czech() {
    let mut zmachine = make_zmachine("tests/czech/czech.z3");
    zmachine.set_interpreter_metadata(InterpreterMetadata {
        interpreter_number: 0,
        interpreter_version: 0,
        standard_version_major: 1,
        standard_version_minor: 0,
    });
    zmachine.restart();

    let output = run_zmachine(zmachine, &[]);

    assert_eq_with_diff(&output, &read_output("tests/czech/czech.out3"));
}

#[test]
fn test_zork1() {
    let zmachine = make_zmachine("tests/zork1/zork1.z3");
    
    let output = run_zmachine(zmachine, &[
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
        &"y",
    ]);

    assert_eq_with_diff(&output, &read_output("tests/zork1/zork1.out3"));
}
