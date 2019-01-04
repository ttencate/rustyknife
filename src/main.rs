use rustyknife::{Memory, ZMachine};
use std::fs;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(StructOpt, Debug)]
#[structopt(name = "basic")]
struct Options {
    #[structopt(name = "FILE", parse(from_os_str))]
    story_file: PathBuf,
}

fn main() {
    let opts = Options::from_args();

    let story_file = fs::read(&opts.story_file)
        .expect(&format!("could not read game file {:?}", &opts.story_file));
    let s = Memory::from_bytes(story_file)
        .expect(&format!("error in story file {:?}", &opts.story_file));
    let mut z = ZMachine::new(&s);
    loop {
        z.step().unwrap();
        println!("{:}", z);
    }
}
