use rustyknife::*;
use std::fs;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(StructOpt, Debug)]
#[structopt(name = "basic")]
struct Options {
    #[structopt(name = "FILE", parse(from_os_str))]
    story_file: PathBuf,
}

struct ConsolePlatform {
}

impl Platform for ConsolePlatform {
    fn print(&mut self, string: &str) {
        // TODO probably need to disable line buffering
        print!("{}", string);
    }

    fn next_instr(&mut self, pc: Address, call_stack_depth: usize, instr: &Instruction) {
        eprintln!("{:6}  {:}{:?}", pc, "  ".repeat(call_stack_depth), instr);
    }
}

fn main() {
    let opts = Options::from_args();

    let story_file = fs::read(&opts.story_file)
        .expect(&format!("could not read game file {:?}", &opts.story_file));
    let mem = Memory::from_bytes(story_file)
        .expect(&format!("error in story file {:?}", &opts.story_file));

    // print!("{:}", mem.obj_table().to_tree_string().unwrap());

    let mut platform = ConsolePlatform {};

    let mut z = ZMachine::new(&mut platform, &mem);
    loop {
        z.step().unwrap();
    }
}
