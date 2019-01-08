use rustyknife::*;
use std::fs;
use std::path::PathBuf;
use structopt::StructOpt;

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

#[derive(StructOpt, Debug)]
#[structopt(name = "basic")]
struct Options {
    #[structopt(name = "FILE", parse(from_os_str))]
    story_file: PathBuf,
}

fn run() -> i32 {
    let opts = Options::from_args();

    let story_file = fs::read(&opts.story_file)
        .expect(&format!("could not read game file {:?}", &opts.story_file));

    // let bytes = Bytes::from(data);
    // let mem = Memory::wrap(bytes)
    //     .expect(&format!("error in story file {:?}", &opts.story_file));
    // print!("{:}", mem.obj_table().to_tree_string().unwrap());

    let mut platform = ConsolePlatform {};

    let mut z = ZMachine::new(&mut platform, story_file)
        .expect(&format!("error in story file {:?}", &opts.story_file));
    if let Err(err) = z.run() {
        eprintln!("{}", err);
        return 1;
    }

    0
}

fn main() {
    std::process::exit(run());
}
