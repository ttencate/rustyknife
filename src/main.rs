// TODO pull this out into a separate rustyknife_console crate
use rustyknife::*;
use std::fs;
use std::path::PathBuf;
use structopt::StructOpt;

struct ConsolePlatform {
    trace: bool,
}

impl ConsolePlatform {
    pub fn new() -> Self {
        ConsolePlatform {
            trace: false,
        }
    }

    pub fn set_trace(&mut self, trace: bool) {
        self.trace = trace;
    }
}

impl Platform for ConsolePlatform {
    fn print(&mut self, string: &str) {
        // TODO probably need to disable line buffering
        print!("{}", string);
    }

    fn next_instr(&mut self, pc: Address, call_stack_depth: usize, instr: &Instruction) {
        if self.trace {
            eprintln!("{:6}  {}{:?}", pc, "  ".repeat(call_stack_depth), instr);
        }
    }
}

#[derive(StructOpt, Debug)]
#[structopt(name = "basic")]
struct Options {
    #[structopt(name = "FILE", parse(from_os_str))]
    story_file: PathBuf,
    #[structopt(short = "t", long = "trace", help = "print Z-machine instructions to stderr as they are executed")]
    trace: bool,
}

fn run() -> i32 {
    let opts = Options::from_args();

    let story_file = fs::read(&opts.story_file)
        .expect(&format!("could not read game file {:?}", &opts.story_file));

    // let bytes = Bytes::from(data);
    // let mem = Memory::wrap(bytes)
    //     .expect(&format!("error in story file {:?}", &opts.story_file));
    // print!("{:}", mem.obj_table().to_tree_string().unwrap());

    let mut platform = ConsolePlatform::new();
    platform.set_trace(opts.trace);

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
