// TODO pull this out into a separate rustyknife_console crate
use rustyknife::*;
use std::fs;
use std::io::{BufRead, Write};
use std::path::PathBuf;
use structopt::StructOpt;

struct ConsolePlatform<'a> {
    trace: bool,
    input: &'a mut BufRead,
}

impl<'a> ConsolePlatform<'a> {
    pub fn new(input: &'a mut BufRead) -> Self {
        ConsolePlatform {
            trace: false,
            input: input,
        }
    }

    pub fn set_trace(&mut self, trace: bool) {
        self.trace = trace;
    }
}

impl<'a> Platform for ConsolePlatform<'a> {
    fn print(&mut self, string: &str) {
        // Note that stdout is typically line-buffered, but we flush it in read_line().
        print!("{}", string);
    }

    fn next_instr(&mut self, pc: Address, call_stack_depth: usize, instr: &Instruction) {
        if self.trace {
            eprintln!("{:6}  {}{:?}", pc, "  ".repeat(call_stack_depth), instr);
        }
    }

    fn read_line(&mut self, _max_len_hint: usize) -> String {
        std::io::stdout().flush().unwrap();
        let mut buf = String::new();
        self.input.read_line(&mut buf).unwrap();
        // Remove trailing newline.
        buf.pop().expect("unexpected EOF on stdin");
        buf
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

    let stdin = std::io::stdin();
    let mut input = stdin.lock();
    let mut platform = ConsolePlatform::new(&mut input);
    platform.set_trace(opts.trace);

    let mut z = ZMachine::new(&mut platform, story_file)
        .expect(&format!("error in story file {:?}", &opts.story_file));
    if let Err(err) = z.run() {
        eprintln!("Interpreter error: {}", err);
        return 1;
    }

    0
}

fn main() {
    std::process::exit(run());
}
