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
    let mut mem = Memory::from_bytes(story_file)
        .expect(&format!("error in story file {:?}", &opts.story_file));

    print!("{:}", mem.obj_table().to_tree_string().unwrap());

    // let mut z = ZMachine::new(&mem);
    // loop {
    //     z.step().unwrap();
    // }
}
