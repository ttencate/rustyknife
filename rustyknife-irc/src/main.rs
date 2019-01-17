#![feature(unsized_locals)]

use irc::client::prelude::*;
use irc::error::IrcError;
use rustyknife::*;
use std::fs;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(StructOpt, Debug)]
#[structopt(name = "basic")]
struct Options {
    #[structopt(name = "FILE", parse(from_os_str))]
    story_file: PathBuf,
    // TODO reinstate
    #[structopt(short = "t", long = "trace", help = "print Z-machine instructions to stderr as they are executed")]
    trace: bool,
    #[structopt(short = "s", long = "server", help = "hostname of IRC server")]
    server: String,
    #[structopt(short = "p", long = "port", help = "port number of IRC server", default_value = "6667")]
    port: u16,
    #[structopt(short = "n", long = "nickname", help = "nickname to use on IRC server")]
    nickname: String,
    #[structopt(short = "c", long = "channel", help = "channel to join on IRC server")]
    channel: String,
}

fn run() -> Result<(), IrcError> {
    let opts = Options::from_args();

    let story_file = fs::read(&opts.story_file)
        .expect(&format!("could not read game file {:?}", &opts.story_file));
    let mut zmachine = ZMachine::new(story_file.clone())
        .expect(&format!("error in story file {:?}", &opts.story_file));

    let config = Config {
        server: Some(opts.server.to_owned()),
        channels: Some(vec![opts.channel.to_owned()]),
        nickname: Some(opts.nickname.to_owned()),
        user_info: Some("A Z-machine bot hosting interactive fiction games".to_string()),
        ..Config::default()
    };
    let client = IrcClient::from_config(config)?;
    eprintln!("Connecting to {}...", opts.server);
    client.identify()?;
    eprintln!("Connected to {}", opts.server);

    let mut bot = Bot {
        continuation: Some(zmachine.start()),
        client: &client,
        channel: opts.channel.to_owned(),
        joined: false,
        output: String::new(),
    };
    bot.run()
}

struct Bot<'a> {
    continuation: Option<Result<Continuation<'a>, RuntimeError>>,
    client: &'a IrcClient,
    channel: String,
    joined: bool,
    output: String,
}

impl<'a> Bot<'a> {
    fn run(&mut self) -> Result<(), IrcError> {
        self.client.for_each_incoming(|msg| self.handle_msg(msg))
    }

    fn handle_msg(&mut self, msg: Message) {
        match &msg.command {
            Command::JOIN(chan, None, None) => if *chan == self.channel {
                self.joined = true;
                self.run_until_read();
            }
            Command::PRIVMSG(target, message) if self.joined => {
                if *target == self.channel {
                    if let Ok(Continuation::ReadLine(next)) = self.continuation.take().unwrap() {
                        self.continuation = Some(next(&message));
                    }
                    self.run_until_read();
                }
            }
            _ => {}
        }
    }

    fn run_until_read(&mut self) {
        loop {
            match self.continuation.take().unwrap() {
                Ok(cont) => {
                    match cont {
                        Continuation::Step(next) => {
                            self.continuation = Some(next());
                        }
                        Continuation::UpdateStatusLine(status_line, next) => {
                            let topic = match status_line.progress {
                                Progress::Score { score, turns } =>
                                    format!("Score: {:3} | Turns: {:4} | {}",
                                            score, turns, status_line.location),
                                Progress::Time { hours, minutes } =>
                                    format!("Time: {}:{:02} | {}",
                                            hours, minutes, status_line.location),
                            };
                            self.set_topic(&topic);
                            self.continuation = Some(next());
                        }
                        Continuation::Print(string, next) => {
                            self.print(&string);
                            self.continuation = Some(next());
                        }
                        Continuation::ReadLine(next) => {
                            self.prompt();
                            self.continuation = Some(Ok(Continuation::ReadLine(next)));
                            return;
                        }
                        Continuation::Quit => {
                            self.panic("Game quit");
                        }
                    }
                }
                Err(err) => {
                    self.panic(err);
                }
            }
        }
    }

    fn set_topic(&self, topic: &str) {
        self.client.send_topic(&self.channel, topic).unwrap(); // TODO not unwrap
    }

    fn say(&self, text: &str) {
        let text = if text.is_empty() { " " } else { text }; // Sending empty messages is not possible.
        self.client.send_privmsg(&self.channel, text).unwrap(); // TODO not unwrap
    }

    fn print(&mut self, text: &str) {
        self.output.push_str(text);
        if let Some(last_newline) = self.output.rfind("\n") {
            for line in self.output[0..last_newline + 1].lines() {
                self.say(line);
            }
            self.output = self.output[last_newline + 1..].to_string();
        }
    }

    fn prompt(&mut self) {
        // Printing a lone ">" in IRC is weird, so we suppress it. Not sure if all games print
        // exactly this prompt, so this might require some tweaking (regex?).
        if self.output != ">" {
            self.say(&self.output);
        }
        self.output = String::new();
    }

    fn panic<E: std::fmt::Display>(&self, err: E) -> ! {
        self.say(&format!("Fatal error: {}", &err));
        self.client.send_quit("eaten by a grue");
        panic!("Fatal error: {}", err);
    }
}

fn main() {
    if let Err(err) = run() {
        eprintln!("Fatal error: {}", err);
        std::process::exit(1);
    }
}
