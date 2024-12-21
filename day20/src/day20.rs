use std::{env, fs, process};

fn main() {
    let args: Vec<_> = env::args().collect();
    if args.len() == 1 {
        println!("Usage: {} <path to input>", args[0]);
        process::exit(1);
    }

    let raw_input = fs::read_to_string(&args[1]).unwrap();
    println!("{raw_input}");
}
