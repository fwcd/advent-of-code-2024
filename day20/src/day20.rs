use std::{env, fs, process};

fn main() {
    let args: Vec<_> = env::args().collect();
    if args.len() == 1 {
        println!("Usage: {} <path to input>", args[0]);
        process::exit(1);
    }

    let raw = fs::read_to_string(&args[1]).unwrap();
    let matrix: Vec<_> = raw.trim().split("\n").collect();

    println!("{matrix:?}");
}
