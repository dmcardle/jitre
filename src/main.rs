// This program endeavors to translate classical regular expressions into X86_64
// machine code. This is probably a terrible idea, but maybe it will be fast!

#![feature(split_inclusive)]

extern crate libc;

mod machine;
mod nfa;
mod regex;

use crate::machine::X64Instr;
use crate::regex::Regex;

fn regex_compile(r: &Regex) -> Vec<X64Instr> {
    panic!("Not implemented")
}

fn main() {
    println!("TBD!");
}
