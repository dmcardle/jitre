// This program endeavors to translate classical regular expressions into X86_64
// machine code. This is probably a terrible idea, but maybe it will be fast!

#![feature(split_inclusive)]
#![feature(test)]

extern crate libc;

pub mod linear_collections;
pub mod machine;
pub mod nfa;
pub mod regex;
