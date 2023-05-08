//! This library endeavors to translate classical regular expressions into
//! X86_64 machine code. This is probably a terrible idea, but maybe it will be
//! fast!
//!
//! The string containing a regular expression undergoes a series of
//! transformations, ultimately becoming machine code:
//! 1. [str]
//! 2. to [regex::Regex]
//! 3. to [nfa::Nfa]
//! 4. to [nfa::Dfa]
//! 5. to machine code (in progress)

#![feature(split_inclusive)]
#![feature(test)]

extern crate libc;

pub mod linear_collections;
pub mod machine;
pub mod nfa;
pub mod regex;
