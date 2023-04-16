// This program endeavors to translate classical regular expressions into X86_64
// machine code. This is probably a terrible idea, but maybe it will be fast!

enum Regex {
    Literal(String),
    Concat(Vec<Regex>),
    Choice(Vec<Regex>),
    Repeat(Box<Regex>),
}

// Interprets the regex |r| against |line|. If it matches, the first return
// value is true, and the second is the non-matching suffix of |line|.
// Otherwise, the return value is (false, None).
fn regex_match<'a>(r: &'a Regex, line: &'a str) -> (bool, Option<&'a str>) {
    match r {
        Regex::Literal(s) => {
            if line.len() < s.len() {
                return (false, None);
            }
            let (before, after) = line.split_at(s.len());
            let matches = before.chars().zip(s.chars()).all(|(c1, c2)| c1 == c2);
            (matches, Some(after))
        }
        Regex::Concat(regexes) => {
            let mut line = &line[..];
            for r in regexes {
                let (is_match, after) = regex_match(r, line);
                if !is_match {
                    return (false, None);
                }
                line = after.unwrap();
            }
            (true, Some(line))
        }
        Regex::Choice(regexes) => {
            for r in regexes {
                let (is_match, after) = regex_match(r, line);
                if is_match {
                    return (true, after);
                }
            }
            (false, None)
        }
        Regex::Repeat(r) => {
            let mut line = &line[..];
            loop {
                let (is_match, after) = regex_match(r, line);
                if !is_match {
                    break;
                }
                line = after.unwrap();
            }
            (true, Some(line))
        }
    }
}

enum X64Reg {
    Rdi,
    Rsi,
    Rdx,
    Rcx,
    R8,
    R9,
}

type LabelName = String;

enum X64Instr {
    Label(LabelName), // Not technically an instruction.
    Cmp(X64Reg, X64Reg),
    Je(LabelName),
    Jne(LabelName),
    Jmp(LabelName),
}

fn regex_compile(r: &Regex) -> Vec<X64Instr> {
    panic!("Not implemented")
}

fn machine_lower(instrs: &[X64Instr]) -> Vec<u8> {
    panic!("Not implemented")
}

// This is probably going to be super unsafe. Write |code| to a buffer and then
// execute it?
fn run_machine_code(code: &[u8]) {
    panic!("Not implemented")
}

fn main() {
    let test_regex = Regex::Concat(vec![
        Regex::Literal("foo".to_string()),
        Regex::Repeat(Box::new(Regex::Choice(vec![
            Regex::Literal("ba".to_string()),
            Regex::Literal("za".to_string()),
        ]))),
    ]);
    println!("{:?}", regex_match(&test_regex, "foobabazazabababar"));
}
