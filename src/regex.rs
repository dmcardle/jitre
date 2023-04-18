pub enum Regex {
    Literal(String),
    Concat(Vec<Regex>),
    Choice(Vec<Regex>),
    Repeat(Box<Regex>),
}

// Interprets the regex |r| against |line|. If it matches, the first return
// value is true, and the second is the non-matching suffix of |line|.
// Otherwise, the return value is (false, None).
pub fn regex_match<'a>(r: &'a Regex, line: &'a str) -> (bool, Option<&'a str>) {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_regex_match() {
        let test_regex = Regex::Concat(vec![
            Regex::Literal("foo".to_string()),
            Regex::Repeat(Box::new(Regex::Choice(vec![
                Regex::Literal("ba".to_string()),
                Regex::Literal("za".to_string()),
            ]))),
        ]);

        let (is_match, tail) = regex_match(&test_regex, "foobabazazabababar");

        assert!(is_match);
        assert_eq!(tail, Some("r"));
    }
}
