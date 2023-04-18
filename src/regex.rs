#[derive(PartialEq, Eq, Debug)]
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

// Splits |expr| into (left, right). The |left| string is guaranteed to contain
// non-control characters. The right string is either empty or begins with a
// control character.
fn regex_split(expr: &str) -> (&str, &str) {
    for (i, c) in expr.char_indices() {
        match c {
            '(' | ')' | '|' | '*' => {
                return expr.split_at(i);
            }
            _ => {}
        }
    }
    (expr, "")
}

#[derive(PartialEq, Eq, Debug)]
enum RegexToken {
    LeftParen,
    RightParen,
    Pipe,
    Star,
    Literal(String),
}

fn tokenize(expr: &str) -> Vec<RegexToken> {
    let mut tokens = Vec::new();
    let mut literal = String::new();

    for (i, c) in expr.char_indices() {
        match c {
            '(' | ')' | '|' | '*' => {
                if !literal.is_empty() {
                    tokens.push(RegexToken::Literal(literal));
                    literal = String::new();
                }
            }
            _ => {}
        };
        match c {
            '(' => tokens.push(RegexToken::LeftParen),
            ')' => tokens.push(RegexToken::RightParen),
            '|' => tokens.push(RegexToken::Pipe),
            '*' => tokens.push(RegexToken::Star),
            _ => literal.push(c),
        };
    }

    if !literal.is_empty() {
        tokens.push(RegexToken::Literal(literal));
    }

    return tokens;
}

fn parse_literal<'a>(tokens: &'a [RegexToken]) -> (Option<Regex>, &'a [RegexToken]) {
    match tokens {
        [RegexToken::Literal(s), tail @ ..] => (Some(Regex::Literal(s.to_string())), tail),
        _ => (None, tokens),
    }
}

fn parse_parens<'a>(tokens: &'a [RegexToken]) -> (Option<Regex>, &'a [RegexToken]) {
    println!("parse_parens( {:?} )", tokens);
    match tokens {
        [RegexToken::LeftParen, tail @ ..] => {
            let mut depth = 1;
            let split: Vec<&[RegexToken]> = tail
                .split_inclusive(|c| {
                    match c {
                        RegexToken::LeftParen => depth += 1,
                        RegexToken::RightParen => depth -= 1,
                        _ => {}
                    };
                    depth > 0
                })
                .collect();

            if split.is_empty() {
                return (None, tokens);
            }
            let n = split.first().unwrap().len();

            let (left, right) = tail.split_at(n);
            println!("left, right = {:?}, {:?}", left, right);
            return (parse_regex_tokens(left), right);
        }
        _ => (None, tokens),
    }
}

fn flatten_regexes(regexes: Vec<Option<Regex>>) -> Option<Regex> {
    let mut regexes: Vec<Regex> = regexes.into_iter().flatten().collect();

    match regexes.len() {
        0 => None,
        1 => Some(regexes.remove(0)),
        _ => Some(Regex::Concat(regexes)),
    }
}

fn parse_regex_tokens(tokens: &[RegexToken]) -> Option<Regex> {
    let mut leftovers: &[RegexToken] = &tokens;
    let mut regexes = Vec::new();
    while leftovers.len() > 0 {
        println!("*** leftovers = {:?}", leftovers);
        let first = leftovers.first().unwrap();
        match first {
            RegexToken::Literal(s) => {
                let (regex, leftovers_) = parse_literal(leftovers);
                regexes.push(regex);
                leftovers = leftovers_;
            }
            RegexToken::LeftParen => {
                let (regex, leftovers_) = parse_parens(leftovers);
                regexes.push(regex);
                leftovers = leftovers_;
            }
            RegexToken::RightParen => {
                println!("On Rightparen, leftovers = {:?}", leftovers);
                leftovers = &leftovers[1..];
            }
            RegexToken::Pipe => panic!("pipe not implemented"),
            RegexToken::Star => panic!("star not implemented"),
        }
    }
    flatten_regexes(regexes)
}

pub fn parse_regex(expr: &str) -> Option<Regex> {
    let tokens = tokenize(expr);
    parse_regex_tokens(&tokens)
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

    #[test]
    fn test_regex_tokenize() {
        let tokens = tokenize("abc*(foo|bar)z");
        assert_eq!(
            tokens,
            vec![
                RegexToken::Literal("abc".to_string()),
                RegexToken::Star,
                RegexToken::LeftParen,
                RegexToken::Literal("foo".to_string()),
                RegexToken::Pipe,
                RegexToken::Literal("bar".to_string()),
                RegexToken::RightParen,
                RegexToken::Literal("z".to_string()),
            ]
        );
    }

    #[test]
    fn test_regex_parse_literal() {
        // Literal
        let parsed = parse_regex("abc");
        assert_eq!(parsed, Some(Regex::Literal("abc".to_string())));
    }

    #[test]
    fn test_regex_parse_parens() {
        // Parens
        let parsed = parse_regex("(abc)");
        assert_eq!(parsed, Some(Regex::Literal("abc".to_string())));
    }

    #[test]
    fn test_regex_parse_parens_double() {
        // Parens
        let parsed = parse_regex("(a(b)c)");
        assert_eq!(
            parsed,
            Some(Regex::Concat(vec![
                Regex::Literal("a".to_string()),
                Regex::Literal("b".to_string()),
                Regex::Literal("c".to_string()),
            ]))
        );
    }

    #[test]
    fn test_regex_parse_pipe() {
        // Parens
        let parsed = parse_regex("a|bc");
        assert_eq!(
            parsed,
            Some(Regex::Choice(vec![
                Regex::Literal("a".to_string()),
                Regex::Literal("bc".to_string())
            ]))
        );
    }

    #[test]
    fn test_regex_parse_star() {
        let parsed = parse_regex("a*");
        assert_eq!(
            parsed,
            Some(Regex::Repeat(Box::new(Regex::Literal("a".to_string()))))
        );

        let parsed = parse_regex("a*b*");
        assert_eq!(
            parsed,
            Some(Regex::Concat(vec![
                Regex::Repeat(Box::new(Regex::Literal("a".to_string()))),
                Regex::Repeat(Box::new(Regex::Literal("b".to_string()))),
            ]))
        );
    }
}
