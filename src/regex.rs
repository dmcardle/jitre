#[derive(PartialEq, Eq, Debug)]
pub enum Regex {
    Literal(String),
    Concat(Vec<Regex>),
    Choice(Vec<Regex>),
    Repeat(Box<Regex>),
}

// Interprets the regex |r| against |line|. If it matches, returns a Some value
// containing the non-matching suffix of |line|. If the regex matched
// completely, that suffix will be the empty string. Otherwise, if the regex
// does not match |line|, returns None.
pub fn regex_match<'a>(r: &'a Regex, line: &'a str) -> Option<&'a str> {
    match r {
        Regex::Literal(s) => {
            if line.len() < s.len() {
                return None;
            }
            let matches = line.chars().zip(s.chars()).all(|(c1, c2)| c1 == c2);
            if matches {
                Some(&line[s.len()..])
            } else {
                None
            }
        }
        Regex::Concat(regexes) => {
            let mut line = &line[..];
            for r in regexes {
                line = regex_match(r, line)?;
            }
            Some(line)
        }
        Regex::Choice(regexes) => {
            for r in regexes {
                let result = regex_match(r, line);
                if result.is_some() {
                    return result;
                }
            }
            None
        }
        Regex::Repeat(r) => {
            let mut line = &line[..];
            loop {
                let result = regex_match(r, line);
                if result.is_none() {
                    break;
                }
                line = result.unwrap();
            }
            Some(line)
        }
    }
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

fn parse_literal<'a>(tokens: &'a [RegexToken]) -> Option<(Regex, &'a [RegexToken])> {
    match tokens {
        [RegexToken::Literal(s), tail @ ..] => Some((Regex::Literal(s.to_string()), tail)),
        _ => None,
    }
}

fn parse_parens<'a>(tokens: &'a [RegexToken]) -> Option<(Regex, &'a [RegexToken])> {
    // Check that tokens begins with a left paren.
    match tokens.first()? {
        RegexToken::LeftParen => {}
        _ => return None,
    }
    // Consume the left paren.
    let tokens = &tokens[1..];

    // Parse the inner regex.
    let (regex, leftovers) = parse_regex_tokens(tokens)?;

    // Check that the next token is a right paren.
    match leftovers.first()? {
        RegexToken::RightParen => {}
        _ => return None,
    }

    return Some((regex, &leftovers[1..]));
}

fn parse_regex_tokens<'a>(tokens: &'a [RegexToken]) -> Option<(Regex, &'a [RegexToken])> {
    let mut leftovers: &[RegexToken] = &tokens;
    let mut regexes = Vec::new();
    while leftovers.len() > 0 {
        println!("*** leftovers = {:?}", leftovers);
        let first = leftovers.first().unwrap();
        match first {
            RegexToken::Literal(s) => {
                let (regex, leftovers_) = parse_literal(leftovers)?;
                regexes.push(regex);
                leftovers = leftovers_;
            }
            RegexToken::LeftParen => {
                let (regex, leftovers_) = parse_parens(leftovers)?;
                regexes.push(regex);
                leftovers = leftovers_;
            }
            RegexToken::RightParen => {
                break;
            }
            RegexToken::Pipe => {
                // Consume the pipe.
                leftovers = &leftovers[1..];

                // Parse the next expression
                let (regex, leftovers_) = parse_regex_tokens(leftovers)?;
                leftovers = leftovers_;

                // Wrap previous regex and |regex| in a Regex::Choice.
                let operand = regexes.pop()?;

                regexes.push(Regex::Choice(vec![operand, regex]));
            }

            RegexToken::Star => {
                // Consume the star.
                leftovers = &leftovers[1..];
                // Wrap the last regex in a Regex::Repeat.
                let operand = regexes.pop()?;
                regexes.push(Regex::Repeat(Box::new(operand)));
            }
        }
    }

    match regexes.len() {
        0 => None,
        1 => Some((regexes.pop()?, leftovers)),
        _ => Some((Regex::Concat(regexes), leftovers)),
    }
}

pub fn parse_regex(expr: &str) -> Option<Regex> {
    let tokens = tokenize(expr);
    let (regex, leftovers) = parse_regex_tokens(&tokens)?;
    Some(regex)
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

        let tail = regex_match(&test_regex, "foobabazazabababar");

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
        let parsed = parse_regex("abc");
        assert_eq!(parsed, Some(Regex::Literal("abc".to_string())));
    }

    #[test]
    fn test_regex_parse_parens() {
        let parsed = parse_regex("(abc)");
        assert_eq!(parsed, Some(Regex::Literal("abc".to_string())));
    }

    #[test]
    fn test_regex_parse_parens_double() {
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
    fn test_regex_parse_pipe_2() {
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
    fn test_regex_parse_pipe_3() {
        let parsed = parse_regex("a|bc|d");
        assert_eq!(
            parsed,
            Some(Regex::Choice(vec![
                Regex::Literal("a".to_string()),
                Regex::Choice(vec![
                    Regex::Literal("bc".to_string()),
                    Regex::Literal("d".to_string())
                ])
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
        let parsed = parse_regex("a*b*");
    }

    #[test]
    fn test_regex_parse_parens_star() {
        let parsed = parse_regex("(abc)*");
        assert_eq!(
            parsed,
            Some(Regex::Repeat(Box::new(Regex::Literal("abc".to_string()))))
        );
    }

    #[test]
    fn test_end_to_end() {
        // Regex for matching one or more binary digits followed by '@'.
        let pattern = "(0|1)(0|1)*@";

        // Assert that the regex is parseable.
        let regex = parse_regex(pattern);
        assert!(regex.is_some());
        let regex = regex.unwrap();

        assert_eq!(regex_match(&regex, "1011@ abc"), Some(" abc"));
        assert_eq!(regex_match(&regex, "abc"), None);
        assert_eq!(regex_match(&regex, "abc 1011"), None);
        assert_eq!(regex_match(&regex, "abc 1011@"), None);
    }
}
