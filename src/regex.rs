use crate::nfa::Nfa;

/// A `Regex` is a classical regular expression.
#[derive(PartialEq, Eq, Debug)]
pub enum Regex {
    Literal(String),
    Concat(Vec<Regex>),
    Choice(Vec<Regex>),
    Repeat(Box<Regex>),
}

impl Regex {
    /// Parses classical regex notation.
    ///
    /// Grammar:
    ///
    /// ```
    /// <regex> ::= <literal>
    ///           | <regex> <regex>        /* concatenation */
    ///           | <regex> '|' <regex>    /* choice */
    ///           | <regex> '*'            /* repetition */
    /// ```
    ///
    /// `<literal>` is defined as a sequence of any ASCII characters.
    ///
    /// TODO: Add support for escape sequences, e.g. so we can parse a literal
    /// asterisk.
    ///
    /// TODO: Read up on UTF-8; probably want to support this instead of ASCII.
    ///
    pub fn parse(expr: &str) -> Option<Regex> {
        let tokens = tokenize(expr);
        let (regex, _leftovers) = parse_regex_tokens(&tokens)?;
        Some(regex)
    }

    /// Converts this Regex to an Nfa using Thompson's construction.
    ///
    /// The states are `u16`, and the alphabet (Σ) is the set of `char` values.
    pub fn to_nfa(&self) -> Nfa<u64, u8> {
        let mut nfa = Nfa::new();
        match self {
            Regex::Literal(s) => {
                let mut prev_state = nfa.start_state();
                for c in s.bytes() {
                    let new_state = nfa.get_fresh_state();
                    nfa.add_transition(prev_state, c, new_state);
                    prev_state = new_state;
                }
                nfa.set_accept(prev_state);
            }
            Regex::Concat(rs) => {
                for r in rs.iter() {
                    nfa.append(r.to_nfa());
                }
            }
            Regex::Choice(rs) => {
                let nfa_choices = rs.iter().map(|r| r.to_nfa());
                for choice in nfa_choices {
                    let (q_choice_start, orig_accept_states) = nfa.join(choice);

                    // The original accept states should still be valid.
                    for q in orig_accept_states {
                        nfa.set_accept(q);
                    }

                    // Each choice's sub-NFA is reachable by an epsilon
                    // transition from the start state.
                    nfa.add_epsilon(nfa.start_state(), q_choice_start);
                }
            }
            Regex::Repeat(r) => {
                // After appending `r`, each of its accept states will have a
                // corresponding accept state in `nfa`.
                nfa.append(r.to_nfa());

                let accept_states: Vec<u64> = nfa.accept_states().copied().collect();
                for q_accept in accept_states {
                    nfa.add_epsilon(q_accept, nfa.start_state());
                }
            }
        }
        nfa
    }

    /// Interprets the regex `r` against the string `line`.
    ///
    /// If it matches, returns a Some value containing the non-matching suffix
    /// of `line`. If the regex matched completely, that suffix will be the
    /// empty string. Otherwise, if the regex does not match `line`, returns
    /// None.
    pub fn interpret<'a>(&self, line: &'a str) -> Option<&'a str> {
        match self {
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
                    line = r.interpret(line)?;
                }
                Some(line)
            }
            Regex::Choice(regexes) => {
                for r in regexes {
                    let result = r.interpret(line);
                    if result.is_some() {
                        return result;
                    }
                }
                None
            }
            Regex::Repeat(r) => {
                let mut line = &line[..];
                loop {
                    let result = r.interpret(line);
                    if result.is_none() {
                        break;
                    }
                    line = result.unwrap();
                }
                Some(line)
            }
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

    for c in expr.chars() {
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
        let first = leftovers.first().unwrap();
        match first {
            RegexToken::Literal(_) => {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_regex_interpret_simple() {
        let test_regex = Regex::Repeat(Box::new(Regex::Literal("foo".to_string())));
        let result = test_regex.interpret("foofoofoo");
        assert_eq!(result, Some(""));
        let result = test_regex.interpret("");
        assert_eq!(result, Some(""));
        let result = test_regex.interpret("barbarbar");
        assert_eq!(result, Some("barbarbar"));
        let result = test_regex.interpret("foofoofoobarbarbar");
        assert_eq!(result, Some("barbarbar"));
    }

    #[test]
    fn test_regex_to_nfa_literal() {
        let test_regex = Regex::Literal("foo".to_string());
        let nfa = test_regex.to_nfa();
        assert_eq!(nfa.simulate("fo".as_bytes()), None);
        assert_eq!(nfa.simulate("foo".as_bytes()), Some(&[][..]));
        assert_eq!(nfa.simulate("foop".as_bytes()), Some("p".as_bytes()));
    }

    #[test]
    fn test_regex_to_nfa_concat() {
        let test_regex = Regex::Concat(vec![Regex::Literal("foo".to_string())]);
        let nfa = test_regex.to_nfa();
        assert_eq!(nfa.simulate("fo".as_bytes()), None);
        assert_eq!(nfa.simulate("foo".as_bytes()), Some(&[][..]));
        assert_eq!(nfa.simulate("foop".as_bytes()), Some("p".as_bytes()));

        let test_regex = Regex::Concat(vec![
            Regex::Literal("foo".to_string()),
            Regex::Literal("bar".to_string()),
        ]);
        let nfa = test_regex.to_nfa();
        assert_eq!(nfa.simulate("fo".as_bytes()), None);
        assert_eq!(nfa.simulate("foo".as_bytes()), None);
        assert_eq!(nfa.simulate("foob".as_bytes()), None);
        assert_eq!(nfa.simulate("foobar".as_bytes()), Some(&[][..]));
        assert_eq!(nfa.simulate("foobarp".as_bytes()), Some("p".as_bytes()));
    }

    #[test]
    fn test_regex_to_nfa_choice() {
        let test_regex = Regex::Choice(vec![Regex::Literal("foo".to_string())]);
        let nfa = test_regex.to_nfa();
        assert_eq!(nfa.simulate("fo".as_bytes()), None);
        assert_eq!(nfa.simulate("foo".as_bytes()), Some(&[][..]));
        assert_eq!(nfa.simulate("foop".as_bytes()), Some("p".as_bytes()));

        let test_regex = Regex::Choice(vec![
            Regex::Literal("foo".to_string()),
            Regex::Literal("bar".to_string()),
        ]);
        let nfa = test_regex.to_nfa();
        assert_eq!(nfa.simulate("fo".as_bytes()), None);
        assert_eq!(nfa.simulate("foo".as_bytes()), Some(&[][..]));
        assert_eq!(nfa.simulate("foob".as_bytes()), Some("b".as_bytes()));
        assert_eq!(nfa.simulate("b".as_bytes()), None);
        assert_eq!(nfa.simulate("bar".as_bytes()), Some(&[][..]));
        assert_eq!(nfa.simulate("barf".as_bytes()), Some("f".as_bytes()));
    }

    #[test]
    fn test_regex_to_nfa_repeat() {
        let test_regex = Regex::Repeat(Box::new(Regex::Literal("foo".to_string())));
        let nfa = test_regex.to_nfa();
        assert_eq!(nfa.simulate("fo".as_bytes()), None);
        assert_eq!(nfa.simulate("foo".as_bytes()), Some(&[][..]));
        assert_eq!(nfa.simulate("foof".as_bytes()), Some("f".as_bytes()));
        assert_eq!(nfa.simulate("foofoo".as_bytes()), Some(&[][..]));
        assert_eq!(nfa.simulate("foofoof".as_bytes()), Some("f".as_bytes()));
    }

    #[test]
    fn test_regex_interpret() {
        let test_regex = Regex::Concat(vec![
            Regex::Literal("foo".to_string()),
            Regex::Repeat(Box::new(Regex::Choice(vec![
                Regex::Literal("ba".to_string()),
                Regex::Literal("za".to_string()),
            ]))),
        ]);

        let tail = test_regex.interpret("foobabazazabababar");
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
        let parsed = Regex::parse("abc");
        assert_eq!(parsed, Some(Regex::Literal("abc".to_string())));
    }

    #[test]
    fn test_regex_parse_parens() {
        let parsed = Regex::parse("(abc)");
        assert_eq!(parsed, Some(Regex::Literal("abc".to_string())));
    }

    #[test]
    fn test_regex_parse_parens_double() {
        let parsed = Regex::parse("(a(b)c)");
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
        let parsed = Regex::parse("a|bc");
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
        let parsed = Regex::parse("a|bc|d");
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
        let parsed = Regex::parse("a*");
        assert_eq!(
            parsed,
            Some(Regex::Repeat(Box::new(Regex::Literal("a".to_string()))))
        );

        let parsed = Regex::parse("a*b*");
        assert_eq!(
            parsed,
            Some(Regex::Concat(vec![
                Regex::Repeat(Box::new(Regex::Literal("a".to_string()))),
                Regex::Repeat(Box::new(Regex::Literal("b".to_string()))),
            ]))
        );
    }

    #[test]
    fn test_regex_parse_parens_star() {
        let parsed = Regex::parse("(abc)*");
        assert_eq!(
            parsed,
            Some(Regex::Repeat(Box::new(Regex::Literal("abc".to_string()))))
        );
    }

    #[test]
    fn test_regex_parse_interpret() {
        // Regex for matching one or more binary digits followed by '@'.
        let pattern = "(0|1)(0|1)*@";

        // Assert that the regex is parseable.
        let regex = Regex::parse(pattern);
        assert!(regex.is_some());
        let regex = regex.unwrap();

        assert_eq!(regex.interpret("1011@ abc"), Some(" abc"));
        assert_eq!(regex.interpret("abc"), None);
        assert_eq!(regex.interpret("abc 1011"), None);
        assert_eq!(regex.interpret("abc 1011@"), None);

        // Test converted NFA.
        let nfa = regex.to_nfa();
        assert_eq!(
            nfa.simulate("1011@ abc".as_bytes()),
            Some(" abc".as_bytes())
        );
        assert_eq!(nfa.simulate("abc".as_bytes()), None);
        assert_eq!(nfa.simulate("abc 1011".as_bytes()), None);
        assert_eq!(nfa.simulate("abc 1011@".as_bytes()), None);
    }
}
