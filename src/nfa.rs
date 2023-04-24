use std::collections::HashMap;
use std::collections::HashSet;

// A Nondeterministic Finite Automaton is defined as (Q, Sigma, Delta, q0, F).
pub struct Nfa<State, Character> {
    transition: HashMap<(State, Character), HashSet<State>>,
    start_state: State,
    accept_states: HashSet<State>,
}

pub struct Dfa<State, Character> {
    transition: HashMap<(State, Character), State>,
    start_state: State,
    accept_states: HashSet<State>,
}

impl<State: std::cmp::Eq + std::hash::Hash + std::marker::Copy + std::clone::Clone> Nfa<State, u8> {
    /// Simulate the NFA, keeping track of all possible states.
    pub fn simulate<'a>(&self, s: &'a [u8]) -> Option<&'a [u8]> {
        let mut best_answer = None;
        let mut state_superposition = HashSet::new();
        state_superposition.insert(self.start_state);

        for (i, c) in s.iter().enumerate() {
            state_superposition = state_superposition
                .into_iter()
                .map(|q| self.transition.get(&(q, *c)))
                .filter(|q_set| q_set.is_some())
                .map(|q_set: Option<_>| q_set.unwrap())
                .filter(|q_set| q_set.len() > 0)
                .flatten()
                .cloned()
                .collect();

            // There's no possibilities for parsing up to position |i|.
            if state_superposition.len() == 0 {
                break;
            }

            // If we're in any of the accept states, this might be the best
            // answer we're going to get.
            if !state_superposition.is_disjoint(&self.accept_states) {
                best_answer = Some(&s[i + 1..]);
            }
        }

        best_answer
    }
}

pub fn nfa_to_dfa<State, Character>(nfa: &Nfa<State, Character>) -> Dfa<State, Character> {
    panic!("Not implemented");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple() {
        // Build an NFA that parses the regex /a(b*|c*)/.
        //
        // Graphically, with accept states q2 and q3:
        //
        //       'a'
        //     q1─┬──> q2───╮
        //        │     ^   │ 'b'
        //        │     ╰───╯
        //        │'a'
        //        ╰──> q3───╮
        //              ^   │ 'c'
        //              ╰───╯
        //
        let mut transition: HashMap<(u8, u8), HashSet<u8>> = HashMap::new();
        transition.insert((1, b'a'), [2, 3].iter().cloned().collect());
        transition.insert((2, b'b'), [2].iter().cloned().collect());
        transition.insert((3, b'c'), [3].iter().cloned().collect());

        let test_nfa = Nfa::<u8, u8> {
            transition: transition,
            start_state: 1,
            accept_states: [2, 3].iter().cloned().collect(),
        };

        // Fails because there's no matching transition from the start state.
        assert_eq!(test_nfa.simulate("".as_bytes()), None);
        assert_eq!(test_nfa.simulate("bc".as_bytes()), None);
        assert_eq!(test_nfa.simulate("xyz".as_bytes()), None);

        // Parses completely.
        assert_eq!(test_nfa.simulate("abbb".as_bytes()), Some(&[][..]));
        assert_eq!(test_nfa.simulate("a".as_bytes()), Some(&[][..]));

        // Parses partially.
        assert_eq!(
            test_nfa.simulate("abc".as_bytes()),
            Some(&"abc".as_bytes()[2..])
        );
        assert_eq!(
            test_nfa.simulate("acb".as_bytes()),
            Some(&"acb".as_bytes()[2..])
        );
    }
}
