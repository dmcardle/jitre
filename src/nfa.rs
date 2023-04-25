use std::collections::HashMap;
use std::collections::HashSet;

// A Nondeterministic Finite Automaton is defined as (Q, Sigma, Delta, q0, F).
pub struct Nfa<State, Character> {
    transition: HashMap<(State, Character), HashSet<State>>,
    start_state: State,
    accept_states: HashSet<State>,
    state_counter: State,
}

pub struct Dfa<State, Character> {
    transition: HashMap<(State, Character), State>,
    start_state: State,
    accept_states: HashSet<State>,
}

impl Nfa<u64, u8> {
    pub fn new() -> Nfa<u64, u8> {
        Nfa::<u64, u8> {
            transition: HashMap::new(),
            start_state: 0u64,
            accept_states: HashSet::new(),
            state_counter: 2u64,
        }
    }

    pub fn get_start_state(&self) -> u64 {
        self.start_state
    }

    /// Get a state ID that is not already in use.
    pub fn get_fresh_state(&mut self) -> u64 {
        let fresh_state = self.state_counter;
        self.state_counter += 1;
        fresh_state
    }

    pub fn make_accept_state(&mut self, state: u64) {
        self.accept_states.insert(state);
    }

    pub fn add_transition(&mut self, from: u64, on: u8, to: u64) {
        let key = (from, on);
        let to: HashSet<u64> = [to].iter().cloned().collect();

        match self.transition.get_mut(&key) {
            Some(to_states) => {
                to_states.extend(&to);
            }
            None => {
                self.transition.insert((from, on), to);
            }
        }
    }

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
        //  ──>q1─┬──> q2───╮
        //        │     ^   │ 'b'
        //        │     ╰───╯
        //        │'a'
        //        ╰──> q3───╮
        //              ^   │ 'c'
        //              ╰───╯
        //

        let mut nfa = Nfa::<u64, u8>::new();
        let q1 = nfa.get_start_state();
        let q2 = nfa.get_fresh_state();
        let q3 = nfa.get_fresh_state();
        nfa.make_accept_state(q2);
        nfa.make_accept_state(q3);

        nfa.add_transition(q1, b'a', q2);
        nfa.add_transition(q1, b'a', q3);
        nfa.add_transition(q2, b'b', q2);
        nfa.add_transition(q3, b'c', q3);

        // Fails because there's no matching transition from the start state.
        assert_eq!(nfa.simulate("".as_bytes()), None);
        assert_eq!(nfa.simulate("bc".as_bytes()), None);
        assert_eq!(nfa.simulate("xyz".as_bytes()), None);

        // Parses completely.
        assert_eq!(nfa.simulate("abbb".as_bytes()), Some(&[][..]));
        assert_eq!(nfa.simulate("a".as_bytes()), Some(&[][..]));

        // Parses partially.
        assert_eq!(nfa.simulate("abc".as_bytes()), Some(&"abc".as_bytes()[2..]));
        assert_eq!(nfa.simulate("acb".as_bytes()), Some(&"acb".as_bytes()[2..]));
    }
}
