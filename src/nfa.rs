use std::collections::HashMap;
use std::collections::HashSet;

// A Nondeterministic Finite Automaton is defined as (Q, Sigma, Delta, q0, F).
pub struct Nfa<State, Character> {
    transition: HashMap<(State, Character), HashSet<State>>,
    epsilon_transition: HashMap<State, HashSet<State>>,
    start_state: State,
    accept_states: HashSet<State>,
    state_counter: State,
}

pub struct Dfa<State, Character> {
    transition: HashMap<(State, Character), State>,
    start_state: State,
    accept_states: HashSet<State>,
}

impl<
        State: std::cmp::Eq + std::hash::Hash + std::marker::Copy,
        Character: std::cmp::Eq + std::hash::Hash + std::marker::Copy,
    > Nfa<State, Character>
{
    /// Get this NFA's start state.
    pub fn start_state(&self) -> State {
        self.start_state
    }

    /// Remember `state` as an accept state.
    pub fn set_accept(&mut self, state: State) {
        self.accept_states.insert(state);
    }

    /// Save a non-epsilon transition rule.
    pub fn add_transition(&mut self, from: State, on: Character, to: State) {
        let key = (from, on);
        match self.transition.get_mut(&key) {
            Some(to_states) => {
                to_states.insert(to);
            }
            None => {
                let to_set: HashSet<State> = [to].iter().cloned().collect();
                self.transition.insert((from, on), to_set);
            }
        }
    }

    /// Save an epsilon transition rule.
    pub fn add_epsilon(&mut self, from: State, to: State) {
        match self.epsilon_transition.get_mut(&from) {
            Some(to_states) => {
                to_states.insert(to);
            }
            None => {
                let to_set: HashSet<State> = [to].iter().cloned().collect();
                self.epsilon_transition.insert(from, to_set);
            }
        }
    }

    /// Find all the states reachable via one or more epsilon transitions.
    pub fn epsilon_transitive_closure(&self, from: State) -> HashSet<State> {
        let mut seen = HashSet::new();
        let mut remaining = vec![from];
        while remaining.len() > 0 {
            let state = remaining.pop().unwrap();
            match self.epsilon_transition.get(&state) {
                Some(qs) => {
                    seen.extend(qs);
                    // No need to rexplore `state`.
                    remaining.extend(qs.iter().filter(|&q| *q != state));
                }
                None => {}
            };
        }
        seen
    }

    /// Simulate the NFA, keeping track of all possible states.
    pub fn simulate<'a>(&self, s: &'a [Character]) -> Option<&'a [Character]> {
        println!("ENTER SIMULATE");
        if s.len() == 0 {
            return Some(s);
        }

        let mut best_answer = None;
        let mut state_superposition = HashSet::new();
        state_superposition.insert(self.start_state);
        let epsilon_reachable = self.epsilon_transitive_closure(self.start_state);
        state_superposition.extend(epsilon_reachable);

        let empty = HashSet::new();
        for (i, c) in s.iter().enumerate() {
            state_superposition = state_superposition
                .into_iter()
                .map(|q| {
                    let mut result = HashSet::new();
                    let regular = match self.transition.get(&(q, *c)) {
                        Some(x) => x,
                        None => &empty,
                    };
                    result.extend(regular);
                    for &state in regular {
                        let epsilon_reachable = self.epsilon_transitive_closure(state);
                        result.extend(epsilon_reachable);
                    }
                    result
                })
                .flatten()
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

impl Nfa<u64, u8> {
    pub fn new() -> Nfa<u64, u8> {
        Nfa::<u64, u8> {
            transition: HashMap::new(),
            epsilon_transition: HashMap::new(),
            start_state: 0u64,
            accept_states: HashSet::new(),
            state_counter: 2u64,
        }
    }

    /// Get a state ID that is not already in use.
    pub fn get_fresh_state(&mut self) -> u64 {
        let fresh_state = self.state_counter;
        self.state_counter += 1;
        fresh_state
    }
}

pub fn nfa_to_dfa<State, Character>(nfa: &Nfa<State, Character>) -> Dfa<State, Character> {
    panic!("Not implemented");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simulate_epsilon() {
        let mut nfa = Nfa::<u64, u8>::new();
        let q1 = nfa.start_state();
        let q2 = nfa.get_fresh_state();
        nfa.set_accept(q2);
        assert_eq!(nfa.simulate("".as_bytes()), Some(&[][..]));

        nfa.add_epsilon(q1, q2);
        assert_eq!(nfa.simulate("".as_bytes()), Some(&[][..]));
    }

    #[test]
    fn test_simulate_epsilon_twice() {
        let mut nfa = Nfa::<u64, u8>::new();
        let q1 = nfa.start_state();
        let q2 = nfa.get_fresh_state();
        let q3 = nfa.get_fresh_state();
        nfa.set_accept(q3);

        nfa.add_transition(q1, b'a', q1);
        nfa.add_epsilon(q1, q2);
        nfa.add_epsilon(q2, q3);
        assert_eq!(nfa.simulate("".as_bytes()), Some(&[][..]));
        assert_eq!(nfa.simulate("a".as_bytes()), Some(&[][..]));
        assert_eq!(nfa.simulate("aa".as_bytes()), Some(&[][..]));
        assert_eq!(nfa.simulate("aab".as_bytes()), Some(&"b".as_bytes()[..]));
    }

    #[test]
    fn test_simulate_simple() {
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
        let q1 = nfa.start_state();
        let q2 = nfa.get_fresh_state();
        let q3 = nfa.get_fresh_state();
        nfa.set_accept(q2);
        nfa.set_accept(q3);

        nfa.add_transition(q1, b'a', q2);
        nfa.add_transition(q1, b'a', q3);
        nfa.add_transition(q2, b'b', q2);
        nfa.add_transition(q3, b'c', q3);

        // Fails because there's no matching transition from the start state.
        assert_eq!(nfa.simulate("bc".as_bytes()), None);
        assert_eq!(nfa.simulate("xyz".as_bytes()), None);

        // Parses completely.
        assert_eq!(nfa.simulate("".as_bytes()), Some(&[][..]));
        assert_eq!(nfa.simulate("abbb".as_bytes()), Some(&[][..]));
        assert_eq!(nfa.simulate("a".as_bytes()), Some(&[][..]));

        // Parses partially.
        assert_eq!(nfa.simulate("abc".as_bytes()), Some(&"abc".as_bytes()[2..]));
        assert_eq!(nfa.simulate("acb".as_bytes()), Some(&"acb".as_bytes()[2..]));
    }
}
