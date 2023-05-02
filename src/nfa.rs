use std::collections::HashMap;
use std::collections::HashSet;

/// A Nondeterministic Finite Automaton (NFA) is defined as the tuple (Q, Sigma,
/// Delta, q0, F). The difference from a Deterministic Finite Automaton (DFA) is
/// the transition function. For NFAs, the transition function Delta has type (Q
/// x Sigma) -> 2^Sigma, whereas for DFAs the transition function delta has type
/// (Q x Sigma) -> Sigma.
pub struct Automaton<State, Character, TransitionRange> {
    transition: HashMap<(State, Character), TransitionRange>,
    epsilon_transition: HashMap<State, TransitionRange>,
    start_state: State,
    accept_states: HashSet<State>,
    state_counter: State,
}

pub type Nfa<State, Character> = Automaton<State, Character, HashSet<State>>;
pub type Dfa<State, Character> = Automaton<State, Character, State>;

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

    pub fn accept_states(&self) -> impl Iterator<Item = &State> {
        self.accept_states.iter()
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
            state_counter: 1u64,
        }
    }

    /// Get a state ID that is not already in use.
    pub fn get_fresh_state(&mut self) -> u64 {
        let fresh_state = self.state_counter;
        self.state_counter += 1;
        fresh_state
    }

    fn get_corresponding_state(&mut self, map: &mut HashMap<u64, u64>, qOther: u64) -> u64 {
        match map.get(&qOther) {
            Some(q) => *q,
            None => {
                let qFresh = self.get_fresh_state();
                map.insert(qOther, qFresh);
                qFresh
            }
        }
    }

    /// Tack the `other` NFA on the end of this one.
    pub fn append(&mut self, other: Nfa<u64, u8>) {
        let (q_other_start, orig_accept_states) = self.join(other);

        // Attach each of this NFA's accept states to the other NFA's start state.
        for &q_accept in orig_accept_states.iter() {
            self.add_epsilon(q_accept, q_other_start);
        }

        // Edge case: if this NFA originally had no accept states, wire its
        // start state directly to the other NFA's start state.
        if orig_accept_states.len() == 0 {
            self.add_epsilon(self.start_state(), q_other_start);
        }
    }

    /// Absorbs `other` into this NFA.
    ///
    /// Replaces this NFA's accept states with those of `other`.
    ///
    /// Returns a tuple. The first element is the new start state corresponding
    /// to `other`'s start state. The second element is the original set of
    /// accept states.
    pub fn join(&mut self, other: Nfa<u64, u8>) -> (u64, HashSet<u64>) {
        // For each state in `other`, allocate a corresponding fresh state.
        let mut state_map: HashMap<u64, u64> = HashMap::new();

        for ((from, on), to_states) in other.transition.iter() {
            let from = self.get_corresponding_state(&mut state_map, *from);

            for to in to_states.iter() {
                let to = self.get_corresponding_state(&mut state_map, *to);
                self.add_transition(from, *on, to);
            }
        }

        for (from, to_states) in other.epsilon_transition.iter() {
            let from = self.get_corresponding_state(&mut state_map, *from);
            for to in to_states.iter() {
                let to = self.get_corresponding_state(&mut state_map, *to);
                self.add_epsilon(from, to);
            }
        }

        // Connect each accept state of `self` to the start state of `other`.

        let accept_states = self.accept_states.clone();
        self.accept_states.clear();

        // Add each accept state in `other` to this NFA.
        for other_accept_state in other.accept_states.iter() {
            let q_other = self.get_corresponding_state(&mut state_map, *other_accept_state);
            self.accept_states.insert(q_other);
        }

        let q_other_start = self.get_corresponding_state(&mut state_map, other.start_state);
        (q_other_start, accept_states)
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

    #[test]
    fn test_append() {
        // Accepts /a(aa)*/, i.e. an odd number of 'a' characters.
        let mut nfa_a = Nfa::<u64, u8>::new();
        let q1 = nfa_a.start_state();
        let q2 = nfa_a.get_fresh_state();
        let q3 = nfa_a.get_fresh_state();
        nfa_a.set_accept(q3);
        nfa_a.add_epsilon(q1, q2);
        nfa_a.add_transition(q2, b'a', q3);
        nfa_a.add_transition(q3, b'a', q2);

        // Accepts /b*/.
        let mut nfa_b = Nfa::<u64, u8>::new();
        let q1 = nfa_b.start_state();
        nfa_b.set_accept(q1);
        nfa_b.add_transition(q1, b'b', q1);

        // Sanity check on `nfa_b`.
        assert_eq!(nfa_b.simulate("bb".as_bytes()), Some(&[][..]));

        // Append `nfa_b` to the end of `nfa_b`. Now, `nfa_a` accepts /a(aa)*b*/.
        nfa_a.append(nfa_b);

        assert_eq!(nfa_a.simulate("bb".as_bytes()), None);
        assert_eq!(nfa_a.simulate("bba".as_bytes()), None);

        // Parses completely.
        assert_eq!(nfa_a.simulate("".as_bytes()), Some(&[][..]));
        assert_eq!(nfa_a.simulate("a".as_bytes()), Some(&[][..]));
        assert_eq!(nfa_a.simulate("aaaaa".as_bytes()), Some(&[][..]));
        assert_eq!(nfa_a.simulate("ab".as_bytes()), Some(&[][..]));
        assert_eq!(nfa_a.simulate("abbb".as_bytes()), Some(&[][..]));
    }
}
