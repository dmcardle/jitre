use std::collections::HashMap;
use std::collections::HashSet;

// A Nondeterministic Finite Automaton is defined as (Q, Sigma, Delta, q0, F).
pub struct Nfa<State, Character> {
    states: Vec<State>,
    transition: HashMap<(State, Character), HashSet<State>>,
    start_state: State,
    accept_states: HashSet<State>,
}

pub struct Dfa<State, Character> {
    states: Vec<State>,
    transition: HashMap<(State, Character), State>,
    start_state: State,
    accept_states: HashSet<State>,
}

pub fn nfa_to_dfa<State, Character>(nfa: &Nfa<State, Character>) -> Dfa<State, Character> {
    panic!("Not implemented");
}
