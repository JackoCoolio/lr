use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    marker::PhantomData,
};

use crate::{
    grammar::{production::ExprSymbol, Grammar},
    lang::Language,
    state::State,
};

#[derive(Hash, Clone, Copy, PartialEq, Eq)]
pub struct StateHandle {
    state_index: usize,
}

impl StateHandle {
    pub(crate) fn new(state_index: usize) -> Self {
        Self { state_index }
    }
}

pub struct GotoTable<N, L> {
    table: HashMap<(StateHandle, ExprSymbol<N, L>), StateHandle>,
}

impl<N, L> GotoTable<N, L>
where
    N: Debug + Clone + Hash + Eq,
    L: Debug + Clone + Hash + Eq,
{
    pub(crate) fn build(grammar: &Grammar<N, L>) -> Self
    where
        L: Language,
    {
        let mut table = HashMap::new();

        let states = grammar.get_states();

        println!("states: {:?}", states);

        for (from_index, state) in states.iter().enumerate() {
            for (position, lookahead) in state.items.iter() {
                let Some(locus) = grammar.get_locus(position) else {
                    // no symbol that could advance this
                    continue;
                };

                let advanced_position = position.advanced();

                let advanced_state =
                    State::from_seed(vec![(advanced_position, HashSet::new())], grammar);

                println!("advanced state: {:?}", advanced_state);

                let to_index = states
                    .iter()
                    .enumerate()
                    .find(|state| state.1 == &advanced_state)
                    .unwrap()
                    .0;

                table.insert(
                    (StateHandle::new(from_index), locus.clone()),
                    StateHandle::new(to_index),
                );
            }
        }

        Self { table }
    }
}

#[test]
fn test_build_goto() {
    todo!("speed this up");
    use crate::grammar::get_test_grammar;

    let grammar = get_test_grammar();

    let goto_table = GotoTable::build(&grammar);
}
