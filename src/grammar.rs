use std::{collections::HashSet, fmt::Debug, hash::Hash};

use thiserror::Error;

use crate::{lang::Nonterminal, nonterm};

use self::production::{ExprSymbol, Production};

pub(crate) mod position;
pub mod production;

pub struct Grammar<N, L, A, Action> {
    pub(crate) productions: Vec<Production<N, L, A, Action>>,
}

pub struct GrammarBuilder<N, L, A, Action> {
    start_productions: Vec<Production<N, L, A, Action>>,
    nonstart_productions: Vec<Production<N, L, A, Action>>,
}

impl<N, L, A, Action> Default for GrammarBuilder<N, L, A, Action> {
    fn default() -> Self {
        Self {
            start_productions: Vec::new(),
            nonstart_productions: Vec::new(),
        }
    }
}

#[derive(Debug, Error)]
pub enum GrammarBuilderError {
    #[error("missing a start nonterminal")]
    MissingStartNonterminal,
    #[error("all start productions must have the same nonterminal")]
    MismatchedStartNonterminals,
    #[error("start nonterminal in nonstart productions")]
    MiscategorizedStartNonterminal,
}

impl<N, L, A, Action> GrammarBuilder<N, L, A, Action> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_start_production(&mut self, production: Production<N, L, A, Action>) -> &mut Self {
        self.start_productions.push(production);
        self
    }

    pub fn add_start_productions<I: IntoIterator<Item = Production<N, L, A, Action>>>(
        &mut self,
        productions: I,
    ) -> &mut Self {
        self.start_productions.extend(productions.into_iter());
        self
    }

    pub fn add_nonstart_production(
        &mut self,
        production: Production<N, L, A, Action>,
    ) -> &mut Self {
        self.nonstart_productions.push(production);
        self
    }

    pub fn add_nonstart_productions<I: IntoIterator<Item = Production<N, L, A, Action>>>(
        &mut self,
        productions: I,
    ) -> &mut Self {
        self.nonstart_productions.extend(productions.into_iter());
        self
    }

    // TODO: join start and nonstart productions and just have an Option<N> field for the start
    // nonterminal

    pub fn build(self) -> Result<Grammar<N, L, A, Action>, GrammarBuilderError>
    where
        N: Clone + Eq + Hash + Nonterminal,
    {
        let mut start_nonterminals = HashSet::new();
        for production in self.start_productions.iter() {
            start_nonterminals.insert(&production.symbol);
        }

        let mut start_nonterminals = start_nonterminals.into_iter();

        // if there aren't any start nonterminals, error
        let Some(start_nonterminal) = start_nonterminals.next() else {
            return Err(GrammarBuilderError::MissingStartNonterminal);
        };

        // if there's more than one start nonterminal, error
        if start_nonterminals.next().is_some() {
            return Err(GrammarBuilderError::MismatchedStartNonterminals);
        }

        let augment = Production::<N, L, A, Action>::new(
            N::start(),
            vec![nonterm!(start_nonterminal.clone())],
            |nodes| nodes.first().unwrap(),
        );

        for production in self.nonstart_productions.iter() {
            if &production.symbol == start_nonterminal {
                return Err(GrammarBuilderError::MiscategorizedStartNonterminal);
            }
        }

        // TODO: maybe restructure. Nonterminal trait isn't very Rusty
        //       Bring back Nonterminal struct with immutable `start` field?

        Ok(Grammar {
            productions: std::iter::once(augment)
                .chain(self.start_productions.into_iter())
                .chain(self.nonstart_productions.into_iter())
                .collect(),
        })
    }
}

#[test]
fn test_grammar_builder() {
    impl Nonterminal for () {
        fn start() -> Self {}
    }

    let builder: GrammarBuilder<(), ()> = GrammarBuilder::default();
    assert!(
        matches!(
            builder.build(),
            Err(GrammarBuilderError::MissingStartNonterminal)
        ),
        "empty grammar builder should not build"
    );

    // TODO: add test cases for other errors
}

impl<N, L> Grammar<N, L> {
    pub(crate) fn get_production(&self, i: usize) -> Option<&Production<N, L>> {
        self.productions.get(i)
    }
}

impl<N, L> Grammar<N, L>
where
    N: Debug + Clone + Hash + Eq,
    L: Debug + Clone + Hash + Eq,
{
    /// Returns a set of all the grammar symbols in the grammar.
    pub(crate) fn get_symbols(&self) -> HashSet<ExprSymbol<N, L>> {
        let mut symbols = HashSet::new();

        for production in self.productions.iter() {
            symbols.insert(ExprSymbol::Nonterminal(production.symbol.clone()));
            for symbol in production.expression.iter() {
                symbols.insert(symbol.clone());
            }
        }

        symbols
    }

    /// Returns all of the nonterminals in the Grammar.
    /// The first nonterminal is the start nonterminal.
    pub(crate) fn get_nonterminals(&self) -> Vec<N> {
        let mut nonterms = Vec::new();
        for prod in self.productions.iter() {
            if nonterms.contains(&prod.symbol) {
                continue;
            }

            nonterms.push(prod.symbol.clone());
        }
        nonterms
    }
}
