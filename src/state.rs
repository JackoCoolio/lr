use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt::{Debug, Display, Formatter},
    hash::Hash,
};

use crate::{
    grammar::{position::Position, production::ExprSymbol, Grammar},
    lang::Language,
    nonterm, term,
};

#[derive(Debug)]
pub struct State<L> {
    pub(crate) items: BTreeMap<Position, HashSet<L>>,
}

impl<L> Hash for State<L> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let mut positions: Vec<_> = self.items.keys().collect();

        // hasher doesn't make guarantees about ordering, so we need to ensure that equivalent
        // States call hash() in the same order
        positions.sort();
        for pos in positions {
            pos.hash(state);
        }
    }
}

impl<L> PartialEq for State<L>
where
    L: Hash + Eq,
{
    fn eq(&self, other: &Self) -> bool {
        for (x, y) in std::iter::zip(self.items.iter(), other.items.iter()) {
            if x != y {
                return false;
            }
        }
        true
    }
}

impl<L> Eq for State<L> where L: Hash + Eq {}

impl<L> State<L>
where
    L: Debug + Clone + Eq + Hash + Language,
{
    /// Creates a State from a seed and computes its closure using the given Grammar.
    pub(crate) fn from_seed<N>(seed: Vec<(Position, HashSet<L>)>, grammar: &Grammar<N, L>) -> Self
    where
        N: Debug + Clone + Hash + Eq,
    {
        todo!()
        /*
                let mut items = BTreeMap::from_iter(seed.into_iter());

                let first = grammar.get_first();
                let follow = grammar.get_follow();

                loop {
                    let mut new_items = items.clone();

                    for (pos, lookaheads) in items.iter() {
                        let locus = grammar.get_locus(pos);

                        let Some(ExprSymbol::Nonterminal(locus)) = locus else {
                            // ignore empty and terminal loci
                            continue;
                        };

                        let next = grammar.get_next(pos);

                        let starting_positions = grammar.get_starting_positions(locus);

                        let lookahead: Vec<L> = match next {
                            Some(ExprSymbol::Terminal(term)) => {
                                // first of next is just a terminal
                                vec![term.clone()]
                            }
                            Some(ExprSymbol::Nonterminal(nonterm)) => {
                                // first of next is first of nonterminal
                                todo!("fix from_seed");
                                /*
                                let x: Vec<L> = first.get(nonterm).into_iter().flatten().cloned().collect();
                                x
                                */
                            }
                            None => lookaheads.iter().cloned().collect(),
                        };

                        for pos in starting_positions {
                            let existing_lookaheads = new_items.entry(pos).or_insert(HashSet::new());
                            let mut set: HashSet<L> = existing_lookaheads.iter().cloned().collect();
                            for la in lookahead.iter() {
                                set.insert(la.clone());
                            }
                            *existing_lookaheads = set.into_iter().collect();
                        }
                    }

                    if new_items == items {
                        return State { items: new_items };
                    }

                    items = new_items;
                }

                Self { items }
        */
    }
}

#[cfg(test)]
impl<L> State<L> {
    pub(crate) fn with_grammar<'a, N>(
        &'a self,
        grammar: &'a Grammar<N, L>,
    ) -> StateWithGrammar<'a, N, L> {
        StateWithGrammar {
            state: self,
            grammar,
        }
    }
}

#[cfg(test)]
pub(crate) struct StateWithGrammar<'a, N, L> {
    state: &'a State<L>,
    grammar: &'a Grammar<N, L>,
}

#[cfg(test)]
impl<N, L> Display for StateWithGrammar<'_, N, L>
where
    N: Display,
    L: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{ ")?;
        for (i, (position, lookaheads)) in self.state.items.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }

            write!(f, "{} {{", position.with_grammar(self.grammar))?;

            for (j, lookahead) in lookaheads.iter().enumerate() {
                if j != 0 {
                    write!(f, ", ");
                }

                write!(f, "{}", lookahead);
            }

            writeln!(f, "}}")?;
        }
        write!(f, "}}")
    }
}

macro_rules! set {
    () => {
        HashSet::new()
    };
    ($($x:expr),+ $(,)?) => {
        HashSet::from_iter(vec![$($x),+].into_iter())
    }
}

#[cfg(test)]
#[test]
fn test_build_closure() {
    todo!("speed this up");
    use crate::{
        grammar::{production::Production, GrammarBuilder},
        lang::Nonterminal,
    };

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    enum Nonterm {
        Start,
        S,
        A,
        B,
    }

    impl Nonterminal for Nonterm {
        fn start() -> Self {
            Self::Start
        }
    }

    #[allow(non_camel_case_types)]
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    enum Term {
        a,
        b,
        c,
        d,
        x,
        Eof,
    }

    impl Language for Term {
        fn eof() -> Self {
            Self::Eof
        }
    }

    let mut builder = GrammarBuilder::new();
    builder
        .add_start_productions(vec![
            Production::new(
                Nonterm::S,
                vec![
                    ExprSymbol::Terminal(Term::a),
                    ExprSymbol::Nonterminal(Nonterm::A),
                    ExprSymbol::Terminal(Term::b),
                ],
            ),
            Production::new(
                Nonterm::S,
                vec![
                    ExprSymbol::Terminal(Term::a),
                    ExprSymbol::Nonterminal(Nonterm::B),
                    ExprSymbol::Terminal(Term::d),
                ],
            ),
            Production::new(
                Nonterm::S,
                vec![
                    ExprSymbol::Terminal(Term::c),
                    ExprSymbol::Nonterminal(Nonterm::A),
                    ExprSymbol::Terminal(Term::d),
                ],
            ),
            Production::new(
                Nonterm::S,
                vec![
                    ExprSymbol::Terminal(Term::c),
                    ExprSymbol::Nonterminal(Nonterm::B),
                    ExprSymbol::Terminal(Term::d),
                ],
            ),
        ])
        .add_nonstart_productions(vec![
            Production::new(Nonterm::A, vec![ExprSymbol::Terminal(Term::x)]),
            Production::new(Nonterm::B, vec![ExprSymbol::Terminal(Term::x)]),
        ]);

    let grammar = builder.build().unwrap();

    let state = State::from_seed(vec![(Position::new(0, 0, true), set![])], &grammar);

    println!("{}", state.with_grammar(&grammar));

    panic!();
}

#[test]
fn test_build_closure2() {
    use crate::{
        grammar::{production::Production, GrammarBuilder},
        lang::Nonterminal,
    };

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    enum Nonterm {
        Start,
        S,
        C,
    }

    impl Nonterminal for Nonterm {
        fn start() -> Self {
            Self::Start
        }
    }

    #[allow(non_camel_case_types)]
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    enum Term {
        c,
        d,
        Eof,
    }

    impl Language for Term {
        fn eof() -> Self {
            Self::Eof
        }
    }

    let mut builder = GrammarBuilder::new();
    builder.add_start_production(Production::new(
        Nonterm::S,
        vec![nonterm!(Nonterm::C), nonterm!(Nonterm::C)],
    ));
    builder.add_nonstart_productions(vec![
        Production::new(Nonterm::C, vec![term!(Term::c), nonterm!(Nonterm::C)]),
        Production::new(Nonterm::C, vec![term!(Term::d)]),
    ]);
    let grammar = builder.build().unwrap();

    let expected_states = vec![
        // 0
        State {
            items: BTreeMap::from_iter(vec![
                (Position::new(0, 0, true), set![Term::eof()]),
                (Position::new(1, 0, false), set![Term::eof()]),
                (Position::new(2, 0, false), set![Term::c, Term::d]),
                (Position::new(3, 0, false), set![Term::c, Term::d]),
            ]),
        },
        // 1
        State {
            items: BTreeMap::from_iter(vec![(Position::new(0, 1, true), set![Term::eof()])]),
        },
        // 2
        State {
            items: BTreeMap::from_iter(vec![
                (Position::new(1, 1, false), set![Term::eof()]),
                (Position::new(2, 0, false), set![Term::eof()]),
                (Position::new(3, 0, false), set![Term::eof()]),
            ]),
        },
        // 3
        State {
            items: BTreeMap::from_iter(vec![
                (Position::new(2, 1, false), set![Term::c, Term::d]),
                (Position::new(2, 0, false), set![Term::c, Term::d]),
                (Position::new(3, 0, false), set![Term::c, Term::d]),
            ]),
        },
    ];

    // 0
    let state = State::from_seed(
        vec![(Position::new(0, 0, true), set![Term::eof()])],
        &grammar,
    );
    assert_eq!(state, expected_states[0]);

    // 1
    let state = State::from_seed(
        vec![(Position::new(0, 1, true), set![Term::eof()])],
        &grammar,
    );
    assert_eq!(state, expected_states[1]);

    // 2
    let state = State::from_seed(
        vec![(Position::new(1, 1, false), set![Term::eof()])],
        &grammar,
    );
    assert_eq!(state, expected_states[2]);

    // 3
    let state = State::from_seed(
        vec![(Position::new(2, 1, false), set![Term::c, Term::d])],
        &grammar,
    );
    assert_eq!(
        state,
        expected_states[3],
        "\n\n{}\n\n!=\n\n{}",
        state.with_grammar(&grammar),
        expected_states[3].with_grammar(&grammar)
    );
}
