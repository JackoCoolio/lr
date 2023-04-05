use std::{collections::HashMap, fmt::Debug, hash::Hash};

use crate::{grammar::production::ExprSymbol, lang::EpsilonSet};

use super::Parser;

pub(super) type FirstTable<N, L> = HashMap<N, EpsilonSet<L>>;

impl<N, L, A> Parser<N, L, A>
where
    N: Debug + Clone + Hash + Eq,
    L: Debug + Clone + Hash + Eq,
{
    /// Computes `FIRST(X_1, X_2, ..., X_n)`.
    /// Note: this is lazy, so it only builds the FIRST table if `sequence` starts with a
    /// nonterminal. Otherwise it doesn't need to.
    pub(crate) fn first_of_string(
        &self,
        sequence: &[ExprSymbol<N, L>],
        lookahead: Option<&L>,
    ) -> EpsilonSet<L>
    where
        L: Debug,
        N: Debug,
    {
        let mut set = EpsilonSet::default();
        let set = match sequence {
            // FIRST of empty string is epsilon
            [] => {
                if let Some(lookahead) = lookahead {
                    set.set_mut().insert(lookahead.clone());
                } else {
                    set.mark_epsilon();
                }
                set
            }
            // FIRST of string that starts with terminal is just the terminal
            [ExprSymbol::Terminal(term), ..] => {
                set.set_mut().insert(term.clone());
                set
            }
            // FIRST of string that starts with a nonterminal is the FIRST of that nonterminal
            // if the FIRST of that nonterminal contains epsilon, add the FIRST of the rest of the
            // string as well
            [ExprSymbol::Nonterminal(nonterm), rest @ ..] => {
                let first = self.get_first().get(nonterm).unwrap();
                set.set_mut().extend(first.as_ref().iter().cloned());
                if !first.has_epsilon() {
                    return set;
                }

                // this looks a little wonky, but we need to preserve the has_epsilon() of
                // first_of_rest
                let mut first_of_rest = self.first_of_string(rest, lookahead);
                first_of_rest.set_mut().extend(set.as_ref().iter().cloned());
                first_of_rest
            }
        };
        set
    }

    /// Returns the FIRST table.
    pub(crate) fn get_first(&self) -> &FirstTable<N, L> {
        self.first.get_or_init(|| self.build_first())
    }

    // simple array indexing might be faster than hashmap
    fn build_first(&self) -> FirstTable<N, L> {
        let mut table: HashMap<N, EpsilonSet<L>> = HashMap::new();

        // initialize sets
        for nonterm in self.grammar.get_nonterminals() {
            table.insert(nonterm, EpsilonSet::default());
        }

        let mut changed = true;

        // repeat until an iteration doesn't change anything
        while changed {
            changed = false;

            for prod in &self.grammar.productions {
                // for tracking whether epsilon appears in all nonterminals in the expression
                let mut include_epsilon = true;

                for expr_symbol in prod.expression.iter() {
                    match expr_symbol {
                        ExprSymbol::Terminal(expr_term) => {
                            // don't include epsilon, because this expression derives a terminal
                            include_epsilon = false;

                            // insert the terminal into FIRST
                            if table
                                .get_mut(&prod.symbol)
                                .unwrap()
                                .set_mut()
                                .insert(expr_term.clone())
                            {
                                // insert returns true if something new was added, so if we got
                                // here, the table was changed
                                changed = true;
                            }

                            // don't traverse farther because this symbol can't derive epsilon
                            break;
                        }
                        ExprSymbol::Nonterminal(expr_nonterm) => {
                            // have to clone to please borrow checker
                            let first = table.get(expr_nonterm).unwrap().clone();

                            let target_set = table.get_mut(&prod.symbol).unwrap().set_mut();

                            // add all symbols
                            for symbol in first.as_ref() {
                                if target_set.insert(symbol.clone()) {
                                    // there was new symbol inserted into this production's FIRST
                                    // entry, so mark that the table was changed
                                    changed = true;
                                }
                            }

                            // if we can't erase this nonterminal, don't traverse farther
                            if !first.has_epsilon() {
                                include_epsilon = false;
                                break;
                            }
                        }
                    }
                }

                // note that this includes the X -> epsilon case since `include_epsilon` is
                // initialized to true
                if include_epsilon && table.get_mut(&prod.symbol).unwrap().mark_epsilon() {
                    changed = true;
                }
            }
        }

        table
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use crate::{
        grammar::{production::Production, Grammar, GrammarBuilder},
        lang::{EpsilonSet, Language, Nonterminal},
        nonterm,
        parser::Parser,
        term,
    };

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    #[allow(non_camel_case_types)]
    pub enum Nonterm {
        Start,
        E,
        Ep,
        T,
        Tp,
        F,
    }

    impl Nonterminal for Nonterm {
        fn start() -> Self {
            Self::Start
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    #[allow(non_camel_case_types)]
    pub enum Term {
        Plus,
        Times,
        LParen,
        RParen,
        Id,
        Eof,
    }

    impl Language for Term {
        fn eof() -> Self {
            Self::Eof
        }
    }

    pub(crate) fn get_test_grammar() -> Grammar<Nonterm, Term, ()> {
        let mut builder = GrammarBuilder::new();
        builder
            .add_start_production(Production::new_passthrough(
                Nonterm::E,
                vec![nonterm!(Nonterm::T), nonterm!(Nonterm::Ep)],
            ))
            .add_nonstart_productions(vec![
                Production::new_passthrough(
                    Nonterm::Ep,
                    vec![
                        term!(Term::Plus),
                        nonterm!(Nonterm::T),
                        nonterm!(Nonterm::Ep),
                    ],
                ),
                Production::new_passthrough(Nonterm::Ep, vec![]),
                Production::new_passthrough(
                    Nonterm::T,
                    vec![nonterm!(Nonterm::F), nonterm!(Nonterm::Tp)],
                ),
                Production::new_passthrough(
                    Nonterm::Tp,
                    vec![
                        term!(Term::Times),
                        nonterm!(Nonterm::F),
                        nonterm!(Nonterm::Tp),
                    ],
                ),
                Production::new_passthrough(Nonterm::Tp, vec![]),
                Production::new_passthrough(
                    Nonterm::F,
                    vec![
                        term!(Term::LParen),
                        nonterm!(Nonterm::E),
                        term!(Term::RParen),
                    ],
                ),
                Production::new_passthrough(Nonterm::F, vec![term!(Term::Id)]),
            ]);

        builder.build().unwrap()
    }

    #[test]
    fn test_grammar_build_first() {
        let grammar = get_test_grammar();

        let parser = Parser::new(grammar);

        // starts uninitialized
        assert!(parser.first.get().is_none());

        let first = parser.get_first();

        // is initialized and cached
        assert!(parser.first.get().is_some());

        // in this case, all FIRSTs are the same
        // bc this grammar is very left-recursive
        assert!(first.get(&Nonterm::F).unwrap().eq(&EpsilonSet::new(
            HashSet::from_iter([Term::LParen, Term::Id]),
            false
        )));

        assert!(first
            .get(&Nonterm::Ep)
            .unwrap()
            .eq(&EpsilonSet::new(HashSet::from_iter([Term::Plus]), true)),);

        assert!(first
            .get(&Nonterm::Tp)
            .unwrap()
            .eq(&EpsilonSet::new(HashSet::from_iter([Term::Times]), true)));
    }
}
