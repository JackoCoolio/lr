use std::{
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
};

use once_cell::unsync::OnceCell;
use thiserror::Error;

use crate::{
    grammar::{
        position::Position,
        production::{ExprSymbol, Production},
        Grammar,
    },
    lang::Language,
};

use self::{action::Action, first::FirstTable};

pub mod action;
pub mod first;

type ActionTable<L> = HashMap<(usize, L), Action>;
type GotoTable<N> = HashMap<(usize, N), usize>;

pub struct Parser<N, L, A> {
    grammar: Grammar<N, L, A>,
    first: OnceCell<FirstTable<N, L>>,
    states: OnceCell<Vec<ItemSet<L>>>,
    tables: OnceCell<(ActionTable<L>, GotoTable<N>)>,
}

impl<N, L, A> Parser<N, L, A> {
    pub fn new(grammar: Grammar<N, L, A>) -> Self {
        Parser {
            grammar,
            first: OnceCell::new(),
            states: OnceCell::new(),
            tables: OnceCell::new(),
        }
    }
}

impl<N, L, A> Parser<N, L, A>
where
    N: Debug + Clone + Hash + Eq,
    L: Debug + Clone + Hash + Eq,
{
    fn closure_of(&self, mut item_set: ItemSet<L>) -> ItemSet<L> {
        // print!("closure_of({}) = ", item_set.with_grammar(&self.grammar));
        self.close_on(&mut item_set);
        // println!("{}", item_set.with_grammar(&self.grammar));
        item_set
    }

    /// Computes the closure of the given item set, mutating it in place.
    fn close_on(&self, item_set: &mut ItemSet<L>) {
        let mut changed = true;

        while changed {
            changed = false;

            // use a separate list of items that we add to item_set later
            // because we immutably borrow item_set for the for loop
            let mut to_add = Vec::new();

            for Item(position, lookahead) in item_set.items() {
                let production = self.grammar.get_production(position.production()).unwrap();

                let locus = production.expression.get(position.expression());

                let Some(ExprSymbol::Nonterminal(nonterm)) = locus else {
                    // skip terminals and end positions
                    continue;
                };

                // not sure if this will panic
                let rest = &production.expression[position.expression() + 1..];

                let first = self.first_of_string(rest, Some(lookahead));

                for (prod_index, _) in self
                    .grammar
                    .productions
                    .iter()
                    .enumerate()
                    .filter(|(_, prod)| &prod.symbol == nonterm)
                {
                    for term in first.set() {
                        to_add.push(Item(Position::new(prod_index, 0), term.clone()));
                    }
                }
            }

            for item in to_add {
                if item_set.as_mut().insert(item) {
                    // mark that we changed the item set
                    changed = true;
                }
            }
        }
    }

    // Computes GOTO(I, X) for the given item set and grammar symbol.
    fn goto(&self, item_set: &ItemSet<L>, symbol: &ExprSymbol<N, L>) -> ItemSet<L> {
        // println!("goto({:#?}, {:?})", item_set, symbol);
        let mut goto = ItemSet::new();

        for item in item_set.items() {
            let Some(locus) = self.grammar.get_locus(item.position()) else {
                continue;
            };

            // if the locus isn't correct, next item
            if locus != symbol {
                continue;
            }

            // we know that this is a valid advance because of the above match check
            goto.as_mut().insert(item.advanced());
        }

        self.closure_of(goto)
    }

    pub(crate) fn get_states(&self) -> &Vec<ItemSet<L>>
    where
        L: Language,
    {
        self.states.get_or_init(|| self.build_states())
    }

    fn build_states(&self) -> Vec<ItemSet<L>>
    where
        L: Language,
    {
        assert!(
            self.states.get().is_none(),
            "use get_states() instead. we've already computed the states for this parser"
        );

        let mut states = Vec::new();

        let initial_state = {
            let mut initial_state = ItemSet::new();
            initial_state
                .as_mut()
                .insert(Item(Position::new(0, 0), L::eof()));
            self.closure_of(initial_state)
        };

        // initialize C to CLOSURE({[S' -> . S, $]})
        states.push(initial_state);

        let symbols = self.grammar.get_symbols();

        let mut changed = true;

        while changed {
            let mut to_add = Vec::new();

            // for each set of items I in C
            for item_set in states.iter() {
                // for each grammar symbol X
                for symbol in symbols.iter() {
                    let goto = self.goto(item_set, symbol);

                    // if GOTO(I, X) is not empty
                    if goto.is_empty() {
                        continue;
                    }

                    // and not in C
                    if states.contains(&goto) {
                        continue;
                    }

                    // add GOTO(I, X) to C
                    to_add.push(goto);
                }
            }

            // we know that to_add cannot contain states that are already in `states`
            changed = !to_add.is_empty();

            for item_set in to_add {
                states.push(item_set);
            }
        }

        states
    }

    fn get_tables(&self) -> Result<&(ActionTable<L>, GotoTable<N>), ParserConstructionError>
    where
        L: Language,
    {
        self.tables.get_or_try_init(|| self.build_tables())
    }

    fn build_tables(&self) -> Result<(ActionTable<L>, GotoTable<N>), ParserConstructionError>
    where
        L: Language,
    {
        assert!(
            self.tables.get().is_none(),
            "use get_tables(), the tables for this parser have already been computed"
        );

        let mut action: ActionTable<L> = HashMap::new();
        let mut goto: GotoTable<N> = HashMap::new();

        let states = self.get_states();
        for (i, state) in states.iter().enumerate() {
            for Item(position, lookahead) in state.items() {
                let locus = self.grammar.get_locus(position);
                match locus {
                    Some(symbol @ ExprSymbol::Terminal(term)) => {
                        // (a)
                        // we shouldn't have to build goto every time. cache somehow?
                        let goto_state = self.goto(state, symbol);

                        let Some(j) = states.iter().position(|state| state == &goto_state) else {
                            continue;
                        };

                        // set ACTION[i, a] to "shift j"
                        if let Some(other) = action.insert((i, term.clone()), Action::Shift(j)) {
                            match other {
                                Action::Reduce(k) => {
                                    return Err(ParserConstructionError::ShiftReduceConflict(j, k))
                                }
                                Action::Shift(k) if j == k => (),
                                _ => unreachable!(),
                            }
                        }
                        // println!("ACTION[{i}, {term:?}] = {}", Action::Shift(j));
                    }
                    Some(symbol @ ExprSymbol::Nonterminal(nonterm)) => {
                        let goto_state = self.goto(state, symbol);

                        let Some(j) = states.iter().position(|state| state == &goto_state) else {
                            continue;
                        };

                        if let Some(other) = goto.insert((i, nonterm.clone()), j) {
                            if other != j {
                                panic!("unknown error");
                            }
                        }
                    }
                    None if position.is_accept_position() => {
                        // (c)
                        if action.insert((i, L::eof()), Action::Accept).is_some() {
                            panic!("unknown error");
                        }
                        // println!("ACTION[{i}, $] = acc");
                    }
                    None => {
                        // (b)
                        if let Some(other) = action.insert(
                            (i, lookahead.clone()),
                            Action::Reduce(position.production()),
                        ) {
                            match other {
                                Action::Shift(k) => {
                                    return Err(ParserConstructionError::ShiftReduceConflict(i, k))
                                }
                                _ => unreachable!(),
                            }
                        }
                        /*
                        println!(
                            "ACTION[{i}, {lookahead:?}] = {}",
                            Action::Reduce(position.production())
                        );
                        */
                    }
                }
            }
        }

        Ok((action, goto))
    }

    /// Parses the Token stream into an AST of type A.
    pub fn parse<Token: AsRef<L>, I: IntoIterator<Item = Token>>(
        &self,
        string: I,
    ) -> Result<A, ParseError<Token>>
    where
        Token: Debug + Clone,
        L: Language,
        A: Debug + From<Token>,
    {
        // this method uses unwrap() heavily, but each use is based on prior assumptions
        // in other words, if we panic, it's because we did something very wrong, not the user

        // start with initial state, state 0
        let mut stack: Vec<usize> = vec![0];
        let mut val_stack: Vec<A> = Vec::new();

        let (action_table, goto_table) = self.get_tables()?;

        let mut string = <I as IntoIterator>::into_iter(string);

        // the next symbol
        let Some(mut a) = string.next() else {
            return Err(ParseError::UnterminatedInput);
        };

        loop {
            let s = stack.last().unwrap();

            let Some(action) = action_table.get(&(*s, a.as_ref().clone())) else {
                return Err(ParseError::UnexpectedSymbol(a));
            };

            match action {
                Action::Accept => break,
                Action::Shift(j) => {
                    val_stack.push(A::from(a.clone()));
                    stack.push(*j);
                    a = match string.next() {
                        None => return Err(ParseError::UnterminatedInput),
                        Some(a) => a,
                    }
                }
                Action::Reduce(j) => {
                    let Production { symbol, expression, action } =
                        // panicking here means implementation error
                        self.grammar.get_production(*j).unwrap();

                    // not sure if this is very fast
                    stack.drain(stack.len() - expression.len()..);

                    let tokens = val_stack.drain(val_stack.len() - expression.len()..);
                    let new_token = action(tokens.collect());
                    val_stack.push(new_token);

                    let s = stack.last().unwrap();
                    let goto_state = goto_table.get(&(*s, symbol.clone())).unwrap();
                    stack.push(*goto_state);
                }
            }
        }

        Ok(val_stack.pop().unwrap())
    }
}

#[derive(Debug, Error)]
pub enum ParserConstructionError {
    #[error("shift-reduce conflict between states {0} and {1}")]
    ShiftReduceConflict(usize, usize),
    #[error("reduce-reduce conflict between states {0} and {1}")]
    ReduceReduceConflict(usize, usize),
}

#[derive(Debug, Error)]
pub enum ParseError<Token> {
    #[error("reached EOF")]
    UnexpectedEOF,
    #[error("reached end of input, but didn't read EOF")]
    UnterminatedInput,
    #[error("unexpected token {0:?}")]
    UnexpectedSymbol(Token),
    #[error("{0}")]
    ConstructionError(#[from] ParserConstructionError),
}

#[cfg(test)]
mod test {
    use std::fmt::Debug;

    use crate::{
        grammar::{position::Position, production::Production, Grammar, GrammarBuilder},
        lang::{Language, Nonterminal},
        nonterm,
        parser::{action::Action, Parser},
        term,
    };

    use super::{Item, ItemSet};

    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    #[allow(non_camel_case_types)]
    enum Term {
        c,
        d,
        eof,
    }

    impl Debug for Term {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(
                f,
                "{}",
                match self {
                    Self::c => "c",
                    Self::d => "d",
                    Self::eof => "$",
                }
            )
        }
    }

    impl Language for Term {
        fn eof() -> Self {
            Self::eof
        }
    }

    #[derive(Debug, Clone)]
    struct Token {
        kind: Term,
    }

    impl AsRef<Term> for Token {
        fn as_ref(&self) -> &Term {
            &self.kind
        }
    }

    impl From<Term> for Token {
        fn from(value: Term) -> Self {
            Self { kind: value }
        }
    }

    impl From<Token> for () {
        fn from(_: Token) -> Self {}
    }

    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    enum Nonterm {
        Start,
        S,
        C,
    }

    impl Debug for Nonterm {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(
                f,
                "{}",
                match self {
                    Self::Start => "S'",
                    Self::S => "S",
                    Self::C => "C",
                }
            )
        }
    }

    impl Nonterminal for Nonterm {
        fn start() -> Self {
            Self::Start
        }
    }

    fn get_test_grammar() -> Grammar<Nonterm, Term, ()> {
        let mut builder = GrammarBuilder::new();
        builder
            .add_start_production(Production::new_passthrough(
                Nonterm::S,
                vec![nonterm!(Nonterm::C), nonterm!(Nonterm::C)],
            ))
            .add_nonstart_production(Production::new_passthrough(
                Nonterm::C,
                vec![term!(Term::c), nonterm!(Nonterm::C)],
            ))
            .add_nonstart_production(Production::new_passthrough(
                Nonterm::C,
                vec![term!(Term::d)],
            ));
        builder.build().unwrap()
    }

    fn get_test_parser() -> Parser<Nonterm, Term, ()> {
        Parser::new(get_test_grammar())
    }

    #[test]
    fn test_parse() {
        let parser = get_test_parser();

        parser
            .parse::<Token, _>(
                vec![Term::d, Term::d, Term::eof]
                    .into_iter()
                    .map(Token::from),
            )
            .expect("dd should parse");

        parser
            .parse(
                vec![Term::c, Term::c, Term::d, Term::d, Term::eof]
                    .into_iter()
                    .map(Token::from),
            )
            .expect("ccdd should parse");

        parser
            .parse(
                vec![Term::d, Term::c, Term::c, Term::c, Term::d, Term::eof]
                    .into_iter()
                    .map(Token::from),
            )
            .expect("dcccd should parse");
    }

    #[test]
    fn test_closure_of() {
        let parser = get_test_parser();

        assert!(
            parser
                .closure_of(ItemSet::from(Item(Position::new(0, 0), Term::eof)))
                .as_ref()
                .len()
                == 6
        );
        assert!(
            parser
                .closure_of(ItemSet::from(Item(Position::new(0, 1), Term::eof)))
                .as_ref()
                .len()
                == 1
        );
        assert!(
            parser
                .closure_of(ItemSet::from(Item(Position::new(1, 1), Term::eof)))
                .as_ref()
                .len()
                == 3
        );
        assert!(
            parser
                .closure_of(ItemSet::from_iter(vec![
                    Item(Position::new(2, 1), Term::c),
                    Item(Position::new(2, 1), Term::d),
                ]))
                .as_ref()
                .len()
                == 6
        );
        assert!(
            parser
                .closure_of(ItemSet::from_iter(vec![
                    Item(Position::new(3, 1), Term::c),
                    Item(Position::new(3, 1), Term::d),
                ]))
                .as_ref()
                .len()
                == 2
        );
    }

    #[test]
    #[ignore = "state order isn't deterministic"]
    fn test_parser_tables() {
        let parser = get_test_parser();

        let states = parser.build_states();

        assert!(states.len() == 10, "incorrect number of states");

        let (action, goto) = parser.build_tables().unwrap();

        // test ACTION
        assert!(action.get(&(0, Term::c)).unwrap() == &Action::Shift(3));
        assert!(action.get(&(0, Term::d)).unwrap() == &Action::Shift(4));
        assert!(action.get(&(1, Term::eof)).unwrap() == &Action::Accept);
        assert!(action.get(&(2, Term::c)).unwrap() == &Action::Shift(6));
        assert!(action.get(&(2, Term::d)).unwrap() == &Action::Shift(7));
        assert!(action.get(&(3, Term::c)).unwrap() == &Action::Shift(3));
        assert!(action.get(&(3, Term::d)).unwrap() == &Action::Shift(4));
        assert!(action.get(&(4, Term::c)).unwrap() == &Action::Reduce(3));
        assert!(action.get(&(4, Term::d)).unwrap() == &Action::Reduce(3));
        assert!(action.get(&(5, Term::d)).unwrap() == &Action::Reduce(1));
        assert!(action.get(&(6, Term::c)).unwrap() == &Action::Shift(6));
        assert!(action.get(&(6, Term::d)).unwrap() == &Action::Shift(7));
        assert!(action.get(&(7, Term::d)).unwrap() == &Action::Reduce(3));
        assert!(action.get(&(8, Term::c)).unwrap() == &Action::Reduce(2));
        assert!(action.get(&(9, Term::d)).unwrap() == &Action::Reduce(2));
        assert!(action.get(&(9, Term::d)).unwrap() == &Action::Reduce(2));
        assert!(action.get(&(10, Term::eof)).unwrap() == &Action::Reduce(2));

        // test GOTO
        assert!(goto.get(&(0, Nonterm::S)).unwrap() == &1);
        assert!(goto.get(&(0, Nonterm::C)).unwrap() == &2);
        assert!(goto.get(&(2, Nonterm::C)).unwrap() == &5);
        assert!(goto.get(&(3, Nonterm::C)).unwrap() == &8);
        assert!(goto.get(&(6, Nonterm::C)).unwrap() == &9);
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Item<L>(Position, L);

impl<L> Item<L> {
    /// Returns the position of this item.
    pub fn position(&self) -> &Position {
        &self.0
    }

    /// Returns the lookahead of this item.
    pub fn lookahead(&self) -> &L {
        &self.1
    }

    /// Returns a copy of this Item, advanced by one.
    /// Note: this does not and can not check if the advance is valid!
    pub fn advanced(&self) -> Item<L>
    where
        L: Clone,
    {
        let mut item = self.clone();
        item.0.advance();
        item
    }
}

#[derive(Debug, Clone)]
pub struct ItemSet<L>(HashSet<Item<L>>);

impl<L> PartialEq for ItemSet<L>
where
    L: Hash + Eq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<L> AsRef<HashSet<Item<L>>> for ItemSet<L> {
    fn as_ref(&self) -> &HashSet<Item<L>> {
        &self.0
    }
}

impl<L> AsMut<HashSet<Item<L>>> for ItemSet<L> {
    fn as_mut(&mut self) -> &mut HashSet<Item<L>> {
        &mut self.0
    }
}

impl<L> From<HashSet<Item<L>>> for ItemSet<L> {
    fn from(value: HashSet<Item<L>>) -> Self {
        Self(value)
    }
}

impl<L> FromIterator<Item<L>> for ItemSet<L>
where
    L: Hash + Eq,
{
    fn from_iter<T: IntoIterator<Item = Item<L>>>(iter: T) -> Self {
        Self(HashSet::from_iter(iter))
    }
}

impl<L> From<Item<L>> for ItemSet<L>
where
    L: Hash + Eq,
{
    fn from(value: Item<L>) -> Self {
        Self::from_iter(std::iter::once(value))
    }
}

impl<L> ItemSet<L> {
    /// Creates a new empty item set.
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns true if the item set is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns an iterator over the items of this set.
    pub fn items(&self) -> std::collections::hash_set::Iter<Item<L>> {
        self.0.iter()
    }

    pub fn with_grammar<'a, N, A>(
        &'a self,
        grammar: &'a Grammar<N, L, A>,
    ) -> ItemSetWithGrammar<'a, N, L, A> {
        ItemSetWithGrammar(self, grammar)
    }
}

impl<L> Default for ItemSet<L> {
    fn default() -> Self {
        ItemSet(HashSet::new())
    }
}

pub struct ItemSetWithGrammar<'a, N, L, A>(&'a ItemSet<L>, &'a Grammar<N, L, A>);

impl<'a, N, L, A> Display for ItemSetWithGrammar<'a, N, L, A>
where
    N: Debug,
    L: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{{")?;
        for Item(position, lookahead) in self.0.items() {
            writeln!(f, "\t{}, {:?}", position.with_grammar(self.1), lookahead)?;
        }
        write!(f, "}}")
    }
}
