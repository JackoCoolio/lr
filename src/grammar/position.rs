use std::{
    fmt::{Debug, Display, Formatter},
    hash::Hash,
};

use super::{production::GrammarSymbol, Grammar};

/// A position that the parser could be at during the parsing process.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Position {
    /// The index of the production that this position lies in
    production: usize,
    /// The index of the symbol that this position lies before
    /// For example, in the position:
    /// S -> a . A b
    /// `Position.expression` is 1
    /// In S -> a A b .
    /// `Position.expression` is 3
    expression: usize,
}

impl Ord for Position {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl PartialOrd for Position {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering::*;
        match self.production.cmp(&other.production) {
            Less => return Some(Less),
            Greater => return Some(Greater),
            _ => (),
        };

        Some(self.expression.cmp(&other.expression))
    }
}

impl Position {
    pub(crate) fn new(production: usize, expression: usize) -> Self {
        Self {
            production,
            expression,
        }
    }

    #[inline]
    pub(crate) fn production(&self) -> usize {
        self.production
    }

    #[inline]
    pub(crate) fn expression(&self) -> usize {
        self.expression
    }

    /// Advances this Position by one within the expression.
    /// Note: this does not and can not check if the advance is valid!
    #[inline]
    pub(crate) fn advance(&mut self) {
        self.expression += 1;
    }

    /// Returns true if this position is the final position from which the input string is
    /// accepted. Assumes that the grammar is augmented, with the augment rule at index 0.
    pub(crate) fn is_accept_position(&self) -> bool {
        self.production == 0 && self.expression == 1
    }
}

impl Position {
    pub(crate) fn with_grammar<'a, N, L, A>(
        &'a self,
        grammar: &'a Grammar<N, L, A>,
    ) -> PositionWithGrammar<'a, N, L, A> {
        PositionWithGrammar {
            position: self,
            grammar,
        }
    }
}

pub(crate) struct PositionWithGrammar<'a, N, L, A> {
    position: &'a Position,
    grammar: &'a Grammar<N, L, A>,
}

impl<N, L, A> Display for PositionWithGrammar<'_, N, L, A>
where
    N: Debug,
    L: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let production = self
            .grammar
            .get_production(self.position.production)
            .unwrap();

        write!(f, "{:?} ->", production.symbol)?;

        for (i, symbol) in production.expression.iter().enumerate() {
            if i == self.position.expression {
                write!(f, " .")?;
            }
            write!(f, " {:?}", symbol)?;
        }

        if self.position.expression == production.expression.len() {
            write!(f, " .")?;
        }

        Ok(())
    }
}

impl<N, L, A> Grammar<N, L, A> {
    fn get_nth_symbol(&self, pos: &Position, n: usize) -> Option<&GrammarSymbol<N, L>> {
        let expr = &self.productions[pos.production].expression;
        expr.get(pos.expression + n)
    }

    pub(crate) fn get_locus(&self, pos: &Position) -> Option<&GrammarSymbol<N, L>> {
        self.get_nth_symbol(pos, 0)
    }
}
