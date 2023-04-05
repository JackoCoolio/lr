use std::fmt::{Debug, Display};

/// A symbol that can be on the right side of a [Production].
/// Either a `Nonterminal` or a `Terminal`.
/// `N` is the type of the nonterminal and `L` is the type of the terminal.
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub enum GrammarSymbol<N, L> {
    Nonterminal(N),
    Terminal(L),
}

impl<N, L> Debug for GrammarSymbol<N, L>
where
    N: Debug,
    L: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Terminal(term) => write!(f, "{:?}", term),
            Self::Nonterminal(nonterm) => write!(f, "{:?}", nonterm),
        }
    }
}

impl<N, L> Display for GrammarSymbol<N, L>
where
    N: Display,
    L: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Terminal(term) => write!(f, "{}", term),
            Self::Nonterminal(nonterm) => write!(f, "{}", nonterm),
        }
    }
}

/// `term!(x)` expands to `ExprSymbol::Terminal(x)`.
#[macro_export]
macro_rules! term {
    ($x:expr) => {
        $crate::grammar::production::GrammarSymbol::Terminal($x)
    };
}

/// `nonterm!(x)` expands to `ExprSymbol::Nonterminal(x)`.
#[macro_export]
macro_rules! nonterm {
    ($x:expr) => {
        $crate::grammar::production::GrammarSymbol::Nonterminal($x)
    };
}

/// A single production in the grammar.
/// `X -> epsilon` is represented by a `Production` with an empty `expression`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Production<N, L, A> {
    pub(crate) symbol: N,
    pub(crate) expression: Vec<GrammarSymbol<N, L>>,
    pub(crate) action: fn(Vec<A>) -> A,
}

impl<N, T, A> Production<N, T, A> {
    /// Creates a new Production with an action that takes the node at the top of the stack and
    /// returns it.
    pub fn new_passthrough(symbol: N, expression: Vec<GrammarSymbol<N, T>>) -> Self
    where
        A: Clone,
    {
        Self {
            symbol,
            expression,
            action: |nodes| nodes.first().unwrap().clone(),
        }
    }

    /// Creates a new Production with the given action.
    pub fn new(symbol: N, expression: Vec<GrammarSymbol<N, T>>, action: fn(Vec<A>) -> A) -> Self {
        Self {
            symbol,
            expression,
            action,
        }
    }
}
