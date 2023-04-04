use std::fmt::{Debug, Display};

/// A symbol that can be on the right side of a [Production].
/// Either a `Nonterminal` or a `Terminal`.
/// `N` is the type of the nonterminal and `L` is the type of the terminal.
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub enum ExprSymbol<N, L> {
    Nonterminal(N),
    Terminal(L),
}

impl<N, L> Debug for ExprSymbol<N, L>
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

impl<N, L> Display for ExprSymbol<N, L>
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
        $crate::grammar::production::ExprSymbol::Terminal($x)
    };
}

/// `nonterm!(x)` expands to `ExprSymbol::Nonterminal(x)`.
#[macro_export]
macro_rules! nonterm {
    ($x:expr) => {
        $crate::grammar::production::ExprSymbol::Nonterminal($x)
    };
}

/// A single production in the grammar.
/// `X -> epsilon` is represented by a `Production` with an empty `expression`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Production<Nonterm, Terminal, AstNode, Action> {
    pub(crate) symbol: Nonterm,
    pub(crate) expression: Vec<ExprSymbol<Nonterm, Terminal>>,
    pub(crate) action: Action,
}

impl<N, T, A, Action> Production<N, T, A, Action>
where
    Action: Fn(Vec<A>) -> A,
{
    /// Creates a new Production.
    pub fn new(symbol: N, expression: Vec<ExprSymbol<N, T>>, action: Action) -> Self {
        Self {
            symbol,
            expression,
            action,
        }
    }

    /// Runs this Production's semantic action on a list of AST nodes.
    pub fn action(&self, nodes: Vec<A>) -> A {
        self.action.call(nodes)
    }
}
