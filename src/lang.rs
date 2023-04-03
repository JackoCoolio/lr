use std::{
    collections::HashSet,
    fmt::{Debug, Display},
    hash::Hash,
};

pub trait Nonterminal {
    /// Returns the start nonterminal.
    fn start() -> Self;
}

pub trait Language {
    /// Returns the EOF token for this language.
    fn eof() -> Self;
}

#[derive(Debug, Clone)]
pub struct EpsilonSet<L>(HashSet<L>, bool);

impl<L> Default for EpsilonSet<L> {
    fn default() -> Self {
        Self(HashSet::new(), false)
    }
}

impl<L> PartialEq for EpsilonSet<L>
where
    L: Hash + Eq,
{
    fn eq(&self, other: &Self) -> bool {
        self.set().eq(other.set()) && self.has_epsilon() == other.has_epsilon()
    }
}

impl<L> Eq for EpsilonSet<L> where L: Hash + Eq {}

impl<L> Display for EpsilonSet<L>
where
    L: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        for (i, term) in self.set().iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", term)?;
        }

        if self.has_epsilon() {
            if !self.set().is_empty() {
                write!(f, ", ")?;
            }
            write!(f, "\u{03b5}")?;
        }

        write!(f, "}}")
    }
}

impl<L> From<HashSet<L>> for EpsilonSet<L> {
    fn from(value: HashSet<L>) -> Self {
        Self(value, false)
    }
}

impl<L> EpsilonSet<L> {
    #[cfg(test)]
    pub(crate) fn new(set: HashSet<L>, has_epsilon: bool) -> Self {
        Self(set, has_epsilon)
    }

    pub(crate) fn has_epsilon(&self) -> bool {
        self.1
    }

    pub(crate) fn set(&self) -> &HashSet<L> {
        &self.0
    }

    pub(crate) fn set_mut(&mut self) -> &mut HashSet<L> {
        &mut self.0
    }

    /// Marks this as an epsilon set and returns `true` if it wasn't marked as such before.
    pub(crate) fn mark_epsilon(&mut self) -> bool {
        let was_false = !self.1;
        self.1 = true;
        was_false
    }
}

impl<L> AsRef<HashSet<L>> for EpsilonSet<L> {
    fn as_ref(&self) -> &HashSet<L> {
        &self.0
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Epsilon;

impl Display for Epsilon {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\u{0370}")
    }
}
