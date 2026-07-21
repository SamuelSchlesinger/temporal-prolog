use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub type Name = String;
pub type Var = String;
pub type Subst = BTreeMap<Var, Term>;
pub type World = BTreeSet<Atom>;

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Term {
    Var(Var),
    Fun(Name, Vec<Term>),
    Prev(Box<Term>),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Atom {
    pub name: Name,
    pub terms: Vec<Term>,
}

impl Atom {
    pub fn new(name: impl Into<String>, terms: Vec<Term>) -> Self {
        Self {
            name: name.into(),
            terms,
        }
    }

    pub fn ground(&self) -> bool {
        self.terms.iter().all(Term::ground)
    }

    pub fn vars(&self) -> BTreeSet<Var> {
        self.terms.iter().flat_map(Term::vars).collect()
    }

    pub fn apply(&self, subst: &Subst) -> Self {
        Self::new(
            &self.name,
            self.terms.iter().map(|t| t.apply(subst)).collect(),
        )
    }
}

impl Term {
    pub fn ground(&self) -> bool {
        match self {
            Self::Var(_) => false,
            Self::Fun(_, terms) => terms.iter().all(Self::ground),
            Self::Prev(term) => term.ground(),
        }
    }

    pub fn vars(&self) -> BTreeSet<Var> {
        match self {
            Self::Var(var) => [var.clone()].into_iter().collect(),
            Self::Fun(_, terms) => terms.iter().flat_map(Self::vars).collect(),
            Self::Prev(term) => term.vars(),
        }
    }

    pub fn apply(&self, subst: &Subst) -> Self {
        match self {
            Self::Var(var) => subst.get(var).map_or_else(
                || self.clone(),
                |term| {
                    if term == self {
                        term.clone()
                    } else {
                        term.apply(subst)
                    }
                },
            ),
            Self::Fun(name, terms) => Self::Fun(
                name.clone(),
                terms.iter().map(|term| term.apply(subst)).collect(),
            ),
            Self::Prev(term) => Self::Prev(Box::new(term.apply(subst))),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Cond {
    Atom(Atom),
    Neg(Box<Cond>),
    Prev(Box<Cond>),
    HasBeen(Box<Cond>),
    Once(Box<Cond>),
    Since(Box<Cond>, Box<Cond>),
    After(Box<Cond>, Box<Cond>),
    For(Box<Cond>, usize),
    And(Vec<Cond>),
    Eventually(Box<Cond>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResultFormula {
    Atom(Atom),
    Reduction(Name, Vec<Term>, Term),
    Always(Box<ResultFormula>),
    Until(Box<ResultFormula>, Cond),
    AtNext(Box<ResultFormula>, Cond),
    And(Vec<ResultFormula>),
    Next(Box<ResultFormula>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SourceRule {
    Fact(ResultFormula),
    Rule(Vec<Cond>, ResultFormula),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program {
    pub rules: Vec<SourceRule>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct NormalCond {
    pub depth: usize,
    pub negated: bool,
    pub atom: Atom,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct NormalRule {
    pub conditions: Vec<NormalCond>,
    pub head: Atom,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NormalizedProgram {
    pub rules: Vec<NormalRule>,
    pub pattern_functions: BTreeSet<Name>,
    /// Predicate names introduced by normalization, excluding fresh variables.
    pub auxiliary_predicates: BTreeSet<Name>,
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var(var) => write!(f, "{var}"),
            Self::Fun(name, terms) if terms.is_empty() => write!(f, "{name}"),
            Self::Fun(name, terms) => {
                write!(f, "{name}(")?;
                for (index, term) in terms.iter().enumerate() {
                    if index > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, "{term}")?;
                }
                write!(f, ")")
            }
            Self::Prev(term) => write!(f, "@{term}"),
        }
    }
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.terms.is_empty() {
            write!(f, "{}", self.name)
        } else {
            write!(f, "{}(", self.name)?;
            for (index, term) in self.terms.iter().enumerate() {
                if index > 0 {
                    write!(f, ",")?;
                }
                write!(f, "{term}")?;
            }
            write!(f, ")")
        }
    }
}
