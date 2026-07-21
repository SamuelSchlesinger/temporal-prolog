//! Source-syntax rendering for parsed and normalized Temporal Prolog ASTs.
//!
//! These functions intentionally do not replace [`std::fmt::Display`] on
//! [`Term`] and [`Atom`]: `Display` is the compact,
//! canonical representation used by semantic digests, while this module emits
//! readable source text with lists, infix operators, and precedence-preserving
//! parentheses.

use crate::ast::{
    Atom, Cond, NormalCond, NormalRule, NormalizedProgram, Program, ResultFormula, SourceRule, Term,
};

/// Render a well-formed term as parseable source syntax.
pub fn pretty_term(term: &Term) -> String {
    match term {
        Term::Var(variable) => variable.clone(),
        Term::Fun(name, terms) if terms.is_empty() => name.clone(),
        Term::Fun(name, terms) if name == "." && terms.len() == 2 => {
            format!(
                "[{}{}]",
                pretty_term(&terms[0]),
                pretty_list_tail(&terms[1])
            )
        }
        Term::Fun(name, terms) if is_binary_arithmetic(name, terms) => format!(
            "{} {name} {}",
            pretty_term_operand(&terms[0]),
            pretty_term_operand(&terms[1])
        ),
        Term::Fun(name, terms) => format!(
            "{name}({})",
            terms.iter().map(pretty_term).collect::<Vec<_>>().join(", ")
        ),
        Term::Prev(term) => format!("@{}", pretty_term_operand(term)),
    }
}

fn is_binary_arithmetic(name: &str, terms: &[Term]) -> bool {
    terms.len() == 2 && matches!(name, "+" | "-" | "*" | "div" | "mod")
}

fn pretty_term_operand(term: &Term) -> String {
    if matches!(term, Term::Fun(name, terms) if is_binary_arithmetic(name, terms)) {
        format!("({})", pretty_term(term))
    } else {
        match term {
            Term::Var(_) | Term::Fun(_, _) => pretty_term(term),
            Term::Prev(_) => format!("({})", pretty_term(term)),
        }
    }
}

fn pretty_list_tail(term: &Term) -> String {
    match term {
        Term::Fun(name, terms) if name == "[]" && terms.is_empty() => String::new(),
        Term::Fun(name, terms) if name == "." && terms.len() == 2 => format!(
            ", {}{}",
            pretty_term(&terms[0]),
            pretty_list_tail(&terms[1])
        ),
        term => format!(" | {}", pretty_term(term)),
    }
}

/// Render an atom, using infix syntax for built-in binary relations.
pub fn pretty_atom(atom: &Atom) -> String {
    match atom.terms.as_slice() {
        [left, right] if matches!(atom.name.as_str(), "=" | "is" | ">" | "<" | ">=" | "<=") => {
            format!("{} {} {}", pretty_term(left), atom.name, pretty_term(right))
        }
        [] => atom.name.clone(),
        terms => format!(
            "{}({})",
            atom.name,
            terms.iter().map(pretty_term).collect::<Vec<_>>().join(", ")
        ),
    }
}

/// Render a condition with enough parentheses to preserve its exact AST.
pub fn pretty_condition(condition: &Cond) -> String {
    match condition {
        Cond::Atom(atom) => pretty_atom(atom),
        Cond::Neg(condition) => format!("~{}", pretty_condition_atom(condition)),
        Cond::Prev(condition) => format!("@{}", pretty_condition_atom(condition)),
        Cond::HasBeen(condition) => format!("#{}", pretty_condition_atom(condition)),
        Cond::Once(condition) => format!("?{}", pretty_condition_atom(condition)),
        Cond::Since(left, right) => format!(
            "{} since {}",
            pretty_condition_atom(left),
            pretty_condition_atom(right)
        ),
        Cond::After(left, right) => format!(
            "{} after {}",
            pretty_condition_atom(left),
            pretty_condition_atom(right)
        ),
        Cond::For(condition, count) => {
            format!("{} for {count}", pretty_condition_atom(condition))
        }
        Cond::And(conditions) => conditions
            .iter()
            .map(pretty_condition_atom)
            .collect::<Vec<_>>()
            .join(" /\\ "),
        Cond::Eventually(condition) => {
            format!("eventually {}", pretty_condition_atom(condition))
        }
    }
}

fn pretty_condition_atom(condition: &Cond) -> String {
    match condition {
        Cond::Atom(_) | Cond::Neg(_) | Cond::Prev(_) => pretty_condition(condition),
        _ => format!("({})", pretty_condition(condition)),
    }
}

/// Render a result formula with enough parentheses to preserve its exact AST.
pub fn pretty_result(result: &ResultFormula) -> String {
    match result {
        ResultFormula::Atom(atom) => pretty_atom(atom),
        ResultFormula::Reduction(name, arguments, body) => format!(
            "{}({}) -> {}",
            name,
            arguments
                .iter()
                .map(pretty_term)
                .collect::<Vec<_>>()
                .join(", "),
            pretty_term(body)
        ),
        ResultFormula::Always(result) => format!("always {}", pretty_result_atom(result)),
        ResultFormula::Until(result, condition) => format!(
            "{} until {}",
            pretty_result_atom(result),
            pretty_condition_atom(condition)
        ),
        ResultFormula::AtNext(result, condition) => format!(
            "{} atnext {}",
            pretty_result_atom(result),
            pretty_condition_atom(condition)
        ),
        ResultFormula::And(results) => results
            .iter()
            .map(pretty_result_atom)
            .collect::<Vec<_>>()
            .join(" /\\ "),
        ResultFormula::Next(result) => format!("next {}", pretty_result_atom(result)),
    }
}

fn pretty_result_atom(result: &ResultFormula) -> String {
    match result {
        ResultFormula::Atom(_) => pretty_result(result),
        _ => format!("({})", pretty_result(result)),
    }
}

/// Render a source rule, including its terminating period.
pub fn pretty_rule(rule: &SourceRule) -> String {
    match rule {
        SourceRule::Fact(result) => format!("{}.", pretty_result(result)),
        SourceRule::Rule(conditions, result) => format!(
            "{} => {}.",
            conditions
                .iter()
                .map(pretty_condition_atom)
                .collect::<Vec<_>>()
                .join(" /\\ "),
            pretty_result(result)
        ),
    }
}

/// Render a complete source program with one rule per line.
pub fn pretty_program(program: &Program) -> String {
    trailing_newline(program.rules.iter().map(pretty_rule))
}

/// Render a normal-form condition.
pub fn pretty_normal_condition(condition: &NormalCond) -> String {
    format!(
        "{}{}{}",
        "@".repeat(condition.depth),
        if condition.negated { "~" } else { "" },
        pretty_atom(&condition.atom)
    )
}

/// Render a normal-form rule, including its terminating period.
pub fn pretty_normal_rule(rule: &NormalRule) -> String {
    if rule.conditions.is_empty() {
        format!("{}.", pretty_atom(&rule.head))
    } else {
        format!(
            "{} => {}.",
            rule.conditions
                .iter()
                .map(pretty_normal_condition)
                .collect::<Vec<_>>()
                .join(" /\\ "),
            pretty_atom(&rule.head)
        )
    }
}

/// Render all rules in a normalized program with one rule per line.
pub fn pretty_normalized_program(program: &NormalizedProgram) -> String {
    trailing_newline(program.rules.iter().map(pretty_normal_rule))
}

fn trailing_newline(lines: impl Iterator<Item = String>) -> String {
    let mut rendered = lines.collect::<Vec<_>>().join("\n");
    if !rendered.is_empty() {
        rendered.push('\n');
    }
    rendered
}
