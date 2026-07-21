use crate::ast::*;
use std::collections::{BTreeMap, BTreeSet};

pub fn normalize(program: Program) -> Result<NormalizedProgram, String> {
    validate_program_symbols(&program)?;
    let pf_names = reduction_names(&program.rules);
    validate_term_previous(&program.rules, &pf_names)?;
    let mut fresh = Fresh::new(identifiers(&program.rules));
    let mut rules = step1(program.rules, &mut fresh)?;
    rules = step2(rules, &mut fresh)?;
    rules = step3(rules, &pf_names, &mut fresh)?;
    rules = step4(rules, &mut fresh)?;
    let mut normal = Vec::new();
    for rule in rules {
        normal.push(to_normal(rule)?);
    }
    let normal_predicates = normal
        .iter()
        .flat_map(|rule| {
            std::iter::once(&rule.head.name)
                .chain(rule.conditions.iter().map(|condition| &condition.atom.name))
        })
        .cloned()
        .collect::<BTreeSet<_>>();
    let auxiliary_predicates = fresh
        .generated
        .intersection(&normal_predicates)
        .cloned()
        .collect();
    Ok(NormalizedProgram {
        rules: normal,
        pattern_functions: pf_names,
        auxiliary_predicates,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AtomRole {
    Condition,
    Result,
}

/// Validate fixed symbol signatures and external namespaces before
/// normalization can erase source distinctions.
pub fn validate_program_symbols(program: &Program) -> Result<(), String> {
    let mut patterns = BTreeMap::new();
    for rule in &program.rules {
        let result = match rule {
            SourceRule::Fact(result) | SourceRule::Rule(_, result) => result,
        };
        collect_pattern_signatures(result, &mut patterns)?;
    }

    let mut predicates = BTreeMap::new();
    let mut constructors = BTreeMap::new();
    for rule in &program.rules {
        validate_rule_symbols(rule, &patterns, &mut predicates, &mut constructors)?;
    }
    Ok(())
}

fn collect_pattern_signatures(
    result: &ResultFormula,
    patterns: &mut BTreeMap<Name, usize>,
) -> Result<(), String> {
    match result {
        ResultFormula::Atom(_) => Ok(()),
        ResultFormula::Reduction(name, args, _) => {
            if external_predicate_arity(name).is_some() || arithmetic_function_arity(name).is_some()
            {
                return Err(format!("pattern function name {name:?} is reserved"));
            }
            remember_signature(patterns, "pattern function", name, args.len(), "input ")
        }
        ResultFormula::Always(result) | ResultFormula::Next(result) => {
            collect_pattern_signatures(result, patterns)
        }
        ResultFormula::Until(result, _) | ResultFormula::AtNext(result, _) => {
            collect_pattern_signatures(result, patterns)
        }
        ResultFormula::And(results) => {
            for result in results {
                collect_pattern_signatures(result, patterns)?;
            }
            Ok(())
        }
    }
}

fn validate_rule_symbols(
    rule: &SourceRule,
    patterns: &BTreeMap<Name, usize>,
    predicates: &mut BTreeMap<Name, usize>,
    constructors: &mut BTreeMap<Name, usize>,
) -> Result<(), String> {
    match rule {
        SourceRule::Fact(result) => {
            validate_result_symbols(result, patterns, predicates, constructors)
        }
        SourceRule::Rule(conditions, result) => {
            for condition in conditions {
                validate_cond_symbols(condition, patterns, predicates, constructors)?;
            }
            validate_result_symbols(result, patterns, predicates, constructors)
        }
    }
}

fn validate_result_symbols(
    result: &ResultFormula,
    patterns: &BTreeMap<Name, usize>,
    predicates: &mut BTreeMap<Name, usize>,
    constructors: &mut BTreeMap<Name, usize>,
) -> Result<(), String> {
    match result {
        ResultFormula::Atom(atom) => {
            validate_atom_symbols(atom, AtomRole::Result, patterns, predicates, constructors)
        }
        ResultFormula::Reduction(_, args, body) => {
            for term in args.iter().chain([body]) {
                validate_term_symbols(term, patterns, constructors)?;
            }
            Ok(())
        }
        ResultFormula::Always(result) | ResultFormula::Next(result) => {
            validate_result_symbols(result, patterns, predicates, constructors)
        }
        ResultFormula::Until(result, condition) | ResultFormula::AtNext(result, condition) => {
            validate_result_symbols(result, patterns, predicates, constructors)?;
            validate_cond_symbols(condition, patterns, predicates, constructors)
        }
        ResultFormula::And(results) => {
            for result in results {
                validate_result_symbols(result, patterns, predicates, constructors)?;
            }
            Ok(())
        }
    }
}

fn validate_cond_symbols(
    condition: &Cond,
    patterns: &BTreeMap<Name, usize>,
    predicates: &mut BTreeMap<Name, usize>,
    constructors: &mut BTreeMap<Name, usize>,
) -> Result<(), String> {
    match condition {
        Cond::Atom(atom) => validate_atom_symbols(
            atom,
            AtomRole::Condition,
            patterns,
            predicates,
            constructors,
        ),
        Cond::Neg(condition)
        | Cond::Prev(condition)
        | Cond::HasBeen(condition)
        | Cond::Once(condition)
        | Cond::For(condition, _)
        | Cond::Eventually(condition) => {
            validate_cond_symbols(condition, patterns, predicates, constructors)
        }
        Cond::Since(left, right) | Cond::After(left, right) => {
            validate_cond_symbols(left, patterns, predicates, constructors)?;
            validate_cond_symbols(right, patterns, predicates, constructors)
        }
        Cond::And(conditions) => {
            for condition in conditions {
                validate_cond_symbols(condition, patterns, predicates, constructors)?;
            }
            Ok(())
        }
    }
}

fn validate_atom_symbols(
    atom: &Atom,
    role: AtomRole,
    patterns: &BTreeMap<Name, usize>,
    predicates: &mut BTreeMap<Name, usize>,
    constructors: &mut BTreeMap<Name, usize>,
) -> Result<(), String> {
    if let Some(expected) = external_predicate_arity(&atom.name) {
        if role == AtomRole::Result {
            return Err(format!(
                "external predicate {:?} cannot appear in a rule result",
                atom.name
            ));
        }
        if atom.terms.len() != expected {
            return Err(format!(
                "external predicate {:?} expects arity {expected}, found {}",
                atom.name,
                atom.terms.len()
            ));
        }
    } else if let Some(input_arity) = patterns.get(&atom.name) {
        let expected = input_arity + 1;
        if atom.terms.len() != expected {
            return Err(format!(
                "pattern function {:?} has relational arity {expected}, found {}",
                atom.name,
                atom.terms.len()
            ));
        }
    } else {
        remember_signature(predicates, "predicate", &atom.name, atom.terms.len(), "")?;
    }
    for term in &atom.terms {
        validate_term_symbols(term, patterns, constructors)?;
    }
    Ok(())
}

fn validate_term_symbols(
    term: &Term,
    patterns: &BTreeMap<Name, usize>,
    constructors: &mut BTreeMap<Name, usize>,
) -> Result<(), String> {
    match term {
        Term::Var(_) => Ok(()),
        Term::Prev(term) => validate_term_symbols(term, patterns, constructors),
        Term::Fun(name, terms) => {
            if let Some(expected) = patterns.get(name) {
                if terms.len() != *expected {
                    return Err(format!(
                        "pattern function {name:?} expects input arity {expected}, found {}",
                        terms.len()
                    ));
                }
            } else if let Some(expected) = arithmetic_function_arity(name) {
                if terms.len() != expected {
                    return Err(format!(
                        "arithmetic operator {name:?} expects arity {expected}, found {}",
                        terms.len()
                    ));
                }
            } else {
                remember_signature(constructors, "constructor", name, terms.len(), "")?;
            }
            for term in terms {
                validate_term_symbols(term, patterns, constructors)?;
            }
            Ok(())
        }
    }
}

fn remember_signature(
    signatures: &mut BTreeMap<Name, usize>,
    kind: &str,
    name: &str,
    arity: usize,
    arity_label: &str,
) -> Result<(), String> {
    match signatures.get(name) {
        None => {
            signatures.insert(name.to_string(), arity);
            Ok(())
        }
        Some(expected) if *expected == arity => Ok(()),
        Some(expected) => Err(format!(
            "{kind} {name:?} has inconsistent {arity_label}arity: expected {expected}, found {arity}"
        )),
    }
}

struct Fresh {
    used: BTreeSet<String>,
    counter: usize,
    generated: BTreeSet<String>,
}

impl Fresh {
    fn new(used: BTreeSet<String>) -> Self {
        let counter = used
            .iter()
            .filter_map(|identifier| auxiliary_suffix(identifier))
            .max()
            .map_or(0, |value| value + 1);
        Self {
            used,
            counter,
            generated: BTreeSet::new(),
        }
    }
    fn name(&mut self, prefix: &str) -> String {
        loop {
            let name = format!("{prefix}_aux{}", self.counter);
            self.counter += 1;
            if self.used.insert(name.clone()) {
                self.generated.insert(name.clone());
                return name;
            }
        }
    }
}

fn auxiliary_suffix(identifier: &str) -> Option<usize> {
    let digit_count = identifier
        .chars()
        .rev()
        .take_while(char::is_ascii_digit)
        .count();
    if digit_count == 0 {
        return None;
    }
    let prefix = &identifier[..identifier.len() - digit_count];
    if !prefix.ends_with("_aux") {
        return None;
    }
    identifier[identifier.len() - digit_count..].parse().ok()
}

fn step1(mut rules: Vec<SourceRule>, fresh: &mut Fresh) -> Result<Vec<SourceRule>, String> {
    for _ in 0..1000 {
        let mut changed = false;
        let mut next = Vec::new();
        for rule in rules {
            let expanded = step1_rule(rule, fresh)?;
            changed |= expanded.1;
            next.extend(expanded.0);
        }
        if !changed {
            return Ok(next);
        }
        rules = next;
    }
    Err("normalizer step 1 exceeded its iteration limit".into())
}

fn step1_rule(rule: SourceRule, fresh: &mut Fresh) -> Result<(Vec<SourceRule>, bool), String> {
    match rule {
        SourceRule::Fact(ResultFormula::And(results)) => Ok((
            flatten_results(results)
                .into_iter()
                .map(SourceRule::Fact)
                .collect(),
            true,
        )),
        SourceRule::Rule(conditions, ResultFormula::And(results)) => Ok((
            flatten_results(results)
                .into_iter()
                .map(|result| SourceRule::Rule(conditions.clone(), result))
                .collect(),
            true,
        )),
        SourceRule::Rule(conditions, result)
            if conditions.iter().any(|c| matches!(c, Cond::And(_))) =>
        {
            Ok((
                vec![SourceRule::Rule(
                    conditions.into_iter().flat_map(flatten_cond).collect(),
                    result,
                )],
                true,
            ))
        }
        SourceRule::Fact(ResultFormula::Always(result)) => {
            Ok((vec![SourceRule::Fact(*result)], true))
        }
        SourceRule::Rule(conditions, ResultFormula::Always(result)) => {
            let args = vars_result(&result).into_iter().map(Term::Var).collect();
            let aux = Atom::new(fresh.name("always"), args);
            Ok((
                vec![
                    SourceRule::Rule(conditions, ResultFormula::Atom(aux.clone())),
                    SourceRule::Rule(
                        vec![Cond::Prev(Box::new(Cond::Atom(aux.clone())))],
                        ResultFormula::Atom(aux.clone()),
                    ),
                    SourceRule::Rule(vec![Cond::Atom(aux)], *result),
                ],
                true,
            ))
        }
        SourceRule::Fact(ResultFormula::Until(result, trigger)) => Ok((
            vec![SourceRule::Rule(
                vec![Cond::Neg(Box::new(trigger))],
                *result,
            )],
            true,
        )),
        SourceRule::Rule(conditions, ResultFormula::Until(result, trigger)) => {
            let vars = union(vars_result(&result), vars_cond(&trigger));
            let aux = Atom::new(
                fresh.name("until"),
                vars.into_iter().map(Term::Var).collect(),
            );
            Ok((
                vec![
                    SourceRule::Rule(conditions, ResultFormula::Atom(aux.clone())),
                    SourceRule::Rule(
                        vec![
                            Cond::Prev(Box::new(Cond::Atom(aux.clone()))),
                            Cond::Prev(Box::new(Cond::Neg(Box::new(trigger.clone())))),
                        ],
                        ResultFormula::Atom(aux.clone()),
                    ),
                    SourceRule::Rule(vec![Cond::Atom(aux), Cond::Neg(Box::new(trigger))], *result),
                ],
                true,
            ))
        }
        SourceRule::Fact(ResultFormula::AtNext(result, trigger)) => {
            Ok((vec![SourceRule::Rule(vec![trigger], *result)], true))
        }
        SourceRule::Rule(conditions, ResultFormula::AtNext(result, trigger)) => {
            let vars = union(vars_result(&result), vars_cond(&trigger));
            let aux = Atom::new(
                fresh.name("atnext"),
                vars.into_iter().map(Term::Var).collect(),
            );
            Ok((
                vec![
                    SourceRule::Rule(conditions, ResultFormula::Atom(aux.clone())),
                    SourceRule::Rule(
                        vec![
                            Cond::Prev(Box::new(Cond::Atom(aux.clone()))),
                            Cond::Prev(Box::new(Cond::Neg(Box::new(trigger.clone())))),
                        ],
                        ResultFormula::Atom(aux.clone()),
                    ),
                    SourceRule::Rule(vec![Cond::Atom(aux), trigger], *result),
                ],
                true,
            ))
        }
        SourceRule::Fact(ResultFormula::Next(result)) => {
            let aux = Atom::new(
                fresh.name("next"),
                vars_result(&result).into_iter().map(Term::Var).collect(),
            );
            Ok((
                vec![
                    SourceRule::Fact(ResultFormula::Atom(aux.clone())),
                    SourceRule::Rule(vec![Cond::Prev(Box::new(Cond::Atom(aux)))], *result),
                ],
                true,
            ))
        }
        SourceRule::Rule(conditions, ResultFormula::Next(result)) => {
            let aux = Atom::new(
                fresh.name("next"),
                vars_result(&result).into_iter().map(Term::Var).collect(),
            );
            Ok((
                vec![
                    SourceRule::Rule(conditions, ResultFormula::Atom(aux.clone())),
                    SourceRule::Rule(vec![Cond::Prev(Box::new(Cond::Atom(aux)))], *result),
                ],
                true,
            ))
        }
        other => Ok((vec![other], false)),
    }
}

fn step2(mut rules: Vec<SourceRule>, fresh: &mut Fresh) -> Result<Vec<SourceRule>, String> {
    for _ in 0..1000 {
        let mut changed = false;
        let mut next = Vec::new();
        for rule in rules {
            match rule {
                SourceRule::Rule(mut conditions, result) => {
                    if let Some(index) = conditions.iter().position(has_step2) {
                        let selected = conditions.remove(index);
                        next.extend(transform_step2(selected, result, conditions, fresh)?);
                        changed = true;
                    } else {
                        next.push(SourceRule::Rule(conditions, result));
                    }
                }
                fact => next.push(fact),
            }
        }
        if !changed {
            return Ok(next);
        }
        rules = next;
    }
    Err("normalizer step 2 exceeded its iteration limit".into())
}

fn transform_step2(
    cond: Cond,
    result: ResultFormula,
    mut others: Vec<Cond>,
    fresh: &mut Fresh,
) -> Result<Vec<SourceRule>, String> {
    match cond {
        Cond::And(conditions) => {
            let mut flattened: Vec<_> = conditions.into_iter().flat_map(flatten_cond).collect();
            flattened.append(&mut others);
            Ok(vec![SourceRule::Rule(flattened, result)])
        }
        Cond::HasBeen(inner) => {
            let atom = Atom::new(
                fresh.name("hasbeen"),
                vars_cond(&inner).into_iter().map(Term::Var).collect(),
            );
            let inner_cond = *inner;
            Ok(vec![
                rule_with_aux(atom.clone(), others, result),
                SourceRule::Rule(
                    vec![
                        inner_cond.clone(),
                        Cond::Atom(Atom::new("at", vec![constant("0")])),
                    ],
                    ResultFormula::Atom(atom.clone()),
                ),
                SourceRule::Rule(
                    vec![Cond::Prev(Box::new(Cond::Atom(atom.clone()))), inner_cond],
                    ResultFormula::Atom(atom),
                ),
            ])
        }
        Cond::Once(inner) | Cond::Eventually(inner) => {
            let atom = Atom::new(
                fresh.name("once"),
                vars_cond(&inner).into_iter().map(Term::Var).collect(),
            );
            Ok(vec![
                rule_with_aux(atom.clone(), others, result),
                SourceRule::Rule(vec![*inner], ResultFormula::Atom(atom.clone())),
                SourceRule::Rule(
                    vec![Cond::Prev(Box::new(Cond::Atom(atom.clone())))],
                    ResultFormula::Atom(atom),
                ),
            ])
        }
        Cond::Since(left, right) => {
            let atom = Atom::new(
                fresh.name("since"),
                union(vars_cond(&left), vars_cond(&right))
                    .into_iter()
                    .map(Term::Var)
                    .collect(),
            );
            Ok(vec![
                rule_with_aux(atom.clone(), others, result),
                SourceRule::Rule(
                    vec![*right, *left.clone()],
                    ResultFormula::Atom(atom.clone()),
                ),
                SourceRule::Rule(
                    vec![Cond::Prev(Box::new(Cond::Atom(atom.clone()))), *left],
                    ResultFormula::Atom(atom),
                ),
            ])
        }
        Cond::After(left, right) => {
            let seen = Atom::new(
                fresh.name("after_seen"),
                vars_cond(&right).into_iter().map(Term::Var).collect(),
            );
            let completed = Atom::new(
                fresh.name("after"),
                union(vars_cond(&left), vars_cond(&right))
                    .into_iter()
                    .map(Term::Var)
                    .collect(),
            );
            Ok(vec![
                rule_with_aux(completed.clone(), others, result),
                SourceRule::Rule(vec![*right], ResultFormula::Atom(seen.clone())),
                SourceRule::Rule(
                    vec![Cond::Prev(Box::new(Cond::Atom(seen.clone())))],
                    ResultFormula::Atom(seen.clone()),
                ),
                SourceRule::Rule(
                    vec![Cond::Prev(Box::new(Cond::Atom(seen))), *left],
                    ResultFormula::Atom(completed.clone()),
                ),
                SourceRule::Rule(
                    vec![Cond::Prev(Box::new(Cond::Atom(completed.clone())))],
                    ResultFormula::Atom(completed),
                ),
            ])
        }
        Cond::For(inner, count) => {
            if count == 0 {
                return Err("the right operand of for must be positive".into());
            }
            let mut conditions = (0..count)
                .map(|depth| nest_prev(depth, (*inner).clone()))
                .collect::<Vec<_>>();
            conditions.append(&mut others);
            Ok(vec![SourceRule::Rule(conditions, result)])
        }
        Cond::Neg(inner) if has_step2(&inner) => {
            let atom = Atom::new(
                fresh.name("neg"),
                vars_cond(&inner).into_iter().map(Term::Var).collect(),
            );
            let mut output = vec![rule_with_condition(
                Cond::Neg(Box::new(Cond::Atom(atom.clone()))),
                others,
                result,
            )];
            output.extend(transform_step2(
                *inner,
                ResultFormula::Atom(atom),
                vec![],
                fresh,
            )?);
            Ok(output)
        }
        Cond::Prev(inner) if has_step2(&inner) => {
            let atom = Atom::new(
                fresh.name("prev"),
                vars_cond(&inner).into_iter().map(Term::Var).collect(),
            );
            let mut output = vec![rule_with_condition(
                Cond::Prev(Box::new(Cond::Atom(atom.clone()))),
                others,
                result,
            )];
            output.extend(transform_step2(
                *inner,
                ResultFormula::Atom(atom),
                vec![],
                fresh,
            )?);
            Ok(output)
        }
        other => Ok(vec![rule_with_condition(other, others, result)]),
    }
}

fn step3(
    rules: Vec<SourceRule>,
    pf: &BTreeSet<Name>,
    fresh: &mut Fresh,
) -> Result<Vec<SourceRule>, String> {
    rules
        .into_iter()
        .map(|rule| {
            let (conditions, result) = match rule {
                SourceRule::Fact(result) => (vec![], result),
                SourceRule::Rule(conditions, result) => (conditions, result),
            };
            let head = match result {
                ResultFormula::Atom(atom) => atom,
                ResultFormula::Reduction(name, mut args, body) => {
                    args.push(body);
                    Atom::new(name, args)
                }
                other => return Err(format!("future result survived step 1: {other:?}")),
            };
            let (head, mut generated) = expand_atom(head, pf, fresh);
            let mut expanded_conditions = Vec::new();
            for condition in conditions {
                let (condition, mut extras) = expand_cond_terms(condition, pf, fresh);
                expanded_conditions.push(condition);
                generated.append(&mut extras);
            }
            expanded_conditions.append(&mut generated);
            Ok(if expanded_conditions.is_empty() {
                SourceRule::Fact(ResultFormula::Atom(head))
            } else {
                SourceRule::Rule(expanded_conditions, ResultFormula::Atom(head))
            })
        })
        .collect()
}

fn step4(mut rules: Vec<SourceRule>, fresh: &mut Fresh) -> Result<Vec<SourceRule>, String> {
    for _ in 0..1000 {
        let mut changed = false;
        let mut next = Vec::new();
        for rule in rules {
            match rule {
                SourceRule::Rule(conditions, result) => {
                    let mut rewritten = Vec::new();
                    let mut extras = Vec::new();
                    for condition in conditions {
                        let (condition, extra, did_change) = step4_cond(condition, fresh);
                        rewritten.push(condition);
                        extras.extend(extra);
                        changed |= did_change;
                    }
                    next.push(SourceRule::Rule(rewritten, result));
                    next.extend(extras);
                }
                fact => next.push(fact),
            }
        }
        if !changed {
            return Ok(next);
        }
        rules = next;
    }
    Err("normalizer step 4 exceeded its iteration limit".into())
}

fn step4_cond(cond: Cond, fresh: &mut Fresh) -> (Cond, Vec<SourceRule>, bool) {
    match cond {
        Cond::Neg(inner) if !matches!(*inner, Cond::Atom(_)) => {
            let atom = Atom::new(
                fresh.name("neg"),
                vars_cond(&inner).into_iter().map(Term::Var).collect(),
            );
            (
                Cond::Neg(Box::new(Cond::Atom(atom.clone()))),
                vec![SourceRule::Rule(vec![*inner], ResultFormula::Atom(atom))],
                true,
            )
        }
        Cond::Prev(inner) => {
            let (rewritten, extras, changed) = step4_cond(*inner, fresh);
            (Cond::Prev(Box::new(rewritten)), extras, changed)
        }
        Cond::And(conditions) => {
            let mut rewritten = Vec::new();
            let mut extras = Vec::new();
            let mut changed = false;
            for condition in conditions {
                let (condition, mut extra, did_change) = step4_cond(condition, fresh);
                rewritten.push(condition);
                extras.append(&mut extra);
                changed |= did_change;
            }
            (Cond::And(rewritten), extras, changed)
        }
        other => (other, vec![], false),
    }
}

fn to_normal(rule: SourceRule) -> Result<NormalRule, String> {
    match rule {
        SourceRule::Fact(ResultFormula::Atom(head)) => Ok(NormalRule {
            conditions: vec![],
            head,
        }),
        SourceRule::Rule(conditions, ResultFormula::Atom(head)) => {
            let mut output = Vec::new();
            for condition in conditions {
                output.extend(distribute_previous(condition, 0)?);
            }
            Ok(NormalRule {
                conditions: output,
                head,
            })
        }
        other => Err(format!("non-normal rule after normalization: {other:?}")),
    }
}

fn distribute_previous(cond: Cond, depth: usize) -> Result<Vec<NormalCond>, String> {
    match cond {
        Cond::Prev(inner) => distribute_previous(*inner, depth + 1),
        Cond::And(conditions) => {
            let mut output = Vec::new();
            for condition in conditions {
                output.extend(distribute_previous(condition, depth)?);
            }
            Ok(output)
        }
        Cond::Atom(atom) => Ok(vec![NormalCond {
            depth,
            negated: false,
            atom,
        }]),
        Cond::Neg(inner) => match *inner {
            Cond::Atom(atom) => Ok(vec![NormalCond {
                depth,
                negated: true,
                atom,
            }]),
            other => Err(format!("non-atomic negation after step 4: {other:?}")),
        },
        other => Err(format!(
            "surface condition survived normalization: {other:?}"
        )),
    }
}

fn expand_cond_terms(cond: Cond, pf: &BTreeSet<Name>, fresh: &mut Fresh) -> (Cond, Vec<Cond>) {
    match cond {
        Cond::Atom(atom) => {
            let (atom, extras) = expand_atom(atom, pf, fresh);
            (Cond::Atom(atom), extras)
        }
        Cond::Neg(inner) => {
            let (c, e) = expand_cond_terms(*inner, pf, fresh);
            (Cond::Neg(Box::new(c)), e)
        }
        Cond::Prev(inner) => {
            let (c, e) = expand_cond_terms(*inner, pf, fresh);
            (Cond::Prev(Box::new(c)), e)
        }
        Cond::And(conditions) => {
            let mut output = Vec::new();
            let mut extras = Vec::new();
            for condition in conditions {
                let (c, mut e) = expand_cond_terms(condition, pf, fresh);
                output.push(c);
                extras.append(&mut e);
            }
            (Cond::And(output), extras)
        }
        other => (other, vec![]),
    }
}

fn expand_atom(atom: Atom, pf: &BTreeSet<Name>, fresh: &mut Fresh) -> (Atom, Vec<Cond>) {
    let mut terms = Vec::new();
    let mut extras = Vec::new();
    for term in atom.terms {
        let (t, mut e) = expand_term(term, 0, pf, fresh);
        terms.push(t);
        extras.append(&mut e);
    }
    (Atom::new(atom.name, terms), extras)
}

fn expand_term(
    term: Term,
    depth: usize,
    pf: &BTreeSet<Name>,
    fresh: &mut Fresh,
) -> (Term, Vec<Cond>) {
    match term {
        Term::Var(_) => (term, vec![]),
        Term::Prev(inner) => expand_term(*inner, depth + 1, pf, fresh),
        Term::Fun(name, args) => {
            let mut expanded = Vec::new();
            let mut extras = Vec::new();
            for arg in args {
                let (t, mut e) = expand_term(arg, depth, pf, fresh);
                expanded.push(t);
                extras.append(&mut e);
            }
            if pf.contains(&name) {
                let var_name = fresh.name("V");
                let var = Term::Var(var_name.clone());
                let mut relation_args = expanded;
                relation_args.push(var.clone());
                extras.push(nest_prev(depth, Cond::Atom(Atom::new(name, relation_args))));
                (var, extras)
            } else {
                (Term::Fun(name, expanded), extras)
            }
        }
    }
}

fn validate_term_previous(rules: &[SourceRule], pf: &BTreeSet<Name>) -> Result<(), String> {
    if rules
        .iter()
        .any(|rule| source_rule_terms(rule).iter().any(|t| invalid_prev(t, pf)))
    {
        Err("term-level @ requires a term containing a pattern function".into())
    } else {
        Ok(())
    }
}

fn invalid_prev(term: &Term, pf: &BTreeSet<Name>) -> bool {
    match term {
        Term::Var(_) => false,
        Term::Fun(_, args) => args.iter().any(|t| invalid_prev(t, pf)),
        Term::Prev(inner) => !contains_pf(inner, pf) || invalid_prev(inner, pf),
    }
}
fn contains_pf(term: &Term, pf: &BTreeSet<Name>) -> bool {
    match term {
        Term::Var(_) => false,
        Term::Fun(name, args) => pf.contains(name) || args.iter().any(|t| contains_pf(t, pf)),
        Term::Prev(inner) => contains_pf(inner, pf),
    }
}

fn has_step2(cond: &Cond) -> bool {
    match cond {
        Cond::HasBeen(_)
        | Cond::Once(_)
        | Cond::Since(_, _)
        | Cond::After(_, _)
        | Cond::For(_, _)
        | Cond::Eventually(_) => true,
        Cond::Neg(inner) | Cond::Prev(inner) => has_step2(inner),
        Cond::And(conditions) => conditions.iter().any(has_step2),
        Cond::Atom(_) => false,
    }
}

fn rule_with_aux(atom: Atom, mut others: Vec<Cond>, result: ResultFormula) -> SourceRule {
    others.insert(0, Cond::Atom(atom));
    SourceRule::Rule(others, result)
}
fn rule_with_condition(cond: Cond, mut others: Vec<Cond>, result: ResultFormula) -> SourceRule {
    others.insert(0, cond);
    SourceRule::Rule(others, result)
}
fn nest_prev(depth: usize, mut cond: Cond) -> Cond {
    for _ in 0..depth {
        cond = Cond::Prev(Box::new(cond));
    }
    cond
}
fn constant(name: &str) -> Term {
    Term::Fun(name.into(), vec![])
}
fn union(mut left: BTreeSet<Var>, right: BTreeSet<Var>) -> BTreeSet<Var> {
    left.extend(right);
    left
}
fn flatten_cond(cond: Cond) -> Vec<Cond> {
    match cond {
        Cond::And(cs) => cs.into_iter().flat_map(flatten_cond).collect(),
        c => vec![c],
    }
}
fn flatten_results(results: Vec<ResultFormula>) -> Vec<ResultFormula> {
    results
        .into_iter()
        .flat_map(|r| match r {
            ResultFormula::And(rs) => flatten_results(rs),
            x => vec![x],
        })
        .collect()
}

fn vars_cond(cond: &Cond) -> BTreeSet<Var> {
    match cond {
        Cond::Atom(atom) => atom.vars(),
        Cond::Neg(c)
        | Cond::Prev(c)
        | Cond::HasBeen(c)
        | Cond::Once(c)
        | Cond::For(c, _)
        | Cond::Eventually(c) => vars_cond(c),
        Cond::Since(a, b) | Cond::After(a, b) => union(vars_cond(a), vars_cond(b)),
        Cond::And(cs) => cs.iter().flat_map(vars_cond).collect(),
    }
}
fn vars_result(result: &ResultFormula) -> BTreeSet<Var> {
    match result {
        ResultFormula::Atom(atom) => atom.vars(),
        ResultFormula::Reduction(_, args, body) => {
            args.iter().chain([body]).flat_map(Term::vars).collect()
        }
        ResultFormula::Always(r) | ResultFormula::Next(r) => vars_result(r),
        ResultFormula::Until(r, c) | ResultFormula::AtNext(r, c) => {
            union(vars_result(r), vars_cond(c))
        }
        ResultFormula::And(rs) => rs.iter().flat_map(vars_result).collect(),
    }
}

fn reduction_names(rules: &[SourceRule]) -> BTreeSet<Name> {
    rules
        .iter()
        .flat_map(|rule| match rule {
            SourceRule::Fact(r) | SourceRule::Rule(_, r) => result_reductions(r),
        })
        .collect()
}
fn result_reductions(result: &ResultFormula) -> BTreeSet<Name> {
    match result {
        ResultFormula::Reduction(name, _, _) => [name.clone()].into_iter().collect(),
        ResultFormula::Always(r) | ResultFormula::Next(r) => result_reductions(r),
        ResultFormula::Until(r, _) | ResultFormula::AtNext(r, _) => result_reductions(r),
        ResultFormula::And(rs) => rs.iter().flat_map(result_reductions).collect(),
        ResultFormula::Atom(_) => BTreeSet::new(),
    }
}

fn identifiers(rules: &[SourceRule]) -> BTreeSet<String> {
    format!("{rules:?}")
        .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .filter(|s| !s.is_empty())
        .map(str::to_owned)
        .collect()
}

fn source_rule_terms(rule: &SourceRule) -> Vec<&Term> {
    let mut terms = Vec::new();
    match rule {
        SourceRule::Fact(result) => collect_result_terms(result, &mut terms),
        SourceRule::Rule(conditions, result) => {
            for condition in conditions {
                collect_cond_terms(condition, &mut terms);
            }
            collect_result_terms(result, &mut terms);
        }
    }
    terms
}
fn collect_atom_terms<'a>(atom: &'a Atom, out: &mut Vec<&'a Term>) {
    out.extend(atom.terms.iter());
}
fn collect_cond_terms<'a>(cond: &'a Cond, out: &mut Vec<&'a Term>) {
    match cond {
        Cond::Atom(atom) => collect_atom_terms(atom, out),
        Cond::Neg(c)
        | Cond::Prev(c)
        | Cond::HasBeen(c)
        | Cond::Once(c)
        | Cond::For(c, _)
        | Cond::Eventually(c) => collect_cond_terms(c, out),
        Cond::Since(a, b) | Cond::After(a, b) => {
            collect_cond_terms(a, out);
            collect_cond_terms(b, out);
        }
        Cond::And(cs) => {
            for c in cs {
                collect_cond_terms(c, out);
            }
        }
    }
}
fn collect_result_terms<'a>(result: &'a ResultFormula, out: &mut Vec<&'a Term>) {
    match result {
        ResultFormula::Atom(atom) => collect_atom_terms(atom, out),
        ResultFormula::Reduction(_, args, body) => {
            out.extend(args.iter());
            out.push(body);
        }
        ResultFormula::Always(r) | ResultFormula::Next(r) => collect_result_terms(r, out),
        ResultFormula::Until(r, c) | ResultFormula::AtNext(r, c) => {
            collect_result_terms(r, out);
            collect_cond_terms(c, out);
        }
        ResultFormula::And(rs) => {
            for r in rs {
                collect_result_terms(r, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_program;

    fn normalized(source: &str) -> NormalizedProgram {
        normalize(parse_program(source).unwrap()).unwrap()
    }

    fn atom(name: &str) -> Atom {
        Atom::new(name, vec![])
    }

    #[test]
    fn normalizes_simple_facts() {
        assert_eq!(
            normalized("p.").rules,
            vec![NormalRule {
                conditions: vec![],
                head: atom("p"),
            }]
        );
    }

    #[test]
    fn normalizes_simple_rules() {
        assert_eq!(
            normalized("a => b.").rules,
            vec![NormalRule {
                conditions: vec![NormalCond {
                    depth: 0,
                    negated: false,
                    atom: atom("a"),
                }],
                head: atom("b"),
            }]
        );
    }

    #[test]
    fn unconditional_always_reduces_to_its_bare_result() {
        assert_eq!(
            normalized("always p.").rules,
            vec![NormalRule {
                conditions: vec![],
                head: atom("p"),
            }]
        );
    }

    #[test]
    fn conditional_always_auxiliary_uses_only_result_variables() {
        let program = normalized("start(X) => always running.");
        let auxiliary_heads: Vec<_> = program
            .rules
            .iter()
            .filter(|rule| program.auxiliary_predicates.contains(&rule.head.name))
            .map(|rule| &rule.head.terms)
            .collect();
        assert!(!auxiliary_heads.is_empty());
        assert!(auxiliary_heads.iter().all(|terms| terms.is_empty()));
    }

    #[test]
    fn generated_predicates_do_not_collide_with_source_names() {
        let program = normalized("always_aux0. start => always running.");
        assert!(!program.auxiliary_predicates.contains("always_aux0"));
        assert!(program
            .auxiliary_predicates
            .iter()
            .any(|name| name.starts_with("always_aux")));
    }

    #[test]
    fn unconditional_atnext_reduces_to_trigger_rule() {
        assert_eq!(
            normalized("ready atnext trigger.").rules,
            vec![NormalRule {
                conditions: vec![NormalCond {
                    depth: 0,
                    negated: false,
                    atom: atom("trigger"),
                }],
                head: atom("ready"),
            }]
        );
    }

    #[test]
    fn until_recurrence_uses_previous_negated_trigger() {
        let program = normalized("start => running until stop.");
        assert!(program.rules.iter().any(|rule| {
            program.auxiliary_predicates.contains(&rule.head.name)
                && rule.conditions.iter().any(|condition| {
                    condition.depth == 1 && condition.negated && condition.atom == atom("stop")
                })
        }));
    }

    #[test]
    fn for_expands_to_every_required_previous_depth() {
        let program = normalized("a for 3 => b.");
        let rule = program
            .rules
            .iter()
            .find(|rule| rule.head == atom("b"))
            .unwrap();
        let depths: BTreeSet<_> = rule
            .conditions
            .iter()
            .map(|condition| condition.depth)
            .collect();
        assert_eq!(depths, [0, 1, 2].into_iter().collect());
    }

    #[test]
    fn negation_becomes_a_negated_normal_condition() {
        let program = normalized("~a => b.");
        assert!(program.rules.iter().any(|rule| rule
            .conditions
            .iter()
            .any(|condition| condition.negated && condition.atom == atom("a"))));
    }

    #[test]
    fn pattern_function_relation_has_an_extra_output_argument() {
        let program = normalized("wrap(X) -> box(X).");
        let rule = program
            .rules
            .iter()
            .find(|rule| rule.head.name == "wrap")
            .unwrap();
        assert_eq!(rule.head.terms.len(), 2);
        assert!(program.pattern_functions.contains("wrap"));
    }

    #[test]
    fn normalizes_temporal_operators_exposed_by_nested_conjunctions() {
        assert!(!normalized("#(a /\\ (b since c)) => result.")
            .rules
            .is_empty());
    }

    #[test]
    fn pushes_negation_through_exposed_conjunctions() {
        assert!(!normalized("#(~(a /\\ b) /\\ c) => result.")
            .rules
            .is_empty());
    }

    #[test]
    fn term_previous_moves_only_the_pattern_function_condition() {
        let program = normalized("lookup(key) -> value. present(@lookup(key)) => found.");
        let found = program
            .rules
            .iter()
            .find(|rule| rule.head == atom("found"))
            .unwrap();
        assert!(found
            .conditions
            .iter()
            .any(|condition| { condition.depth == 0 && condition.atom.name == "present" }));
        assert!(found
            .conditions
            .iter()
            .any(|condition| { condition.depth == 1 && condition.atom.name == "lookup" }));
    }

    #[test]
    fn strict_after_uses_two_latches() {
        let normalized = normalize(parse_program("a after b => result.").unwrap()).unwrap();
        assert_eq!(normalized.rules.len(), 5);
    }

    #[test]
    fn rejects_plain_previous_term() {
        assert!(normalize(parse_program("p(@X).").unwrap()).is_err());
    }

    #[test]
    fn records_generated_predicates_without_hiding_source_aux_names() {
        let normalized =
            normalize(parse_program("user_aux0. trigger => next generated.").unwrap()).unwrap();
        assert_eq!(
            normalized.auxiliary_predicates,
            ["next_aux1".to_string()].into_iter().collect()
        );
    }

    #[test]
    fn rejects_inconsistent_source_signatures_and_builtin_results() {
        for source in [
            "p. p(a).",
            "value(box). value(box(a)).",
            "choose(X) -> X. choose(X,Y) -> X.",
            "lookup(X) -> X. lookup(a).",
            "at(99).",
            "at(0,1) => impossible.",
            "X is div(1) => impossible(X).",
        ] {
            assert!(
                normalize(parse_program(source).unwrap()).is_err(),
                "{source}"
            );
        }
    }

    #[test]
    fn keeps_predicate_and_constructor_namespaces_distinct() {
        normalize(parse_program("tag(tag).").unwrap()).unwrap();
    }
}
