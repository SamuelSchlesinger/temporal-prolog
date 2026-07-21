use crate::ast::*;
use num_bigint::{BigInt, Sign};
use std::collections::{BTreeMap, BTreeSet};

const FIXPOINT_LIMIT: usize = 10_000;
const MODEL_CANDIDATE_LIMIT: usize = 20;
const BC_DEPTH_LIMIT: usize = 100;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Interpreter {
    pub program: NormalizedProgram,
    pub worlds: Vec<World>,
    pub assertions: World,
}

impl Interpreter {
    pub fn new(program: NormalizedProgram) -> Self {
        Self {
            program,
            worlds: Vec::new(),
            assertions: World::new(),
        }
    }

    pub fn assert(&mut self, atom: Atom) -> Result<(), String> {
        validate_assertion_namespace(&self.program, &atom)?;
        validate_runtime_signatures(&self.program, &self.worlds, &self.assertions, Some(&atom))?;
        self.assertions.insert(atom);
        Ok(())
    }

    pub fn world(&self) -> Option<&World> {
        self.worlds.last()
    }

    /// Advance using a canonical member of the minimal-model set.
    pub fn step(&mut self) -> Result<(), String> {
        let mut branches = self.step_all()?;
        let selected = branches
            .drain(..)
            .next()
            .ok_or_else(|| "world computation returned no model".to_string())?;
        *self = selected;
        Ok(())
    }

    /// Return one interpreter branch for every minimal current world.
    pub fn step_all(&self) -> Result<Vec<Self>, String> {
        validate_runtime_state(self)?;
        validate_profile(&self.program)?;
        let world_number = self.worlds.len();
        let (pf_rules, forward_rules) = partition_rules(&self.program);
        let fixed = external_facts(world_number)
            .union(&self.assertions)
            .cloned()
            .collect::<World>();
        let worlds = if stratify(&forward_rules).is_ok() {
            vec![compute_stratified(
                &self.program.pattern_functions,
                &pf_rules,
                &forward_rules,
                &self.worlds,
                world_number,
                fixed,
            )?]
        } else {
            compute_general(
                &self.program.pattern_functions,
                &pf_rules,
                &forward_rules,
                &self.worlds,
                world_number,
                fixed,
            )?
        };
        Ok(worlds
            .into_iter()
            .map(|world| {
                let mut next = self.clone();
                next.worlds.push(world);
                next.assertions.clear();
                next
            })
            .collect())
    }

    /// Force the finite general evaluator for differential testing.
    pub fn step_general_all(&self) -> Result<Vec<Self>, String> {
        validate_runtime_state(self)?;
        validate_profile(&self.program)?;
        let n = self.worlds.len();
        let (pf, forward) = partition_rules(&self.program);
        let fixed = external_facts(n).union(&self.assertions).cloned().collect();
        Ok(compute_general(
            &self.program.pattern_functions,
            &pf,
            &forward,
            &self.worlds,
            n,
            fixed,
        )?
        .into_iter()
        .map(|world| {
            let mut next = self.clone();
            next.worlds.push(world);
            next.assertions.clear();
            next
        })
        .collect())
    }

    pub fn query(&self, atom: &Atom) -> Result<Vec<Subst>, String> {
        if self.program.auxiliary_predicates.contains(&atom.name) {
            return Err("generated predicates cannot be queried".into());
        }
        validate_runtime_signatures(&self.program, &self.worlds, &self.assertions, Some(atom))?;
        let (pf_rules, _) = partition_rules(&self.program);
        let current = self.world().cloned().unwrap_or_default();
        let n = self.worlds.len().saturating_sub(1);
        satisfy_positive(
            &self.program.pattern_functions,
            &pf_rules,
            atom,
            &current,
            &self.worlds,
            n,
        )
    }
}

fn validate_runtime_state(state: &Interpreter) -> Result<(), String> {
    for atom in &state.assertions {
        validate_assertion_namespace(&state.program, atom)?;
    }
    validate_runtime_signatures(&state.program, &state.worlds, &state.assertions, None)
}

fn validate_assertion_namespace(program: &NormalizedProgram, atom: &Atom) -> Result<(), String> {
    if !atom.ground() {
        return Err("assertions must be ground".into());
    }
    if is_external_atom(atom) {
        return Err("built-in external predicates cannot be asserted".into());
    }
    if program.pattern_functions.contains(&atom.name) {
        return Err("pattern-function relations cannot be asserted".into());
    }
    if program.auxiliary_predicates.contains(&atom.name) {
        return Err("generated predicates cannot be asserted".into());
    }
    Ok(())
}

#[derive(Default)]
struct RuntimeSignatures {
    predicates: BTreeMap<Name, usize>,
    constructors: BTreeMap<Name, usize>,
}

fn validate_runtime_signatures(
    program: &NormalizedProgram,
    worlds: &[World],
    assertions: &World,
    extra: Option<&Atom>,
) -> Result<(), String> {
    let mut signatures = RuntimeSignatures::default();
    for rule in &program.rules {
        validate_runtime_atom(&mut signatures, &rule.head)?;
        for condition in &rule.conditions {
            validate_runtime_atom(&mut signatures, &condition.atom)?;
        }
    }
    for atom in worlds
        .iter()
        .flat_map(|world| world.iter())
        .chain(assertions)
        .chain(extra)
    {
        validate_runtime_atom(&mut signatures, atom)?;
    }
    Ok(())
}

fn validate_runtime_atom(signatures: &mut RuntimeSignatures, atom: &Atom) -> Result<(), String> {
    if let Some(expected) = external_predicate_arity(&atom.name) {
        if atom.terms.len() != expected {
            return Err(format!(
                "external predicate {:?} expects arity {expected}, found {}",
                atom.name,
                atom.terms.len()
            ));
        }
    } else {
        remember_runtime_signature(
            &mut signatures.predicates,
            "predicate",
            &atom.name,
            atom.terms.len(),
        )?;
    }
    for term in &atom.terms {
        validate_runtime_term(signatures, term)?;
    }
    Ok(())
}

fn validate_runtime_term(signatures: &mut RuntimeSignatures, term: &Term) -> Result<(), String> {
    match term {
        Term::Var(_) => Ok(()),
        Term::Prev(_) => Err("term-level @ is not valid in runtime atoms".into()),
        Term::Fun(name, terms) => {
            if let Some(expected) = arithmetic_function_arity(name) {
                if terms.len() != expected {
                    return Err(format!(
                        "arithmetic operator {name:?} expects arity {expected}, found {}",
                        terms.len()
                    ));
                }
            } else {
                remember_runtime_signature(
                    &mut signatures.constructors,
                    "constructor",
                    name,
                    terms.len(),
                )?;
            }
            for term in terms {
                validate_runtime_term(signatures, term)?;
            }
            Ok(())
        }
    }
}

fn remember_runtime_signature(
    signatures: &mut BTreeMap<Name, usize>,
    kind: &str,
    name: &str,
    arity: usize,
) -> Result<(), String> {
    match signatures.get(name) {
        None => {
            signatures.insert(name.to_string(), arity);
            Ok(())
        }
        Some(expected) if *expected == arity => Ok(()),
        Some(expected) => Err(format!(
            "{kind} {name:?} has inconsistent arity: expected {expected}, found {arity}"
        )),
    }
}

fn partition_rules(program: &NormalizedProgram) -> (Vec<NormalRule>, Vec<NormalRule>) {
    program
        .rules
        .iter()
        .cloned()
        .partition(|rule| program.pattern_functions.contains(&rule.head.name))
}

fn external_facts(n: usize) -> World {
    [
        Atom::new("at", vec![Term::Fun(n.to_string(), vec![])]),
        Atom::new("true", vec![]),
    ]
    .into_iter()
    .collect()
}

fn compute_stratified(
    pf_names: &BTreeSet<Name>,
    pf_rules: &[NormalRule],
    rules: &[NormalRule],
    history: &[World],
    n: usize,
    mut world: World,
) -> Result<World, String> {
    for stratum in stratify(rules)? {
        world = fixed_point(pf_names, pf_rules, &stratum, history, n, world)?;
    }
    Ok(world)
}

fn fixed_point(
    pf_names: &BTreeSet<Name>,
    pf_rules: &[NormalRule],
    rules: &[NormalRule],
    history: &[World],
    n: usize,
    mut world: World,
) -> Result<World, String> {
    for _ in 0..FIXPOINT_LIMIT {
        let before = world.len();
        for rule in rules {
            world.extend(derive_rule(pf_names, pf_rules, rule, history, n, &world)?);
        }
        if world.len() == before {
            return Ok(world);
        }
    }
    Err(format!(
        "fixed-point computation exceeded {FIXPOINT_LIMIT} iterations at world {n}"
    ))
}

fn compute_general(
    pf_names: &BTreeSet<Name>,
    pf_rules: &[NormalRule],
    rules: &[NormalRule],
    history: &[World],
    n: usize,
    fixed: World,
) -> Result<Vec<World>, String> {
    let relaxed: Vec<_> = rules
        .iter()
        .cloned()
        .map(|mut rule| {
            rule.conditions.retain(|c| !(c.depth == 0 && c.negated));
            rule
        })
        .collect();
    let candidate_world = candidate_fixed_point(
        pf_names,
        pf_rules,
        rules,
        &relaxed,
        history,
        n,
        fixed.clone(),
    )?;
    let candidates: Vec<_> = candidate_world.difference(&fixed).cloned().collect();
    if candidates.len() > MODEL_CANDIDATE_LIMIT {
        return Err(format!(
            "minimal-model candidate base has {} atoms, limit is {MODEL_CANDIDATE_LIMIT}",
            candidates.len()
        ));
    }
    let mut models = Vec::new();
    for mask in 0u64..(1u64 << candidates.len()) {
        let mut proposed = fixed.clone();
        for (index, atom) in candidates.iter().enumerate() {
            if mask & (1 << index) != 0 {
                proposed.insert(atom.clone());
            }
        }
        if is_model(pf_names, pf_rules, rules, history, n, &proposed)? {
            models.push(proposed);
        }
    }
    if models.is_empty() {
        return Err("program has no model for the current external interpretation".into());
    }
    let components = ordered_sccs(rules);
    let minimal = models
        .iter()
        .filter(|model| {
            !models
                .iter()
                .any(|other| other != *model && model_smaller(&components, other, model))
        })
        .cloned()
        .collect();
    Ok(minimal)
}

fn candidate_fixed_point(
    pf_names: &BTreeSet<Name>,
    pf_rules: &[NormalRule],
    original: &[NormalRule],
    relaxed: &[NormalRule],
    history: &[World],
    n: usize,
    mut world: World,
) -> Result<World, String> {
    let internal_names: BTreeSet<_> = original.iter().map(|rule| rule.head.name.clone()).collect();
    for _ in 0..FIXPOINT_LIMIT {
        let before = world.len();
        for rule in relaxed {
            world.extend(derive_rule(pf_names, pf_rules, rule, history, n, &world)?);
        }
        // A classical model may contain an unsupported internal atom solely
        // to block a negative antecedent. Ground all such atoms under the
        // relaxed closure so enumeration does not impose stable semantics.
        for rule in original {
            let relaxed_conditions: Vec<_> = rule
                .conditions
                .iter()
                .filter(|condition| !(condition.depth == 0 && condition.negated))
                .cloned()
                .collect();
            let substitutions =
                find_substitutions(pf_names, pf_rules, &relaxed_conditions, history, n, &world)?;
            for condition in rule.conditions.iter().filter(|condition| {
                condition.depth == 0
                    && condition.negated
                    && internal_names.contains(&condition.atom.name)
            }) {
                for subst in &substitutions {
                    let atom = condition.atom.apply(subst);
                    if atom.ground() {
                        world.insert(atom);
                    }
                }
            }
        }
        if world.len() == before {
            return Ok(world);
        }
    }
    Err(format!(
        "candidate generation exceeded {FIXPOINT_LIMIT} iterations at world {n}"
    ))
}

fn is_model(
    pf_names: &BTreeSet<Name>,
    pf_rules: &[NormalRule],
    rules: &[NormalRule],
    history: &[World],
    n: usize,
    world: &World,
) -> Result<bool, String> {
    for rule in rules {
        if derive_rule(pf_names, pf_rules, rule, history, n, world)?
            .iter()
            .any(|atom| !world.contains(atom))
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn derive_rule(
    pf_names: &BTreeSet<Name>,
    pf_rules: &[NormalRule],
    rule: &NormalRule,
    history: &[World],
    n: usize,
    current: &World,
) -> Result<Vec<Atom>, String> {
    Ok(
        find_substitutions(pf_names, pf_rules, &rule.conditions, history, n, current)?
            .into_iter()
            .map(|subst| rule.head.apply(&subst))
            .filter(Atom::ground)
            .collect(),
    )
}

fn find_substitutions(
    pf_names: &BTreeSet<Name>,
    pf_rules: &[NormalRule],
    conditions: &[NormalCond],
    history: &[World],
    n: usize,
    current: &World,
) -> Result<Vec<Subst>, String> {
    let mut ordered = conditions.to_vec();
    ordered.sort_by_key(|condition| condition.negated);
    solve_conditions(pf_names, pf_rules, &ordered, history, n, current)
}

fn solve_conditions(
    pf_names: &BTreeSet<Name>,
    pf_rules: &[NormalRule],
    conditions: &[NormalCond],
    history: &[World],
    n: usize,
    current: &World,
) -> Result<Vec<Subst>, String> {
    if conditions.is_empty() {
        return Ok(vec![Subst::new()]);
    }
    let first = satisfy_condition(pf_names, pf_rules, &conditions[0], history, n, current)?;
    let mut output = Vec::new();
    for subst in first {
        let rest: Vec<_> = conditions[1..]
            .iter()
            .map(|condition| NormalCond {
                depth: condition.depth,
                negated: condition.negated,
                atom: condition.atom.apply(&subst),
            })
            .collect();
        for tail in solve_conditions(pf_names, pf_rules, &rest, history, n, current)? {
            output.push(compose(&tail, &subst));
        }
    }
    Ok(output)
}

fn satisfy_condition(
    pf_names: &BTreeSet<Name>,
    pf_rules: &[NormalRule],
    condition: &NormalCond,
    history: &[World],
    n: usize,
    current: &World,
) -> Result<Vec<Subst>, String> {
    let Some((target, target_n)) = lookup_world(condition.depth, history, n, current) else {
        return Ok(vec![]);
    };
    if condition.negated {
        let positive = satisfy_positive(
            pf_names,
            pf_rules,
            &condition.atom,
            target,
            history,
            target_n,
        )?;
        Ok(if positive.is_empty() {
            vec![Subst::new()]
        } else {
            vec![]
        })
    } else {
        satisfy_positive(
            pf_names,
            pf_rules,
            &condition.atom,
            target,
            history,
            target_n,
        )
    }
}

fn lookup_world<'a>(
    depth: usize,
    history: &'a [World],
    n: usize,
    current: &'a World,
) -> Option<(&'a World, usize)> {
    if depth == 0 {
        Some((current, n))
    } else if depth <= n {
        Some((&history[n - depth], n - depth))
    } else {
        None
    }
}

fn satisfy_positive(
    pf_names: &BTreeSet<Name>,
    pf_rules: &[NormalRule],
    atom: &Atom,
    world: &World,
    history: &[World],
    n: usize,
) -> Result<Vec<Subst>, String> {
    if let Some(result) = evaluate_external(atom, n) {
        return Ok(result);
    }
    if pf_names.contains(&atom.name) {
        solve_backward(pf_names, pf_rules, atom, world, history, n, 0)
    } else {
        Ok(match_world(atom, world))
    }
}

fn match_world(pattern: &Atom, world: &World) -> Vec<Subst> {
    world
        .iter()
        .filter(|atom| atom.name == pattern.name)
        .filter_map(|atom| unify_atom(pattern, atom))
        .collect()
}

/// Return whether a pattern matches a stored world fact. Unlike
/// `Interpreter::query`, this never invokes pattern-function relations.
pub fn world_matches(pattern: &Atom, world: &World) -> bool {
    !match_world(pattern, world).is_empty()
}

fn evaluate_external(atom: &Atom, n: usize) -> Option<Vec<Subst>> {
    match (atom.name.as_str(), atom.terms.as_slice()) {
        ("true", []) => Some(vec![Subst::new()]),
        ("false", []) => Some(vec![]),
        ("=", [left, right]) => Some(unify_terms(left, right).into_iter().collect()),
        ("at", [Term::Var(var)]) => Some(vec![[(var.clone(), Term::Fun(n.to_string(), vec![]))]
            .into_iter()
            .collect()]),
        ("at", [Term::Fun(value, args)]) if args.is_empty() => Some(if value == &n.to_string() {
            vec![Subst::new()]
        } else {
            vec![]
        }),
        ("is", [result, expression]) => Some(match eval_arith(expression) {
            Some(value) => unify_terms(result, &Term::Fun(value.to_string(), vec![]))
                .into_iter()
                .collect(),
            None => vec![],
        }),
        (op @ (">" | "<" | ">=" | "<="), [left, right]) => {
            match (eval_arith(left), eval_arith(right)) {
                (Some(a), Some(b)) => Some(
                    if match op {
                        ">" => a > b,
                        "<" => a < b,
                        ">=" => a >= b,
                        _ => a <= b,
                    } {
                        vec![Subst::new()]
                    } else {
                        vec![]
                    },
                ),
                _ => Some(vec![]),
            }
        }
        _ => None,
    }
}

fn eval_arith(term: &Term) -> Option<BigInt> {
    match term {
        Term::Fun(value, args) if args.is_empty() => value.parse().ok(),
        Term::Fun(op, args) if args.len() == 2 => {
            let left = eval_arith(&args[0])?;
            let right = eval_arith(&args[1])?;
            match op.as_str() {
                "+" => Some(left + right),
                "-" => Some(left - right),
                "*" => Some(left * right),
                "div" => floor_div_mod(left, right).map(|(quotient, _)| quotient),
                "mod" => floor_div_mod(left, right).map(|(_, remainder)| remainder),
                _ => None,
            }
        }
        _ => None,
    }
}

fn floor_div_mod(left: BigInt, right: BigInt) -> Option<(BigInt, BigInt)> {
    if right.sign() == Sign::NoSign {
        return None;
    }
    let mut quotient = &left / &right;
    let mut remainder = &left % &right;
    if remainder.sign() != Sign::NoSign && remainder.sign() != right.sign() {
        quotient -= 1;
        remainder += &right;
    }
    Some((quotient, remainder))
}

fn solve_backward(
    pf_names: &BTreeSet<Name>,
    rules: &[NormalRule],
    goal: &Atom,
    world: &World,
    history: &[World],
    n: usize,
    depth: usize,
) -> Result<Vec<Subst>, String> {
    if depth >= BC_DEPTH_LIMIT {
        return Err(format!(
            "pattern-function recursion exceeded depth {BC_DEPTH_LIMIT}"
        ));
    }
    let mut output = Vec::new();
    for (index, rule) in rules.iter().enumerate() {
        let renamed = rename_rule(rule, depth, index);
        if let Some(initial) = unify_atom(goal, &renamed.head) {
            let conditions: Vec<_> = renamed
                .conditions
                .iter()
                .map(|condition| NormalCond {
                    depth: condition.depth,
                    negated: condition.negated,
                    atom: condition.atom.apply(&initial),
                })
                .collect();
            for tail in solve_bc_conditions(pf_names, rules, &conditions, world, history, n, depth)?
            {
                output.push(compose(&tail, &initial));
            }
        }
    }
    Ok(output)
}

fn solve_bc_conditions(
    pf_names: &BTreeSet<Name>,
    rules: &[NormalRule],
    conditions: &[NormalCond],
    current: &World,
    history: &[World],
    n: usize,
    depth: usize,
) -> Result<Vec<Subst>, String> {
    if conditions.is_empty() {
        return Ok(vec![Subst::new()]);
    }
    let condition = &conditions[0];
    let Some((target, target_n)) = lookup_world(condition.depth, history, n, current) else {
        return Ok(vec![]);
    };
    let positive = |atom: &Atom| -> Result<Vec<Subst>, String> {
        if pf_names.contains(&atom.name) {
            solve_backward(pf_names, rules, atom, target, history, target_n, depth + 1)
        } else if let Some(result) = evaluate_external(atom, target_n) {
            Ok(result)
        } else {
            Ok(match_world(atom, target))
        }
    };
    let first = if condition.negated {
        if positive(&condition.atom)?.is_empty() {
            vec![Subst::new()]
        } else {
            vec![]
        }
    } else {
        positive(&condition.atom)?
    };
    let mut output = Vec::new();
    for subst in first {
        let rest: Vec<_> = conditions[1..]
            .iter()
            .map(|c| NormalCond {
                depth: c.depth,
                negated: c.negated,
                atom: c.atom.apply(&subst),
            })
            .collect();
        for tail in solve_bc_conditions(pf_names, rules, &rest, current, history, n, depth)? {
            output.push(compose(&tail, &subst));
        }
    }
    Ok(output)
}

fn rename_rule(rule: &NormalRule, depth: usize, index: usize) -> NormalRule {
    let variables: BTreeSet<_> = rule
        .head
        .vars()
        .into_iter()
        .chain(
            rule.conditions
                .iter()
                .flat_map(|condition| condition.atom.vars()),
        )
        .collect();
    let subst: Subst = variables
        .into_iter()
        .map(|var| {
            let renamed = Term::Var(format!("_bc{depth}_{index}_{var}"));
            (var, renamed)
        })
        .collect();
    NormalRule {
        conditions: rule
            .conditions
            .iter()
            .map(|c| NormalCond {
                depth: c.depth,
                negated: c.negated,
                atom: c.atom.apply(&subst),
            })
            .collect(),
        head: rule.head.apply(&subst),
    }
}

fn unify_atom(left: &Atom, right: &Atom) -> Option<Subst> {
    if left.name != right.name || left.terms.len() != right.terms.len() {
        return None;
    }
    unify_term_lists(&left.terms, &right.terms)
}
fn unify_term_lists(left: &[Term], right: &[Term]) -> Option<Subst> {
    let mut subst = Subst::new();
    for (a, b) in left.iter().zip(right) {
        let next = unify_terms(&a.apply(&subst), &b.apply(&subst))?;
        subst = compose(&next, &subst);
    }
    Some(subst)
}
fn unify_terms(left: &Term, right: &Term) -> Option<Subst> {
    match (left, right) {
        (Term::Var(a), Term::Var(b)) if a == b => Some(Subst::new()),
        (Term::Var(var), term) | (term, Term::Var(var)) => {
            if term.vars().contains(var) {
                None
            } else {
                Some([(var.clone(), term.clone())].into_iter().collect())
            }
        }
        (Term::Fun(a, xs), Term::Fun(b, ys)) if a == b && xs.len() == ys.len() => {
            unify_term_lists(xs, ys)
        }
        (Term::Prev(a), Term::Prev(b)) => unify_terms(a, b),
        _ => None,
    }
}
fn compose(after: &Subst, before: &Subst) -> Subst {
    let mut output: Subst = before
        .iter()
        .map(|(var, term)| (var.clone(), term.apply(after)))
        .collect();
    output.extend(after.clone());
    output
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DepKind {
    Positive,
    Negative,
}
fn dependencies(rules: &[NormalRule]) -> BTreeMap<Name, Vec<(Name, DepKind)>> {
    let mut output: BTreeMap<Name, Vec<(Name, DepKind)>> = BTreeMap::new();
    for rule in rules {
        for condition in &rule.conditions {
            if condition.depth == 0 {
                output.entry(rule.head.name.clone()).or_default().push((
                    condition.atom.name.clone(),
                    if condition.negated {
                        DepKind::Negative
                    } else {
                        DepKind::Positive
                    },
                ));
            }
        }
    }
    output
}

fn stratify(rules: &[NormalRule]) -> Result<Vec<Vec<NormalRule>>, String> {
    let deps = dependencies(rules);
    let heads: BTreeSet<_> = rules.iter().map(|r| r.head.name.clone()).collect();
    let mut strata: BTreeMap<_, usize> = heads.iter().map(|p| (p.clone(), 0)).collect();
    for iteration in 0..=heads.len() {
        let previous = strata.clone();
        for predicate in &heads {
            let mut needed = *previous.get(predicate).unwrap_or(&0);
            for (dependency, kind) in deps.get(predicate).into_iter().flatten() {
                needed = needed.max(
                    previous.get(dependency).copied().unwrap_or(0)
                        + usize::from(*kind == DepKind::Negative),
                );
            }
            strata.insert(predicate.clone(), needed);
        }
        if strata == previous {
            let max = strata.values().copied().max().unwrap_or(0);
            return Ok((0..=max)
                .map(|level| {
                    rules
                        .iter()
                        .filter(|r| strata.get(&r.head.name).copied().unwrap_or(0) == level)
                        .cloned()
                        .collect()
                })
                .collect());
        }
        if iteration == heads.len() {
            break;
        }
    }
    Err("program contains a current-world negative dependency cycle".into())
}

fn ordered_sccs(rules: &[NormalRule]) -> Vec<BTreeSet<Name>> {
    let heads: BTreeSet<_> = rules.iter().map(|r| r.head.name.clone()).collect();
    let deps = dependencies(rules);
    let reachable = |start: &Name| {
        let mut seen = BTreeSet::new();
        let mut work = vec![start.clone()];
        while let Some(node) = work.pop() {
            if seen.insert(node.clone()) {
                for (next, _) in deps.get(&node).into_iter().flatten() {
                    if heads.contains(next) {
                        work.push(next.clone());
                    }
                }
            }
        }
        seen
    };
    let reach: BTreeMap<_, _> = heads.iter().map(|p| (p.clone(), reachable(p))).collect();
    let mut remaining = heads.clone();
    let mut components = Vec::new();
    while let Some(first) = remaining.iter().next().cloned() {
        let component: BTreeSet<_> = remaining
            .iter()
            .filter(|other| reach[&first].contains(*other) && reach[*other].contains(&first))
            .cloned()
            .collect();
        for p in &component {
            remaining.remove(p);
        }
        components.push(component);
    }
    let mut ordered = Vec::new();
    while !components.is_empty() {
        let ready: Vec<_> = components
            .iter()
            .filter(|component| {
                !component.iter().any(|p| {
                    deps.get(p).into_iter().flatten().any(|(q, _)| {
                        components
                            .iter()
                            .any(|target| target != *component && target.contains(q))
                    })
                })
            })
            .cloned()
            .collect();
        if ready.is_empty() {
            break;
        }
        for component in &ready {
            if let Some(index) = components.iter().position(|c| c == component) {
                components.remove(index);
            }
            ordered.push(component.clone());
        }
    }
    ordered.extend(components);
    ordered
}

fn model_smaller(components: &[BTreeSet<Name>], left: &World, right: &World) -> bool {
    for component in components {
        let l: BTreeSet<_> = left
            .iter()
            .filter(|a| component.contains(&a.name))
            .collect();
        let r: BTreeSet<_> = right
            .iter()
            .filter(|a| component.contains(&a.name))
            .collect();
        if l != r {
            return l.is_subset(&r) && l.len() < r.len();
        }
    }
    false
}

fn validate_profile(program: &NormalizedProgram) -> Result<(), String> {
    for rule in program
        .rules
        .iter()
        .filter(|r| !program.pattern_functions.contains(&r.head.name))
    {
        let positives: Vec<_> = rule.conditions.iter().filter(|c| !c.negated).collect();
        let mut bound = BTreeSet::new();
        loop {
            let before = bound.clone();
            for condition in &positives {
                bind_from_atom(&condition.atom, &mut bound);
            }
            if bound == before {
                break;
            }
        }
        let observed: BTreeSet<_> = rule
            .head
            .vars()
            .into_iter()
            .chain(
                rule.conditions
                    .iter()
                    .filter(|c| c.negated)
                    .flat_map(|c| c.atom.vars()),
            )
            .collect();
        let unsafe_vars: Vec<_> = observed.difference(&bound).cloned().collect();
        if !unsafe_vars.is_empty() {
            return Err(format!(
                "rule is not range restricted; ungrounded variables: {unsafe_vars:?}"
            ));
        }
    }
    Ok(())
}

fn bind_from_atom(atom: &Atom, bound: &mut BTreeSet<Var>) {
    match (atom.name.as_str(), atom.terms.as_slice()) {
        ("true" | "false" | ">" | "<" | ">=" | "<=", _) => {}
        ("=", [left, right]) => {
            let left_vars = left.vars();
            let right_vars = right.vars();
            if left_vars.is_subset(bound) {
                bound.extend(right_vars.clone());
            }
            if right_vars.is_subset(bound) {
                bound.extend(left_vars);
            }
        }
        ("is", [result, expression]) if expression.vars().is_subset(bound) => {
            bound.extend(result.vars());
        }
        _ => bound.extend(atom.vars()),
    }
}

/// Stable semantic checksum used by both benchmarks and integration tests.
pub fn semantic_digest(worlds: &[World]) -> String {
    let mut hash = 0xcbf29ce484222325u64;
    for (index, world) in worlds.iter().enumerate() {
        for byte in format!("{index}:").bytes().chain(
            world
                .iter()
                .flat_map(|atom| format!("{atom};").into_bytes()),
        ) {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
    }
    format!("{hash:016x}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile;

    fn atom(source: &str) -> Atom {
        crate::parser::parse_atom(source).unwrap()
    }

    fn constant(name: &str) -> Term {
        Term::Fun(name.into(), vec![])
    }

    #[test]
    fn unifies_identical_terms() {
        assert_eq!(
            unify_terms(&constant("a"), &constant("a")),
            Some(Subst::new())
        );
    }

    #[test]
    fn unifies_a_variable_with_a_term() {
        assert_eq!(
            unify_terms(&Term::Var("X".into()), &constant("a")),
            Some([("X".into(), constant("a"))].into_iter().collect())
        );
    }

    #[test]
    fn rejects_different_functors() {
        assert_eq!(unify_terms(&constant("a"), &constant("b")), None);
    }

    #[test]
    fn unifies_nested_terms() {
        let left = Term::Fun("f".into(), vec![Term::Var("X".into()), constant("b")]);
        let right = Term::Fun("f".into(), vec![constant("a"), constant("b")]);
        assert_eq!(
            unify_terms(&left, &right),
            Some([("X".into(), constant("a"))].into_iter().collect())
        );
    }

    #[test]
    fn occurs_check_rejects_infinite_terms() {
        let variable = Term::Var("X".into());
        let recursive = Term::Fun("f".into(), vec![variable.clone()]);
        assert_eq!(unify_terms(&variable, &recursive), None);
    }

    #[test]
    fn unifies_matching_atoms() {
        assert_eq!(
            unify_atom(&atom("p(X)"), &atom("p(a)")),
            Some([("X".into(), constant("a"))].into_iter().collect())
        );
    }

    #[test]
    fn rejects_atoms_with_different_predicates() {
        assert_eq!(unify_atom(&atom("p"), &atom("q")), None);
    }

    #[test]
    fn repeated_variables_require_consistent_bindings() {
        assert!(unify_atom(&atom("p(X,X)"), &atom("p(a,a)")).is_some());
        assert_eq!(unify_atom(&atom("p(X,X)"), &atom("p(a,b)")), None);
    }

    #[test]
    fn unifies_matching_previous_terms() {
        assert_eq!(
            unify_terms(
                &Term::Prev(Box::new(Term::Var("X".into()))),
                &Term::Prev(Box::new(constant("a"))),
            ),
            Some([("X".into(), constant("a"))].into_iter().collect())
        );
    }

    #[test]
    fn current_world_negative_cycle_is_not_stratifiable() {
        let program = compile("~a => b. ~b => a.").unwrap();
        assert!(stratify(&program.rules).is_err());
    }

    #[test]
    fn previous_world_negation_does_not_create_a_current_cycle() {
        let program = compile("@~a => b. ~b => a.").unwrap();
        assert!(stratify(&program.rules).is_ok());
    }

    #[test]
    fn strict_after() {
        let mut state = Interpreter::new(compile("a after b => result.").unwrap());
        state.assert(atom("b")).unwrap();
        state.step().unwrap();
        state.step().unwrap();
        state.assert(atom("a")).unwrap();
        state.step().unwrap();
        assert!(state.world().unwrap().contains(&atom("result")));
        state.step().unwrap();
        assert!(state.world().unwrap().contains(&atom("result")));
    }

    #[test]
    fn general_negative_models() {
        let state = Interpreter::new(compile("~a => b. ~b => a.").unwrap());
        let branches = state.step_all().unwrap();
        assert_eq!(branches.len(), 2);
    }

    #[test]
    fn recursive_pattern_function() {
        let source = "append([], X) -> X. append([H|T], Y) -> [H|append(T,Y)].";
        let state = Interpreter::new(compile(source).unwrap());
        let answers = state.query(&atom("append([1],[2],Z)")).unwrap();
        assert!(!answers.is_empty());
    }

    #[test]
    fn rejects_builtin_assertions_even_through_public_state() {
        let program = compile("ok.").unwrap();
        let builtin = atom("at(99)");
        let mut checked = Interpreter::new(program.clone());
        assert!(checked.assert(builtin.clone()).is_err());

        let mut direct = Interpreter::new(program);
        direct.assertions.insert(builtin);
        assert!(direct.step_all().is_err());
    }

    #[test]
    fn evaluates_external_predicates_through_query() {
        let state = Interpreter::new(compile("ok.").unwrap());
        assert_eq!(state.query(&atom("1 = 1")).unwrap().len(), 1);
        assert_eq!(state.query(&atom("1 < 2")).unwrap().len(), 1);
        let arithmetic = state.query(&atom("X is 2 + 3")).unwrap();
        assert_eq!(arithmetic[0].get("X"), Some(&Term::Fun("5".into(), vec![])));
        let at = state.query(&atom("at(N)")).unwrap();
        assert_eq!(at[0].get("N"), Some(&Term::Fun("0".into(), vec![])));
        assert_eq!(state.query(&atom("true")).unwrap().len(), 1);
        assert!(state.query(&atom("false")).unwrap().is_empty());
    }

    #[test]
    fn rejects_malformed_runtime_queries() {
        let state = Interpreter::new(compile("lookup(X) -> X. present(key).").unwrap());
        assert!(state.query(&atom("at(0,1)")).is_err());
        assert!(state.query(&atom("present")).is_err());
        assert!(state.query(&atom("present(key(a))")).is_err());
        assert!(state.query(&atom("present(@key)")).is_err());
    }

    #[test]
    fn rejects_runtime_signature_changes_even_through_public_state() {
        let predicate = Interpreter::new(compile("p.").unwrap());
        let wrong_predicate = atom("p(a)");
        let mut checked = predicate.clone();
        assert!(checked.assert(wrong_predicate.clone()).is_err());
        let mut direct = predicate;
        direct.assertions.insert(wrong_predicate);
        assert!(direct.step_all().is_err());

        let constructor = Interpreter::new(compile("value(box).").unwrap());
        let wrong_constructor = atom("value(box(a))");
        let mut checked = constructor.clone();
        assert!(checked.assert(wrong_constructor.clone()).is_err());
        let mut direct = constructor;
        direct.assertions.insert(wrong_constructor);
        assert!(direct.step_all().is_err());
    }

    #[test]
    fn keeps_dynamic_input_signatures_fixed_across_worlds() {
        let mut state = Interpreter::new(compile("ok.").unwrap());
        state.assert(atom("event")).unwrap();
        assert!(state.assert(atom("event(a)")).is_err());
        state.step().unwrap();
        assert!(state.assert(atom("event(a)")).is_err());
        state.assertions.insert(atom("event(a)"));
        assert!(state.step_all().is_err());
    }

    #[test]
    fn rejects_internal_names_and_surface_terms_in_assertions() {
        let mut pattern = Interpreter::new(compile("lookup(X) -> X.").unwrap());
        let relation = atom("lookup(a,a)");
        assert!(pattern.assert(relation.clone()).is_err());
        pattern.assertions.insert(relation);
        assert!(pattern.step_all().is_err());

        let program = compile("trigger => next fired.").unwrap();
        let generated = program.auxiliary_predicates.iter().next().unwrap().clone();
        let generated_atom = Atom::new(generated, vec![]);
        let mut generated_state = Interpreter::new(program);
        assert!(generated_state.assert(generated_atom.clone()).is_err());
        assert!(generated_state.query(&generated_atom).is_err());
        generated_state.assertions.insert(generated_atom);
        assert!(generated_state.step_all().is_err());

        let mut surface = Interpreter::new(compile("ok.").unwrap());
        assert!(surface.assert(atom("p(@a)")).is_err());
        assert!(surface.assert(atom("p(div(1))")).is_err());
    }
}
