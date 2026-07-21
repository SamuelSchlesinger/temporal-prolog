use std::collections::BTreeSet;
use temporal_prolog::{Atom, Interpreter, NormalCond, NormalRule, NormalizedProgram, World};

fn atom(name: &str) -> Atom {
    Atom::new(name, vec![])
}

fn positive(atom: &Atom) -> NormalCond {
    NormalCond {
        depth: 0,
        negated: false,
        atom: atom.clone(),
    }
}

fn negative(atom: &Atom) -> NormalCond {
    NormalCond {
        depth: 0,
        negated: true,
        atom: atom.clone(),
    }
}

fn rule(conditions: Vec<NormalCond>, head: &Atom) -> NormalRule {
    NormalRule {
        conditions,
        head: head.clone(),
    }
}

#[test]
fn general_evaluator_agrees_with_independent_exhaustive_oracle() {
    let a = atom("a");
    let b = atom("b");
    let false_atom = atom("false");

    // These semantically inert clauses put a and b in one SCC, making the
    // paper's SCC order coincide with ordinary subset minimality.
    let structural = vec![
        rule(vec![positive(&a), positive(&false_atom)], &b),
        rule(vec![positive(&b), positive(&false_atom)], &a),
    ];
    let optional = vec![
        rule(vec![], &a),
        rule(vec![], &b),
        rule(vec![negative(&a)], &a),
        rule(vec![negative(&b)], &b),
        rule(vec![negative(&b)], &a),
        rule(vec![negative(&a)], &b),
        rule(vec![positive(&a)], &b),
        rule(vec![positive(&b)], &a),
        rule(vec![positive(&a), negative(&b)], &b),
        rule(vec![positive(&b), negative(&a)], &a),
    ];
    let universe = [a.clone(), b.clone()].into_iter().collect::<World>();

    for mask in 0usize..(1usize << optional.len()) {
        let mut rules = structural.clone();
        rules.extend(
            optional
                .iter()
                .enumerate()
                .filter(|(index, _)| mask & (1 << index) != 0)
                .map(|(_, rule)| rule.clone()),
        );

        let expected = oracle_models(&rules, &[a.clone(), b.clone()]);
        let program = NormalizedProgram {
            rules,
            pattern_functions: BTreeSet::new(),
        };
        let mut actual = Interpreter::new(program)
            .step_general_all()
            .unwrap_or_else(|error| panic!("program {mask}: {error}"))
            .into_iter()
            .map(|state| {
                state
                    .world()
                    .expect("one step creates a world")
                    .intersection(&universe)
                    .cloned()
                    .collect::<World>()
            })
            .collect::<Vec<_>>();
        actual.sort();
        assert_eq!(actual, expected, "program mask {mask}");
    }
}

fn oracle_models(rules: &[NormalRule], atoms: &[Atom]) -> Vec<World> {
    let mut models = Vec::new();
    for mask in 0usize..(1usize << atoms.len()) {
        let world = atoms
            .iter()
            .enumerate()
            .filter(|(index, _)| mask & (1 << index) != 0)
            .map(|(_, atom)| atom.clone())
            .collect::<World>();
        if rules.iter().all(|rule| oracle_rule(rule, &world)) {
            models.push(world);
        }
    }
    models
        .iter()
        .filter(|model| {
            !models
                .iter()
                .any(|other| other.len() < model.len() && other.is_subset(model))
        })
        .cloned()
        .collect()
}

fn oracle_rule(rule: &NormalRule, world: &World) -> bool {
    !rule
        .conditions
        .iter()
        .all(|condition| oracle_condition(condition, world))
        || world.contains(&rule.head)
}

fn oracle_condition(condition: &NormalCond, world: &World) -> bool {
    let positive = match condition.atom.name.as_str() {
        "false" => false,
        "true" => true,
        _ => world.contains(&condition.atom),
    };
    positive != condition.negated
}
