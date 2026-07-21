use temporal_prolog::{compile, parse_atom, Interpreter};

fn atom(source: &str) -> temporal_prolog::Atom {
    parse_atom(source).unwrap()
}

#[test]
fn initial_world_negation() {
    let mut state = Interpreter::new(
        compile(include_str!("../../conformance/cases/initial_world.tpl")).unwrap(),
    );
    state.step().unwrap();
    assert!(!state.world().unwrap().contains(&atom("inner_negation")));
    assert!(state.world().unwrap().contains(&atom("outer_negation")));
}

#[test]
fn strict_after_is_latched() {
    let source = include_str!("../../conformance/cases/after_strict.tpl");
    let mut same_world = Interpreter::new(compile(source).unwrap());
    same_world.assert(atom("restart")).unwrap();
    same_world.assert(atom("monitoring")).unwrap();
    same_world.step().unwrap();
    assert!(!same_world.world().unwrap().contains(&atom("check_system")));

    let mut state = Interpreter::new(compile(source).unwrap());
    state.assert(atom("restart")).unwrap();
    state.step().unwrap();
    state.assert(atom("monitoring")).unwrap();
    state.step().unwrap();
    assert!(state.world().unwrap().contains(&atom("check_system")));
    state.step().unwrap();
    assert!(state.world().unwrap().contains(&atom("check_system")));
}

#[test]
fn negative_cycle_has_two_branches() {
    let state = Interpreter::new(
        compile(include_str!("../../conformance/cases/negative_cycle.tpl")).unwrap(),
    );
    let branches = state.step_all().unwrap();
    assert_eq!(branches.len(), 2);
    let outcomes: Vec<_> = branches
        .iter()
        .map(|branch| {
            (
                branch.world().unwrap().contains(&atom("a")),
                branch.world().unwrap().contains(&atom("b")),
            )
        })
        .collect();
    assert!(outcomes.contains(&(true, false)));
    assert!(outcomes.contains(&(false, true)));
}

#[test]
fn paper_4_7_has_overlooked_third_branch() {
    let mut state =
        Interpreter::new(compile(include_str!("../../conformance/cases/paper_4_7.tpl")).unwrap());
    state.assert(atom("assign(1)")).unwrap();
    state.assert(atom("assign(2)")).unwrap();
    let branches = state.step_all().unwrap();
    assert_eq!(branches.len(), 3);
    assert!(branches.iter().any(|branch| !branch
        .world()
        .unwrap()
        .contains(&atom("assigned_to(1)"))
        && !branch.world().unwrap().contains(&atom("assigned_to(2)"))));
}

#[test]
fn unsupported_negative_blocker_remains_a_classical_model() {
    let state = Interpreter::new(
        compile(include_str!(
            "../../conformance/cases/unsupported_blocker.tpl"
        ))
        .unwrap(),
    );
    let branches = state.step_all().unwrap();
    assert_eq!(branches.len(), 2);
    assert!(branches
        .iter()
        .any(|branch| branch.world().unwrap().contains(&atom("q(a)"))));
    assert!(branches
        .iter()
        .any(|branch| branch.world().unwrap().contains(&atom("p(a)"))));
}

#[test]
fn recursive_pattern_function() {
    let mut state =
        Interpreter::new(compile(include_str!("../../conformance/cases/append.tpl")).unwrap());
    state.step().unwrap();
    assert!(state.world().unwrap().contains(&atom("joined([1,2,3,4])")));
}

#[test]
fn portable_arbitrary_precision_arithmetic() {
    let mut state = Interpreter::new(
        compile(include_str!("../../conformance/cases/arithmetic_edges.tpl")).unwrap(),
    );
    state.step().unwrap();
    let world = state.world().unwrap();
    for expected in [
        "canonical_integer_spellings(7,0)",
        "quotient_negative(-3)",
        "remainder_negative(2)",
        "quotient_negative_divisor(-3)",
        "remainder_negative_divisor(-2)",
        "precedence(4)",
        "arbitrary_precision(85070591730234615865843651857942052864)",
    ] {
        assert!(world.contains(&atom(expected)), "missing {expected}");
    }
    assert!(world
        .iter()
        .all(|candidate| candidate.name != "division_by_zero_succeeded"));
}

#[test]
fn shared_rejection_cases() {
    assert!(compile(include_str!("../../conformance/rejections/for_zero.tpl")).is_err());
    assert!(compile(include_str!(
        "../../conformance/rejections/plain_previous_term.tpl"
    ))
    .is_err());
    assert!(compile(include_str!(
        "../../conformance/rejections/missing_period.tpl"
    ))
    .is_err());

    let unsafe_program = compile(include_str!(
        "../../conformance/rejections/unsafe_range.tpl"
    ))
    .unwrap();
    assert!(Interpreter::new(unsafe_program).step_all().is_err());
}
