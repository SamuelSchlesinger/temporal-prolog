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
fn result_temporal_operators_scope_over_complete_conjunctions() {
    let mut state = Interpreter::new(
        compile(include_str!(
            "../../conformance/cases/result_precedence.tpl"
        ))
        .unwrap(),
    );
    state.assert(atom("start")).unwrap();
    state.assert(atom("arm")).unwrap();
    state.step().unwrap();
    state.assert(atom("fire")).unwrap();
    state.step().unwrap();
    for expected in ["left", "right", "bell", "light"] {
        assert!(
            state.world().unwrap().contains(&atom(expected)),
            "missing {expected}"
        );
    }
}

#[test]
fn documented_unicode_aliases_execute_together() {
    let mut state = Interpreter::new(
        compile(include_str!("../../conformance/cases/unicode_aliases.tpl")).unwrap(),
    );
    state.step().unwrap();
    state.step().unwrap();
    for expected in ["value(token)", "next_fact", "unicode_ok"] {
        assert!(
            state.world().unwrap().contains(&atom(expected)),
            "missing {expected}"
        );
    }
}

#[test]
fn contextual_names_follow_their_namespace() {
    let mut keyword_state = Interpreter::new(
        compile(include_str!(
            "../../conformance/cases/keyword_constructors.tpl"
        ))
        .unwrap(),
    );
    keyword_state.step().unwrap();
    assert!(keyword_state.world().unwrap().contains(&atom(
        "keyword_terms(always,since,after,for,until,atnext,eventually,next,true,false,is)"
    )));
    assert!(keyword_state
        .world()
        .unwrap()
        .contains(&atom("prefix_builtin(5)")));
    assert!(!keyword_state.world().unwrap().contains(&atom("impossible")));

    let mut predicate_state = Interpreter::new(
        compile(include_str!(
            "../../conformance/cases/arithmetic_predicates.tpl"
        ))
        .unwrap(),
    );
    predicate_state.assert(atom("div(a,b)")).unwrap();
    predicate_state.assert(atom("mod(c,d)")).unwrap();
    predicate_state.step().unwrap();
    assert!(predicate_state
        .world()
        .unwrap()
        .contains(&atom("namespace_ok")));
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

    for (name, source) in [
        (
            "mixed predicate arity",
            include_str!("../../conformance/rejections/mixed_predicate_arity.tpl"),
        ),
        (
            "mixed constructor arity",
            include_str!("../../conformance/rejections/mixed_constructor_arity.tpl"),
        ),
        (
            "mixed pattern arity",
            include_str!("../../conformance/rejections/mixed_pattern_arity.tpl"),
        ),
        (
            "malformed pattern relation",
            include_str!("../../conformance/rejections/malformed_pattern_relation.tpl"),
        ),
        (
            "builtin result",
            include_str!("../../conformance/rejections/builtin_result.tpl"),
        ),
        (
            "malformed builtin",
            include_str!("../../conformance/rejections/malformed_builtin.tpl"),
        ),
        (
            "malformed arithmetic",
            include_str!("../../conformance/rejections/malformed_arithmetic.tpl"),
        ),
        (
            "chained temporal condition",
            include_str!("../../conformance/rejections/chained_temporal_condition.tpl"),
        ),
        (
            "non-ASCII identifier",
            include_str!("../../conformance/rejections/non_ascii_identifier.tpl"),
        ),
        (
            "overflowing for count",
            include_str!("../../conformance/rejections/for_count_overflow.tpl"),
        ),
    ] {
        assert!(compile(source).is_err(), "accepted {name}: {source:?}");
    }

    let unsafe_program = compile(include_str!(
        "../../conformance/rejections/unsafe_range.tpl"
    ))
    .unwrap();
    assert!(Interpreter::new(unsafe_program).step_all().is_err());
}
