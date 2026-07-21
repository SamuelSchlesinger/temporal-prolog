use temporal_prolog::{compile, parse_atom, Interpreter};

fn atom(source: &str) -> temporal_prolog::Atom {
    parse_atom(source).unwrap()
}

fn contains(state: &Interpreter, source: &str) -> bool {
    state
        .world()
        .is_some_and(|world| world.contains(&atom(source)))
}

#[test]
fn future_result_operators() {
    let mut always = Interpreter::new(compile("trigger => always held.").unwrap());
    always.assert(atom("trigger")).unwrap();
    always.step().unwrap();
    assert!(contains(&always, "held"));
    always.step().unwrap();
    assert!(contains(&always, "held"));

    let mut next = Interpreter::new(compile("trigger => next fired.").unwrap());
    next.assert(atom("trigger")).unwrap();
    next.step().unwrap();
    assert!(!contains(&next, "fired"));
    next.step().unwrap();
    assert!(contains(&next, "fired"));

    let mut atnext = Interpreter::new(compile("trigger => signal atnext go.").unwrap());
    atnext.assert(atom("trigger")).unwrap();
    atnext.step().unwrap();
    assert!(!contains(&atnext, "signal"));
    atnext.assert(atom("go")).unwrap();
    atnext.step().unwrap();
    assert!(contains(&atnext, "signal"));

    let mut until = Interpreter::new(compile("value until stop.").unwrap());
    until.step().unwrap();
    assert!(contains(&until, "value"));
    until.assert(atom("stop")).unwrap();
    until.step().unwrap();
    assert!(!contains(&until, "value"));
}

#[test]
fn past_condition_operators() {
    let source = "ready for 2 => twice. ready since start => since_result. \
                  ?event => once_result. #ready => continuously_ready.";
    let mut state = Interpreter::new(compile(source).unwrap());
    state.assert(atom("ready")).unwrap();
    state.assert(atom("start")).unwrap();
    state.assert(atom("event")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "since_result"));
    assert!(contains(&state, "once_result"));
    assert!(contains(&state, "continuously_ready"));
    assert!(!contains(&state, "twice"));

    state.assert(atom("ready")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "twice"));
    assert!(contains(&state, "once_result"));
    assert!(contains(&state, "continuously_ready"));
}

#[test]
fn term_previous_only_moves_pattern_function_condition() {
    let source = "lookup(key) -> value. present(@lookup(key)) => found.";
    let mut state = Interpreter::new(compile(source).unwrap());
    state.assert(atom("present(value)")).unwrap();
    state.step().unwrap();
    assert!(!contains(&state, "found"));
    state.assert(atom("present(value)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "found"));
}

#[test]
fn fast_and_general_evaluators_agree() {
    let program = compile("seed(X) => p(X). p(X) /\\ ~blocked(X) => q(X).").unwrap();
    let mut state = Interpreter::new(program);
    state.assert(atom("seed(a)")).unwrap();
    let fast = state.step_all().unwrap();
    let general = state.step_general_all().unwrap();
    assert_eq!(fast.len(), 1);
    assert_eq!(general.len(), 1);
    assert_eq!(fast[0].world(), general[0].world());
}

#[test]
fn recursion_limit_and_range_errors_are_not_logical_failure() {
    let loop_program = compile("loop(X) -> loop(X).").unwrap();
    let loop_state = Interpreter::new(loop_program);
    assert!(loop_state.query(&atom("loop(a,Y)")).is_err());

    let unsafe_program = compile("~p(X) => q(X).").unwrap();
    let unsafe_state = Interpreter::new(unsafe_program);
    assert!(unsafe_state.step_all().is_err());
}

#[test]
fn arbitrary_precision_floor_division_and_invalid_arithmetic() {
    let mut state = Interpreter::new(
        compile(include_str!("../../conformance/cases/arithmetic_edges.tpl")).unwrap(),
    );
    state.step().unwrap();
    assert!(contains(&state, "canonical_integer_spellings(7,0)"));
    assert!(contains(&state, "quotient_negative(-3)"));
    assert!(contains(&state, "remainder_negative(2)"));
    assert!(contains(&state, "quotient_negative_divisor(-3)"));
    assert!(contains(&state, "remainder_negative_divisor(-2)"));
    assert!(contains(&state, "precedence(4)"));
    assert!(contains(
        &state,
        "arbitrary_precision(85070591730234615865843651857942052864)"
    ));
    assert!(state
        .world()
        .unwrap()
        .iter()
        .all(|candidate| candidate.name != "division_by_zero_succeeded"));
}
