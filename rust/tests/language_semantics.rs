use temporal_prolog::{compile, is_external_atom, parse_atom, Atom, Interpreter, Term};

fn atom(source: &str) -> Atom {
    parse_atom(source).unwrap()
}

fn contains(state: &Interpreter, source: &str) -> bool {
    state
        .world()
        .is_some_and(|world| world.contains(&atom(source)))
}

fn contains_at(state: &Interpreter, world: usize, source: &str) -> bool {
    state.worlds[world].contains(&atom(source))
}

fn state(source: &str) -> Interpreter {
    Interpreter::new(compile(source).unwrap())
}

#[test]
fn empty_program_produces_an_empty_world() {
    let mut state = state("");
    state.step().unwrap();
    assert!(state.world().unwrap().iter().all(is_external_atom));
}

#[test]
fn derives_a_fact_from_a_simple_rule() {
    let mut state = state("hot(X) => off(X).");
    state.assert(atom("hot(heater)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "off(heater)"));
}

#[test]
fn negation_as_failure_is_blocked_by_a_fact() {
    let mut state = state("device(heater). device(X) /\\ ~hot(X) => on(X).");
    state.assert(atom("hot(heater)")).unwrap();
    state.step().unwrap();
    assert!(!contains(&state, "on(heater)"));
}

#[test]
fn foot_warmer_changes_branch_when_input_disappears() {
    let mut state = state(
        "device(heater). device(X) /\\ hot(X) => off(X). \
         device(X) /\\ ~hot(X) => on(X).",
    );
    state.assert(atom("hot(heater)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "off(heater)"));
    assert!(!contains(&state, "on(heater)"));
    state.step().unwrap();
    assert!(contains(&state, "on(heater)"));
    assert!(!contains(&state, "off(heater)"));
    assert!(contains(&state, "device(heater)"));
}

#[test]
fn ground_negation_changes_when_input_disappears() {
    let mut state = state("hot(heater) => off(heater). ~hot(heater) => on(heater).");
    state.assert(atom("hot(heater)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "off(heater)"));
    assert!(!contains(&state, "on(heater)"));
    state.step().unwrap();
    assert!(contains(&state, "on(heater)"));
    assert!(!contains(&state, "off(heater)"));
}

#[test]
fn previous_condition_reads_the_previous_world() {
    let mut state = state("@on(X) /\\ hot(X) => warning(X). on(X) => on(X).");
    state.assert(atom("on(heater)")).unwrap();
    state.step().unwrap();
    assert!(!contains(&state, "warning(heater)"));
    state.assert(atom("hot(heater)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "warning(heater)"));
}

#[test]
fn previous_condition_is_false_in_world_zero() {
    let mut state = state("@p => q.");
    state.assert(atom("p")).unwrap();
    state.step().unwrap();
    assert!(!contains(&state, "q"));
}

#[test]
fn inner_and_outer_negation_differ_in_world_zero() {
    let mut state = state("@~p => inner_neg. ~@p => outer_neg.");
    state.step().unwrap();
    assert!(!contains(&state, "inner_neg"));
    assert!(contains(&state, "outer_neg"));
}

#[test]
fn previous_negation_is_evaluated_normally_after_world_zero() {
    let mut state = state("@~p => absent_before.");
    state.step().unwrap();
    state.step().unwrap();
    assert!(contains(&state, "absent_before"));
}

#[test]
fn has_been_auxiliary_does_not_capture_surrounding_variables() {
    let mut state = state("#ready /\\ item(X) => result(X).");
    state.assert(atom("ready")).unwrap();
    state.assert(atom("item(a)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "result(a)"));
}

#[test]
fn priority_style_mutual_exclusion_selects_the_first_process() {
    let mut state = state(
        "assign(X) /\\ @assigned_to(X) => assigned_to(X). \
         assign(1) /\\ ~@assigned_to_something => assigned_to(1). \
         assign(2) /\\ ~assign(1) /\\ ~@assigned_to_something => assigned_to(2). \
         assigned_to(X) => assigned_to_something.",
    );
    state.assert(atom("assign(1)")).unwrap();
    state.assert(atom("assign(2)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "assigned_to(1)"));
    assert!(!contains(&state, "assigned_to(2)"));
}

#[test]
fn current_world_rules_reach_a_fixpoint_after_previous_world_match() {
    let mut state = state("@p => q. q => r.");
    state.assert(atom("p")).unwrap();
    state.step().unwrap();
    assert!(!contains(&state, "q"));
    state.step().unwrap();
    assert!(contains(&state, "q"));
    assert!(contains(&state, "r"));
}

#[test]
fn numeric_comparison_can_succeed() {
    let mut state = state("temp(X) /\\ X > 100 => alarm.");
    state.assert(atom("temp(150)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "alarm"));
}

#[test]
fn numeric_comparison_can_fail() {
    let mut state = state("temp(X) /\\ X > 100 => alarm.");
    state.assert(atom("temp(50)")).unwrap();
    state.step().unwrap();
    assert!(!contains(&state, "alarm"));
}

#[test]
fn eventually_condition_holds_now_and_result_can_persist() {
    let mut state = state("eventually p => q. q => q.");
    state.assert(atom("p")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "q"));
    state.step().unwrap();
    assert!(contains(&state, "q"));
}

#[test]
fn next_defers_a_result_by_one_world() {
    let mut state = state("a => next b.");
    state.assert(atom("a")).unwrap();
    state.step().unwrap();
    assert!(!contains(&state, "b"));
    state.step().unwrap();
    assert!(contains(&state, "b"));
}

#[test]
fn nested_next_defers_a_result_by_two_worlds() {
    let mut state = state("a => next next b.");
    state.assert(atom("a")).unwrap();
    state.step().unwrap();
    assert!(!contains(&state, "b"));
    state.step().unwrap();
    assert!(!contains(&state, "b"));
    state.step().unwrap();
    assert!(contains(&state, "b"));
}

#[test]
fn eventually_can_participate_in_a_conjunction() {
    let mut state = state("eventually p /\\ q => r.");
    state.assert(atom("p")).unwrap();
    state.assert(atom("q")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "r"));
}

#[test]
fn ground_pattern_function_rewrites_a_nested_result() {
    let mut state = state("wrap(hello) -> box(hello). result(wrap(hello)).");
    state.step().unwrap();
    assert!(contains(&state, "result(box(hello))"));
}

#[test]
fn conditional_pattern_function_reduction_executes() {
    let mut state = state(
        "enabled(X) => choose(X) -> selected. \
         request(X) /\\ choose(X) = Y => result(Y).",
    );
    state.assert(atom("enabled(a)")).unwrap();
    state.assert(atom("request(a)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "result(selected)"));
}

#[test]
fn pattern_function_calls_require_grounded_inputs() {
    let state = state("identity(X) -> X. identity(X) = a => leaked.");
    assert!(state.step_all().is_err());
}

#[test]
fn pattern_function_clauses_must_ground_their_outputs() {
    let state = state("wild(X) -> Y. result(wild(a)).");
    assert!(state.step_all().is_err());
}

#[test]
fn positive_conditions_may_ground_pattern_function_outputs() {
    let mut state = state("value(a). value(Y) => choose(X) -> Y. result(choose(key)).");
    state.step().unwrap();
    assert!(contains(&state, "result(a)"));
}

#[test]
fn previous_negation_inside_pattern_function_is_false_in_world_zero() {
    let mut state = state(
        "@~blocked(X) => choose(X) -> selected. \
         request(X) /\\ choose(X) = Y => result(Y).",
    );
    state.assert(atom("request(a)")).unwrap();
    state.step().unwrap();
    assert!(!contains(&state, "result(selected)"));
    state.assert(atom("request(a)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "result(selected)"));
}

#[test]
fn equality_binds_a_rule_variable() {
    let mut state = state("p(X) /\\ X = hello => q(X).");
    state.assert(atom("p(hello)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "q(hello)"));
}

#[test]
fn equality_fails_for_distinct_ground_terms() {
    let mut state = state("a = b => never.");
    state.step().unwrap();
    assert!(!contains(&state, "never"));
}

#[test]
fn at_binds_the_current_world_number() {
    let mut state = state("at(N) /\\ N > 3 => late.");
    for _ in 0..5 {
        state.step().unwrap();
    }
    assert!(!contains_at(&state, 3, "late"));
    assert!(contains_at(&state, 4, "late"));
}

#[test]
fn previous_at_binds_the_previous_world_number() {
    let mut state = state("@at(N) /\\ N = 1 => prev_was_one.");
    for _ in 0..3 {
        state.step().unwrap();
    }
    assert!(contains(&state, "prev_was_one"));
}

#[test]
fn current_at_still_works_at_depth_zero() {
    let mut state = state("at(N) /\\ N = 2 => is_world_two.");
    for _ in 0..3 {
        state.step().unwrap();
    }
    assert!(contains(&state, "is_world_two"));
}

#[test]
fn doubly_previous_at_binds_two_worlds_back() {
    let mut state = state("@@at(N) /\\ N = 1 => two_back_was_one.");
    for _ in 0..4 {
        state.step().unwrap();
    }
    assert!(contains(&state, "two_back_was_one"));
}

#[test]
fn bare_fact_is_derived() {
    let mut state = state("p.");
    state.step().unwrap();
    assert!(contains(&state, "p"));
}

#[test]
fn non_ground_assertion_is_rejected() {
    let mut state = state("");
    assert!(state.assert(atom("p(X)")).is_err());
}

#[test]
fn world_history_has_one_entry_per_step() {
    let mut state = state("");
    for _ in 0..3 {
        state.step().unwrap();
    }
    assert_eq!(state.worlds.len(), 3);
}

#[test]
fn self_unification_preserves_an_existing_binding() {
    let mut state = state("p(X) /\\ X = X => q(X).");
    state.assert(atom("p(a)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "q(a)"));
}

#[test]
fn conditional_always_persists_its_bound_result() {
    let mut state = state("c(X) => always r(X).");
    state.assert(atom("c(a)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "r(a)"));
    state.step().unwrap();
    assert!(contains(&state, "r(a)"));
    state.step().unwrap();
    assert!(contains(&state, "r(a)"));
}

#[test]
fn unconditional_until_stops_and_then_resumes() {
    let mut state = state("q until trigger.");
    state.step().unwrap();
    assert!(contains(&state, "q"));
    state.assert(atom("trigger")).unwrap();
    state.step().unwrap();
    assert!(!contains(&state, "q"));
    state.step().unwrap();
    assert!(contains(&state, "q"));
}

#[test]
fn conditional_until_persists_until_the_trigger() {
    let mut state = state("c => q until trigger.");
    state.assert(atom("c")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "q"));
    state.step().unwrap();
    assert!(contains(&state, "q"));
    state.assert(atom("trigger")).unwrap();
    state.step().unwrap();
    assert!(!contains(&state, "q"));
}

#[test]
fn unconditional_atnext_fires_when_trigger_appears() {
    let mut state = state("q atnext trigger.");
    state.step().unwrap();
    assert!(!contains(&state, "q"));
    state.assert(atom("trigger")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "q"));
}

#[test]
fn pattern_function_condition_can_read_the_previous_world() {
    let mut state = state("lookup(key) -> val. marker. marker /\\ @lookup(key) = X => found(X).");
    state.step().unwrap();
    state.step().unwrap();
    assert!(contains(&state, "found(val)"));
}

#[test]
fn negative_numbers_participate_in_comparisons() {
    let mut state = state("temp(X) /\\ X < 0 => freezing.");
    state.assert(atom("temp(-5)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "freezing"));
}

#[test]
fn not_equal_filters_equal_values() {
    let mut state = state("p(a). p(b). p(X) /\\ X != a => not_a(X).");
    state.step().unwrap();
    assert!(contains(&state, "not_a(b)"));
    assert!(!contains(&state, "not_a(a)"));
}

#[test]
fn is_evaluates_addition() {
    let mut state = state("p(X) /\\ X is 2 + 3 => q(X).");
    state.assert(atom("p(5)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "q(5)"));
}

#[test]
fn is_rejects_the_wrong_value() {
    let mut state = state("p(X) /\\ X is 2 + 3 => q(X).");
    state.assert(atom("p(4)")).unwrap();
    state.step().unwrap();
    assert!(!contains(&state, "q(4)"));
}

#[test]
fn arithmetic_uses_bound_variables() {
    let mut state = state("val(X) /\\ Y is X + 1 => next_val(Y).");
    state.assert(atom("val(5)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "next_val(6)"));
}

#[test]
fn arithmetic_evaluates_multiplication() {
    let mut state = state("val(X) /\\ Y is X * 3 => triple(Y).");
    state.assert(atom("val(4)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "triple(12)"));
}

#[test]
fn arithmetic_respects_parentheses() {
    let mut state = state("Y is (2 + 3) * 4 => result(Y).");
    state.step().unwrap();
    assert!(contains(&state, "result(20)"));
}

#[test]
fn arithmetic_evaluates_subtraction() {
    let mut state = state("Y is 10 - 3 => result(Y).");
    state.step().unwrap();
    assert!(contains(&state, "result(7)"));
}

#[test]
fn arithmetic_evaluates_division_and_modulo() {
    let mut state = state("Q is 10 div 3 => quotient(Q). R is 10 mod 3 => remainder(R).");
    state.step().unwrap();
    assert!(contains(&state, "quotient(3)"));
    assert!(contains(&state, "remainder(1)"));
}

#[test]
fn invalid_arithmetic_is_logical_failure() {
    let mut state = state(
        "Bad is 1 div 0 => division_by_zero_succeeded(Bad). \
         Bad is not_an_integer + 1 => non_integer_succeeded(Bad).",
    );
    state.step().unwrap();
    assert!(state.world().unwrap().iter().all(|candidate| {
        candidate.name != "division_by_zero_succeeded" && candidate.name != "non_integer_succeeded"
    }));
}

#[test]
fn comparisons_evaluate_arithmetic_expressions() {
    let mut state = state("val(X) /\\ X + 1 > 5 => big(X).");
    state.assert(atom("val(5)")).unwrap();
    state.assert(atom("val(3)")).unwrap();
    state.step().unwrap();
    assert!(contains(&state, "big(5)"));
    assert!(!contains(&state, "big(3)"));
}

#[test]
fn append_base_case_returns_the_second_list() {
    let mut state = state(
        "append([],X) -> X. items([1,2]). \
         items(X) /\\ append([],X) = Y => result(Y).",
    );
    state.step().unwrap();
    assert!(contains(&state, "result([1,2])"));
}

#[test]
fn recursive_append_combines_lists() {
    let mut state = state(
        "append([],X) -> X. append([H|T],Y) -> [H|append(T,Y)]. \
         a([1]). b([2,3]). \
         a(X) /\\ b(Y) /\\ append(X,Y) = Z => result(Z).",
    );
    state.step().unwrap();
    assert!(contains(&state, "result([1,2,3])"));
}

#[test]
fn pattern_function_expands_inside_a_rule_head() {
    let mut state = state(
        "append([],X) -> X. append([H|T],Y) -> [H|append(T,Y)]. \
         a([1,2]). b([3]). a(X) /\\ b(Y) => combined(append(X,Y)).",
    );
    state.step().unwrap();
    assert!(contains(&state, "combined([1,2,3])"));
}

#[test]
fn negated_pattern_function_succeeds_for_a_false_result() {
    let mut state = state(
        "append([],X) -> X. marker. \
         marker /\\ ~append([],[1],[99]) => not_match.",
    );
    state.step().unwrap();
    assert!(contains(&state, "not_match"));
}

#[test]
fn negated_pattern_function_fails_for_a_true_result() {
    let mut state = state(
        "append([],X) -> X. marker. \
         marker /\\ ~append([],[1],[1]) => should_not_derive.",
    );
    state.step().unwrap();
    assert!(!contains(&state, "should_not_derive"));
}

#[test]
fn public_query_resolves_recursive_pattern_functions() {
    let state = state("append([],X) -> X. append([H|T],Y) -> [H|append(T,Y)].");
    let answers = state.query(&atom("append([1],[2],Z)")).unwrap();
    let expected = atom("value([1,2])").terms.remove(0);
    assert!(answers
        .iter()
        .any(|substitution| substitution.get("Z") == Some(&expected)));
}

#[test]
fn public_pattern_function_queries_require_grounded_inputs() {
    let state = state("identity(X) -> X.");
    assert!(state.query(&atom("identity(X,Y)")).is_err());
    assert!(state.query(&atom("identity(a,Y)")).is_ok());
}

#[test]
fn recursive_pattern_function_depth_limit_is_an_error() {
    let state = state("loop(X) -> loop(X).");
    assert!(state.query(&atom("loop(a,Y)")).is_err());
}

#[test]
fn arbitrary_precision_floor_division_has_the_specified_signs() {
    let mut state = state(
        "Q1 is -7 div 3 => q1(Q1). R1 is -7 mod 3 => r1(R1). \
         Q2 is 7 div -3 => q2(Q2). R2 is 7 mod -3 => r2(R2).",
    );
    state.step().unwrap();
    assert!(contains(&state, "q1(-3)"));
    assert!(contains(&state, "r1(2)"));
    assert!(contains(&state, "q2(-3)"));
    assert!(contains(&state, "r2(-2)"));
}

#[test]
fn arbitrary_precision_multiplication_does_not_overflow() {
    let mut state = state("Huge is 9223372036854775808 * 9223372036854775808 => huge(Huge).");
    state.step().unwrap();
    assert!(contains(
        &state,
        "huge(85070591730234615865843651857942052864)"
    ));
}

#[test]
fn query_binds_arithmetic_results() {
    let state = state("");
    let answers = state.query(&atom("X is 2 + 3")).unwrap();
    assert_eq!(answers[0].get("X"), Some(&Term::Fun("5".into(), vec![])));
}
