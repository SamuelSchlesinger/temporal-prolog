use temporal_prolog::{compile, parse_scenario, run_model_check};

#[test]
fn explores_both_safe_arbiter_choices() {
    let scenario = parse_scenario(
        "arbiter.tpmc",
        include_str!("../../examples/model-checking/arbiter.tpmc"),
    )
    .unwrap();
    let result = run_model_check(
        &scenario,
        compile(include_str!("../../examples/model-checking/arbiter.tpl")).unwrap(),
    )
    .unwrap();
    assert!(result.passed());
    assert_eq!(result.nodes.len(), 9);
    assert_eq!(result.terminal_nodes.len(), 2);
    assert_eq!(result.max_width, 2);
    assert_eq!(
        result.render_summary(1, false),
        include_str!("../../examples/model-checking/arbiter.expected")
    );
    assert_eq!(
        result.render_dot(false),
        include_str!("../../examples/model-checking/arbiter.expected.dot")
    );
}

#[test]
fn accepts_correct_atomic_commit() {
    let scenario = parse_scenario(
        "commit-safe.tpmc",
        include_str!("../../examples/model-checking/commit-safe.tpmc"),
    )
    .unwrap();
    let result = run_model_check(
        &scenario,
        compile(include_str!("../../examples/model-checking/commit.tpl")).unwrap(),
    )
    .unwrap();
    assert!(result.passed());
    assert_eq!(result.nodes.len(), 14);
    assert_eq!(result.terminal_nodes.len(), 4);
    assert_eq!(
        result.render_summary(1, false),
        include_str!("../../examples/model-checking/commit-safe.expected")
    );
}

#[test]
fn reports_shortest_broken_commit_counterexample() {
    let scenario = parse_scenario(
        "commit-buggy.tpmc",
        include_str!("../../examples/model-checking/commit-buggy.tpmc"),
    )
    .unwrap();
    let result = run_model_check(
        &scenario,
        compile(include_str!(
            "../../examples/model-checking/commit-buggy.tpl"
        ))
        .unwrap(),
    )
    .unwrap();
    assert!(!result.passed());
    let steps = result.counterexample_traces()[0]
        .iter()
        .map(|node| node.step)
        .collect::<Vec<_>>();
    assert_eq!(steps, vec![Some(0), Some(1), Some(2)]);
    assert_eq!(result.counterexample_traces().len(), 2);
    assert_eq!(
        result.render_summary(1, false),
        include_str!("../../examples/model-checking/commit-buggy.expected")
    );
    assert!(result.render_dot(false).contains("fillcolor=\"#fee2e2\""));
}

#[test]
fn invariants_match_stored_facts_not_pattern_function_queries() {
    let scenario = parse_scenario(
        "fact-only.tpmc",
        "name fact-only\nprogram ignored.tpl\nsteps 1\n\
         invariant no_lookup_fact forbids lookup(key,value)\n",
    )
    .unwrap();
    let result = run_model_check(&scenario, compile("lookup(key) -> value.").unwrap()).unwrap();
    assert!(result.passed());
}

#[test]
fn explores_explicit_no_input_alternative() {
    let scenario = parse_scenario(
        "optional.tpmc",
        "name optional\nprogram ignored.tpl\nsteps 1\n\
         choose 0 event present\nchoose 0 event none\n\
         invariant no_bad forbids bad\n",
    )
    .unwrap();
    let result = run_model_check(&scenario, compile("present => bad.").unwrap()).unwrap();
    assert!(!result.passed());
    assert_eq!(result.nodes.len(), 3);
    assert_eq!(result.counterexample_traces().len(), 1);
}

#[test]
fn renders_source_aux_suffixes_but_hides_generated_predicates() {
    let scenario = parse_scenario(
        "auxiliary.tpmc",
        "name auxiliary\nprogram ignored.tpl\nsteps 2\n\
         assert 0 trigger\ninvariant no_bad forbids bad\n",
    )
    .unwrap();
    let result = run_model_check(
        &scenario,
        compile("user_aux0. always_aux0. trigger => next generated.").unwrap(),
    )
    .unwrap();
    let dot = result.render_dot(false);
    assert!(dot.contains("user_aux0"));
    assert!(dot.contains("always_aux0"));
    assert!(!dot.contains("next_aux1"));
}
