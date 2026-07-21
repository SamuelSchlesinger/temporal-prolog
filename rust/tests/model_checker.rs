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
    assert_eq!(result.nodes.len(), 5);
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
    assert_eq!(
        result.render_summary(1, false),
        include_str!("../../examples/model-checking/commit-buggy.expected")
    );
    assert!(result.render_dot(false).contains("fillcolor=\"#fee2e2\""));
}
