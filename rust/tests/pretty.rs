use temporal_prolog::{
    compile, parse_atom, parse_condition, parse_program, parse_result, parse_rule, parse_term,
    pretty_atom, pretty_condition, pretty_normal_condition, pretty_normal_rule,
    pretty_normalized_program, pretty_program, pretty_result, pretty_rule, pretty_term, Atom,
    NormalCond, NormalRule, Term,
};

#[test]
fn renders_arithmetic_with_readable_precedence() {
    assert_eq!(pretty_term(&parse_term("X + 1").unwrap()), "X + 1");
    assert_eq!(
        pretty_term(&parse_term("(X + 1) * 3").unwrap()),
        "(X + 1) * 3"
    );
    assert_eq!(
        pretty_term(&parse_term("7 div 3 mod 2").unwrap()),
        "(7 div 3) mod 2"
    );
}

#[test]
fn renders_lists_and_previous_terms() {
    assert_eq!(pretty_term(&parse_term("[a,b|T]").unwrap()), "[a, b | T]");
    assert_eq!(pretty_term(&parse_term("@[a,b]").unwrap()), "@[a, b]");
    assert_eq!(pretty_term(&parse_term("@(X + 1)").unwrap()), "@(X + 1)");
}

#[test]
fn renders_builtin_atoms_infix() {
    assert_eq!(
        pretty_atom(&parse_atom("Y is X + 1").unwrap()),
        "Y is X + 1"
    );
    assert_eq!(pretty_atom(&parse_atom("X >= 5").unwrap()), "X >= 5");
}

#[test]
fn renders_temporal_condition_precedence_explicitly() {
    assert_eq!(
        pretty_condition(&parse_condition("a /\\ b since c").unwrap()),
        "(a /\\ b) since c"
    );
    assert_eq!(
        pretty_condition(&parse_condition("a since b /\\ c").unwrap()),
        "a since (b /\\ c)"
    );
    assert_eq!(
        pretty_condition(&parse_condition("eventually (a after b)").unwrap()),
        "eventually (a after b)"
    );
}

#[test]
fn renders_nested_results_and_reductions() {
    assert_eq!(
        pretty_result(&parse_result("always (next p)").unwrap()),
        "always (next p)"
    );
    assert_eq!(
        pretty_result(&parse_result("(p /\\ q) until (a since b)").unwrap()),
        "(p /\\ q) until (a since b)"
    );
    assert_eq!(
        pretty_result(&parse_result("choose(X) -> selected").unwrap()),
        "choose(X) -> selected"
    );
}

#[test]
fn renders_rules_and_programs_as_parseable_source() {
    let rule = parse_rule("(a since b) /\\ c => next result.").unwrap();
    assert_eq!(pretty_rule(&rule), "(a since b) /\\ c => next result.");

    let program = parse_program("p.\na => always q.\nlookup(X) -> X.\n").unwrap();
    assert_eq!(
        pretty_program(&program),
        "p.\na => always q.\nlookup(X) -> X.\n"
    );
}

#[test]
fn every_term_form_round_trips() {
    for source in [
        "X",
        "42",
        "-3",
        "f(X,g(a))",
        "[]",
        "[a,b]",
        "[H|T]",
        "@X",
        "@(X + 1)",
        "X + (Y + Z)",
        "(X + Y) + Z",
        "X * (Y + Z)",
        "7 div 3 mod 2",
    ] {
        let parsed = parse_term(source).unwrap();
        let rendered = pretty_term(&parsed);
        assert_eq!(
            parse_term(&rendered).unwrap(),
            parsed,
            "{source} -> {rendered}"
        );
    }
}

#[test]
fn every_condition_form_round_trips() {
    for source in [
        "p(X)",
        "X = Y",
        "~p",
        "@p",
        "#p",
        "?p",
        "eventually p",
        "~@p",
        "@~p",
        "#(a /\\ b)",
        "?(a since b)",
        "eventually (a after b)",
        "a /\\ b /\\ c",
        "(a /\\ b) since c",
        "a since (b /\\ c)",
        "(a since b) after (c for 2)",
        "~(a /\\ b)",
    ] {
        let parsed = parse_condition(source).unwrap();
        let rendered = pretty_condition(&parsed);
        assert_eq!(
            parse_condition(&rendered).unwrap(),
            parsed,
            "{source} -> {rendered}"
        );
    }
}

#[test]
fn every_result_form_round_trips() {
    for source in [
        "p(X)",
        "choose(X) -> selected",
        "always p",
        "next next p",
        "(always p) /\\ (next q)",
        "p /\\ q until stop",
        "p /\\ q atnext trigger",
        "(p /\\ q) until (a since b)",
        "p atnext (a after b)",
    ] {
        let parsed = parse_result(source).unwrap();
        let rendered = pretty_result(&parsed);
        assert_eq!(
            parse_result(&rendered).unwrap(),
            parsed,
            "{source} -> {rendered}"
        );
    }
}

#[test]
fn rules_and_programs_round_trip() {
    for source in [
        "p.",
        "a /\\ b => c.",
        "(a since b) /\\ c => next result.",
        "enabled(X) => choose(X) -> selected.",
        "q until stop.",
    ] {
        let parsed = parse_rule(source).unwrap();
        let rendered = pretty_rule(&parsed);
        assert_eq!(
            parse_rule(&rendered).unwrap(),
            parsed,
            "{source} -> {rendered}"
        );
    }

    for source in [
        "",
        "p.\na => next b.\n",
        "lookup(X) -> X.\npresent(lookup(key)).\n",
    ] {
        let parsed = parse_program(source).unwrap();
        let rendered = pretty_program(&parsed);
        assert_eq!(
            parse_program(&rendered).unwrap(),
            parsed,
            "{source:?} -> {rendered:?}"
        );
    }
}

#[test]
fn public_single_construct_parsers_reject_trailing_input() {
    assert!(parse_term("a b").is_err());
    assert!(parse_condition("a.").is_err());
    assert!(parse_result("p.").is_err());
    assert!(parse_rule("p. q.").is_err());
}

#[test]
fn renders_normal_form_without_changing_canonical_display() {
    let condition = NormalCond {
        depth: 2,
        negated: true,
        atom: Atom::new("p", vec![Term::Var("X".into())]),
    };
    let rule = NormalRule {
        conditions: vec![condition.clone()],
        head: Atom::new("q", vec![Term::Var("X".into())]),
    };
    assert_eq!(pretty_normal_condition(&condition), "@@~p(X)");
    assert_eq!(pretty_normal_rule(&rule), "@@~p(X) => q(X).");

    let program = compile("@~p(X) /\\ seed(X) => q(X).").unwrap();
    let rendered = pretty_normalized_program(&program);
    assert!(rendered.contains("=> q(X)."));
    assert_eq!(format!("{}", parse_term("[a,b]").unwrap()), ".(a,.(b,[]))");
}
