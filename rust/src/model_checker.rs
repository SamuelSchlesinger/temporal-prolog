use crate::{world_matches, Atom, ChoiceAlternative, ChoiceGroup, Interpreter, Scenario, Term};
use std::collections::BTreeSet;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckNode {
    pub id: usize,
    pub parent: Option<usize>,
    pub step: Option<usize>,
    pub assertions: Vec<Atom>,
    pub facts: Vec<Atom>,
    pub violations: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckResult {
    pub scenario: Scenario,
    pub nodes: Vec<CheckNode>,
    pub terminal_nodes: Vec<usize>,
    pub max_width: usize,
}

struct ActiveNode {
    node_id: usize,
    interpreter: Interpreter,
}

struct Child {
    parent: usize,
    interpreter: Interpreter,
    assertions: Vec<Atom>,
    facts: Vec<Atom>,
    violations: Vec<String>,
}

/// Explore every minimal-model branch to the scenario horizon.  A branch
/// terminates at its first invariant violation.
pub fn run_model_check(
    scenario: &Scenario,
    program: crate::NormalizedProgram,
) -> Result<CheckResult, String> {
    let root = CheckNode {
        id: 0,
        parent: None,
        step: None,
        assertions: Vec::new(),
        facts: Vec::new(),
        violations: Vec::new(),
    };
    let mut nodes = vec![root];
    let mut active = vec![ActiveNode {
        node_id: 0,
        interpreter: Interpreter::new(program),
    }];
    let mut violated_terminals = Vec::new();
    let mut max_width = 0;

    for step in 0..scenario.steps {
        if active.is_empty() {
            break;
        }
        let fixed_assertions = scenario.assertions.get(&step).cloned().unwrap_or_default();
        let groups = scenario.choices.get(&step).cloned().unwrap_or_default();
        let input_variants = input_variants(&fixed_assertions, &groups);
        let mut children = Vec::new();
        for active_node in active {
            for assertions in &input_variants {
                let mut asserted = active_node.interpreter.clone();
                for atom in assertions {
                    asserted.assert(atom.clone())?;
                }
                let mut branches = asserted.step_all()?;
                branches.sort_by_key(|branch| branch.world().cloned().unwrap_or_default());
                for branch in branches {
                    let world = branch
                        .world()
                        .expect("a successful step always creates a world");
                    let violations = scenario
                        .invariants
                        .iter()
                        .filter(|invariant| world_matches(&invariant.forbidden, world))
                        .map(|invariant| invariant.name.clone())
                        .collect();
                    let facts = world.iter().cloned().collect();
                    children.push(Child {
                        parent: active_node.node_id,
                        interpreter: branch,
                        assertions: assertions.clone(),
                        facts,
                        violations,
                    });
                }
            }
        }

        max_width = max_width.max(children.len());
        let mut next_active = Vec::new();
        for child in children {
            let id = nodes.len();
            let is_violation = !child.violations.is_empty();
            nodes.push(CheckNode {
                id,
                parent: Some(child.parent),
                step: child.interpreter.worlds.len().checked_sub(1),
                assertions: child.assertions,
                facts: child.facts,
                violations: child.violations,
            });
            if is_violation {
                violated_terminals.push(id);
            } else {
                next_active.push(ActiveNode {
                    node_id: id,
                    interpreter: child.interpreter,
                });
            }
        }
        active = next_active;
    }

    violated_terminals.extend(active.iter().map(|node| node.node_id));
    Ok(CheckResult {
        scenario: scenario.clone(),
        nodes,
        terminal_nodes: violated_terminals,
        max_width,
    })
}

impl CheckResult {
    pub fn passed(&self) -> bool {
        self.nodes.iter().all(|node| node.violations.is_empty())
    }

    pub fn counterexample_traces(&self) -> Vec<Vec<&CheckNode>> {
        self.nodes
            .iter()
            .filter(|node| !node.violations.is_empty())
            .map(|node| {
                let mut trace = Vec::new();
                let mut current = node;
                loop {
                    if current.id != 0 {
                        trace.push(current);
                    }
                    let Some(parent) = current.parent else {
                        break;
                    };
                    current = &self.nodes[parent];
                }
                trace.reverse();
                trace
            })
            .collect()
    }

    pub fn render_summary(&self, max_counterexamples: usize, include_internal: bool) -> String {
        let violation_nodes = self
            .nodes
            .iter()
            .filter(|node| !node.violations.is_empty())
            .count();
        let safe_leaves = self
            .terminal_nodes
            .iter()
            .filter(|id| self.nodes[**id].violations.is_empty())
            .count();
        let mut lines = vec![
            format!("scenario={}", self.scenario.name),
            format!("steps={}", self.scenario.steps),
            format!("nodes={}", self.nodes.len()),
            format!("leaves={}", self.terminal_nodes.len()),
            format!("safe_leaves={safe_leaves}"),
            format!("max_width={}", self.max_width),
            format!(
                "input_mode={}",
                if self.scenario.choices.is_empty() {
                    "fixed-schedule"
                } else {
                    "configured-choices"
                }
            ),
            format!("invariants={}", self.scenario.invariants.len()),
            format!("violations={violation_nodes}"),
            format!(
                "result={}",
                if self.passed() {
                    "BOUNDED_SAFE"
                } else {
                    "UNSAFE"
                }
            ),
        ];
        for trace in self
            .counterexample_traces()
            .into_iter()
            .take(max_counterexamples)
        {
            let final_node = trace.last().expect("counterexample trace cannot be empty");
            lines.push(format!(
                "counterexample invariant={} node={}",
                final_node.violations.join(","),
                final_node.id
            ));
            for node in trace {
                let facts = visible_facts(include_internal, &node.facts);
                lines.push(format!(
                    "  w{} assertions={} facts={}",
                    node.step.unwrap_or(0),
                    render_atoms(&node.assertions),
                    render_atoms(&facts)
                ));
            }
        }
        lines.join("\n") + "\n"
    }

    pub fn render_dot(&self, include_internal: bool) -> String {
        let mut lines = vec![
            "digraph temporal_prolog {".to_string(),
            "  rankdir=LR;".to_string(),
            format!(
                "  graph [labelloc=t, label=\"{}\"];",
                dot_escape(&format!(
                    "{}: {}",
                    self.scenario.name,
                    if self.passed() {
                        "BOUNDED SAFE"
                    } else {
                        "UNSAFE"
                    }
                ))
            ),
            "  node [shape=box, fontname=\"monospace\"] ;".to_string(),
        ];
        let terminals = self.terminal_nodes.iter().copied().collect::<BTreeSet<_>>();
        for node in &self.nodes {
            if node.id == 0 {
                lines.push("  n0 [shape=ellipse, label=\"start\"];".into());
                continue;
            }
            let mut label_lines = vec![format!("w{}", node.step.unwrap_or(0))];
            label_lines.extend(
                visible_facts(include_internal, &node.facts)
                    .iter()
                    .map(canonical_atom),
            );
            label_lines.extend(node.violations.iter().map(|name| format!("! {name}")));
            let attributes = if !node.violations.is_empty() {
                ", color=\"#b91c1c\", penwidth=2, style=filled, fillcolor=\"#fee2e2\""
            } else if terminals.contains(&node.id) {
                ", peripheries=2"
            } else {
                ""
            };
            lines.push(format!(
                "  n{} [label=\"{}\"{}];",
                node.id,
                dot_escape(&label_lines.join("\n")),
                attributes
            ));
        }
        for node in self.nodes.iter().skip(1) {
            let parent = node.parent.expect("non-root nodes have parents");
            let assertion_label = node
                .assertions
                .iter()
                .map(canonical_atom)
                .collect::<Vec<_>>()
                .join(",");
            let attribute = if assertion_label.is_empty() {
                String::new()
            } else {
                format!(" [label=\"{}\"]", dot_escape(&assertion_label))
            };
            lines.push(format!("  n{parent} -> n{}{};", node.id, attribute));
        }
        lines.push("}".into());
        lines.join("\n") + "\n"
    }
}

fn input_variants(fixed: &[Atom], groups: &[ChoiceGroup]) -> Vec<Vec<Atom>> {
    let mut variants = vec![fixed.to_vec()];
    for group in groups {
        let mut expanded = Vec::new();
        for prefix in variants {
            for alternative in &group.alternatives {
                let mut next = prefix.clone();
                if let ChoiceAlternative::Atom(atom) = alternative {
                    next.push(atom.clone());
                }
                expanded.push(next);
            }
        }
        variants = expanded;
    }
    variants
}

fn visible_facts(include_internal: bool, facts: &[Atom]) -> Vec<Atom> {
    facts
        .iter()
        .filter(|atom| include_internal || !internal_atom(atom))
        .cloned()
        .collect()
}

fn internal_atom(atom: &Atom) -> bool {
    atom.name == "true" || atom.name == "at" || generated_auxiliary(&atom.name)
}

fn generated_auxiliary(name: &str) -> bool {
    let digits = name
        .chars()
        .rev()
        .take_while(|character| character.is_ascii_digit())
        .count();
    digits > 0 && name[..name.len() - digits].ends_with("_aux")
}

fn render_atoms(atoms: &[Atom]) -> String {
    format!(
        "[{}]",
        atoms
            .iter()
            .map(canonical_atom)
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn canonical_atom(atom: &Atom) -> String {
    if atom.terms.is_empty() {
        atom.name.clone()
    } else {
        format!(
            "{}({})",
            atom.name,
            atom.terms
                .iter()
                .map(canonical_term)
                .collect::<Vec<_>>()
                .join(",")
        )
    }
}

fn canonical_term(term: &Term) -> String {
    match term {
        Term::Var(variable) => variable.clone(),
        Term::Fun(name, terms) if name == "[]" && terms.is_empty() => "[]".into(),
        Term::Fun(name, terms) if name == "." && terms.len() == 2 => {
            format!(
                "[{}{}]",
                canonical_term(&terms[0]),
                canonical_list_tail(&terms[1])
            )
        }
        Term::Fun(name, terms) if terms.is_empty() => name.clone(),
        Term::Fun(name, terms) => format!(
            "{}({})",
            name,
            terms
                .iter()
                .map(canonical_term)
                .collect::<Vec<_>>()
                .join(",")
        ),
        Term::Prev(term) => format!("@{}", canonical_term(term)),
    }
}

fn canonical_list_tail(term: &Term) -> String {
    match term {
        Term::Fun(name, terms) if name == "[]" && terms.is_empty() => String::new(),
        Term::Fun(name, terms) if name == "." && terms.len() == 2 => {
            format!(
                ",{}{}",
                canonical_term(&terms[0]),
                canonical_list_tail(&terms[1])
            )
        }
        _ => format!("|{}", canonical_term(term)),
    }
}

fn dot_escape(input: &str) -> String {
    input
        .chars()
        .map(|character| match character {
            '\\' => "\\\\".to_string(),
            '"' => "\\\"".to_string(),
            '\n' => "\\n".to_string(),
            _ => character.to_string(),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{compile, parse_scenario};

    #[test]
    fn finds_a_counterexample_and_renders_it() {
        let scenario = parse_scenario(
            "test.tpmc",
            "name unsafe\nprogram ignored.tpl\nsteps 1\n\
             invariant no_bad forbids bad\n",
        )
        .unwrap();
        let result = run_model_check(&scenario, compile("bad.").unwrap()).unwrap();
        assert!(!result.passed());
        assert_eq!(result.counterexample_traces().len(), 1);
        assert!(result.render_summary(1, false).contains("result=UNSAFE"));
        assert!(result.render_dot(false).contains("fillcolor=\"#fee2e2\""));
    }
}
