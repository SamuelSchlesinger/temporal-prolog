use crate::{semantic_digest, Atom, Interpreter, NormalizedProgram, Term};
use std::collections::BTreeMap;

/// Finite execution horizon, scheduled inputs, and rendering visibility.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BatchOptions {
    /// Positive number of worlds to compute.
    pub steps: usize,
    /// Ground external facts indexed by zero-based world number.
    pub assertions: BTreeMap<usize, Vec<Atom>>,
    /// Whether rendered histories expose normalization auxiliaries.
    pub include_internal: bool,
}

impl Default for BatchOptions {
    fn default() -> Self {
        Self {
            steps: 1,
            assertions: BTreeMap::new(),
            include_internal: false,
        }
    }
}

/// Completed branch-preserving execution and its options.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BatchResult {
    pub options: BatchOptions,
    pub branches: Vec<Interpreter>,
}

/// Execute a finite schedule while preserving every minimal-model branch.
/// Inputs outside the selected horizon are errors rather than ignored data.
pub fn run_batch(options: BatchOptions, program: NormalizedProgram) -> Result<BatchResult, String> {
    validate_options(&options)?;
    let mut branches = vec![Interpreter::new(program)];
    for step in 0..options.steps {
        let mut next = Vec::new();
        for mut branch in branches {
            for atom in options.assertions.get(&step).into_iter().flatten() {
                branch.assert(atom.clone())?;
            }
            next.extend(branch.step_all()?);
        }
        next.sort_by(|left, right| left.worlds.cmp(&right.worlds));
        branches = next;
    }
    branches.sort_by(|left, right| left.worlds.cmp(&right.worlds));
    Ok(BatchResult { options, branches })
}

fn validate_options(options: &BatchOptions) -> Result<(), String> {
    if options.steps == 0 {
        return Err("steps must be a positive integer".into());
    }
    for (step, atoms) in &options.assertions {
        if *step >= options.steps {
            return Err(format!(
                "assertion step {step} is outside the {}-world run",
                options.steps
            ));
        }
        if atoms.iter().any(|atom| !atom.ground()) {
            return Err("assertions must be ground".into());
        }
    }
    Ok(())
}

/// Render the common deterministic, line-oriented batch format.
pub fn render_batch(result: &BatchResult) -> String {
    let mut output = format!(
        "steps={}\nbranches={}\n",
        result.options.steps,
        result.branches.len()
    );
    for (index, branch) in result.branches.iter().enumerate() {
        output.push_str(&format!("branch={index}\n"));
        for (world_number, world) in branch.worlds.iter().enumerate() {
            let facts = world
                .iter()
                .filter(|atom| {
                    result.options.include_internal
                        || !internal_atom(atom, &branch.program.auxiliary_predicates)
                })
                .map(canonical_atom)
                .collect::<Vec<_>>()
                .join(",");
            output.push_str(&format!("  w{world_number}=[{facts}]\n"));
        }
        output.push_str(&format!("  digest={}\n", semantic_digest(&branch.worlds)));
    }
    output
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

fn internal_atom(atom: &Atom, auxiliary_predicates: &std::collections::BTreeSet<String>) -> bool {
    atom.name == "true" || atom.name == "at" || auxiliary_predicates.contains(&atom.name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{compile, parse_atom};

    #[test]
    fn preserves_and_canonically_renders_all_branches() {
        let result = run_batch(
            BatchOptions::default(),
            compile("~a => b. ~b => a.").unwrap(),
        )
        .unwrap();
        assert_eq!(result.branches.len(), 2);
        assert_eq!(
            render_batch(&result),
            "steps=1\nbranches=2\n\
             branch=0\n  w0=[a]\n  digest=3ac3fa0d287999b7\n\
             branch=1\n  w0=[b]\n  digest=faa2015c6af3d282\n"
        );
    }

    #[test]
    fn rejects_unreachable_and_nonground_assertions() {
        let program = compile("ok.").unwrap();
        let mut unreachable = BatchOptions::default();
        unreachable
            .assertions
            .insert(1, vec![parse_atom("event").unwrap()]);
        assert!(run_batch(unreachable, program.clone()).is_err());

        let mut nonground = BatchOptions::default();
        nonground
            .assertions
            .insert(0, vec![parse_atom("event(X)").unwrap()]);
        assert!(run_batch(nonground, program).is_err());
    }

    #[test]
    fn source_aux_suffixes_remain_visible() {
        let mut options = BatchOptions {
            steps: 2,
            ..BatchOptions::default()
        };
        options
            .assertions
            .insert(0, vec![parse_atom("trigger").unwrap()]);
        let result = run_batch(
            options,
            compile("user_aux0. always_aux0. trigger => next generated.").unwrap(),
        )
        .unwrap();
        let rendered = render_batch(&result);
        assert!(rendered.contains("w0=[always_aux0,trigger,user_aux0]"));
        assert!(!rendered.contains("next_aux1"));
    }
}
