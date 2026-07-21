use crate::{parse_atom, Atom};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Invariant {
    pub name: String,
    pub forbidden: Atom,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ChoiceAlternative {
    Atom(Atom),
    None,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ChoiceGroup {
    pub name: String,
    pub alternatives: Vec<ChoiceAlternative>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Scenario {
    pub name: String,
    pub program: String,
    pub steps: usize,
    pub assertions: BTreeMap<usize, Vec<Atom>>,
    pub choices: BTreeMap<usize, Vec<ChoiceGroup>>,
    pub invariants: Vec<Invariant>,
}

#[derive(Default)]
struct PartialScenario {
    name: Option<String>,
    program: Option<String>,
    steps: Option<usize>,
    assertions: BTreeMap<usize, Vec<Atom>>,
    choices: BTreeMap<usize, Vec<ChoiceGroup>>,
    invariants: Vec<Invariant>,
    invariant_names: BTreeSet<String>,
}

/// Parse the portable line-oriented `.tpmc` scenario format shared with the
/// Haskell implementation.
pub fn parse_scenario(source_name: &str, source: &str) -> Result<Scenario, String> {
    let mut partial = PartialScenario::default();
    for (index, original) in source.lines().enumerate() {
        let line_number = index + 1;
        let line = original.split('%').next().unwrap_or_default().trim();
        if line.is_empty() {
            continue;
        }
        parse_directive(line_number, line, &mut partial)
            .map_err(|error| format!("{source_name}:{line_number}: {error}"))?;
    }

    let name = partial
        .name
        .ok_or_else(|| "missing required 'name' directive".to_string())?;
    let program = partial
        .program
        .ok_or_else(|| "missing required 'program' directive".to_string())?;
    let steps = partial
        .steps
        .ok_or_else(|| "missing required 'steps' directive".to_string())?;
    if steps == 0 {
        return Err("steps must be a positive integer".into());
    }
    for step in partial.assertions.keys() {
        if *step >= steps {
            return Err(format!(
                "assertion step {step} is outside the {steps}-world horizon"
            ));
        }
    }
    for (step, groups) in &partial.choices {
        if *step >= steps {
            return Err(format!(
                "choice step {step} is outside the {steps}-world horizon"
            ));
        }
        for group in groups {
            if group.alternatives.len() < 2 {
                return Err(format!(
                    "choice group '{}' at step {step} must have at least two alternatives",
                    group.name
                ));
            }
        }
    }

    Ok(Scenario {
        name,
        program,
        steps,
        assertions: partial.assertions,
        choices: partial.choices,
        invariants: partial.invariants,
    })
}

fn parse_directive(
    line_number: usize,
    line: &str,
    partial: &mut PartialScenario,
) -> Result<(), String> {
    let (directive, rest) = split_word(line);
    match directive {
        "name" => {
            let value = exactly_one("name", rest)?;
            if !valid_name(value) {
                return Err("scenario names may contain only letters, digits, '_' and '-'".into());
            }
            if partial.name.replace(value.to_string()).is_some() {
                return Err("duplicate 'name' directive".into());
            }
        }
        "program" => {
            if rest.is_empty() {
                return Err("program requires a relative or absolute path".into());
            }
            if partial.program.replace(rest.to_string()).is_some() {
                return Err("duplicate 'program' directive".into());
            }
        }
        "steps" => {
            let value = exactly_one("steps", rest)?;
            let steps = value
                .parse::<usize>()
                .map_err(|_| "steps requires a positive integer")?;
            if partial.steps.replace(steps).is_some() {
                return Err("duplicate 'steps' directive".into());
            }
        }
        "assert" => {
            let (step, atom_source) = split_word(rest);
            if step.is_empty() || atom_source.is_empty() {
                return Err("assert requires STEP and ATOM".into());
            }
            let step = step
                .parse::<usize>()
                .map_err(|_| "assert step must be an integer")?;
            let atom = parse_atom(atom_source)
                .map_err(|error| format!("invalid atom on scenario line {line_number}: {error}"))?;
            if !atom.ground() {
                return Err("scheduled assertions must be ground".into());
            }
            partial.assertions.entry(step).or_default().push(atom);
        }
        "choose" => {
            let (step, after_step) = split_word(rest);
            let (group_name, alternative_source) = split_word(after_step);
            if step.is_empty() || group_name.is_empty() || alternative_source.is_empty() {
                return Err("choose requires STEP GROUP and ATOM or 'none'".into());
            }
            let step = step
                .parse::<usize>()
                .map_err(|_| "choose step must be an integer")?;
            if !valid_name(group_name) {
                return Err(
                    "choice group names may contain only letters, digits, '_' and '-'".into(),
                );
            }
            let alternative = if alternative_source == "none" {
                ChoiceAlternative::None
            } else {
                let atom = parse_atom(alternative_source).map_err(|error| {
                    format!("invalid atom on scenario line {line_number}: {error}")
                })?;
                if !atom.ground() {
                    return Err("choice alternatives must be ground".into());
                }
                ChoiceAlternative::Atom(atom)
            };
            add_choice(&mut partial.choices, step, group_name, alternative)?;
        }
        "invariant" => {
            let (name, after_name) = split_word(rest);
            let (keyword, atom_source) = split_word(after_name);
            if name.is_empty() || keyword != "forbids" || atom_source.is_empty() {
                return Err("invariant requires NAME forbids ATOM".into());
            }
            if !valid_name(name) {
                return Err("invariant names may contain only letters, digits, '_' and '-'".into());
            }
            if !partial.invariant_names.insert(name.to_string()) {
                return Err(format!("duplicate invariant name '{name}'"));
            }
            let forbidden = parse_atom(atom_source)
                .map_err(|error| format!("invalid atom on scenario line {line_number}: {error}"))?;
            partial.invariants.push(Invariant {
                name: name.to_string(),
                forbidden,
            });
        }
        _ => return Err(format!("unknown directive '{directive}'")),
    }
    Ok(())
}

fn add_choice(
    choices: &mut BTreeMap<usize, Vec<ChoiceGroup>>,
    step: usize,
    group_name: &str,
    alternative: ChoiceAlternative,
) -> Result<(), String> {
    let groups = choices.entry(step).or_default();
    if let Some(group) = groups.iter_mut().find(|group| group.name == group_name) {
        if group.alternatives.contains(&alternative) {
            return Err(format!(
                "duplicate alternative in choice group '{group_name}'"
            ));
        }
        group.alternatives.push(alternative);
    } else {
        groups.push(ChoiceGroup {
            name: group_name.to_string(),
            alternatives: vec![alternative],
        });
    }
    Ok(())
}

fn exactly_one<'a>(directive: &str, rest: &'a str) -> Result<&'a str, String> {
    let mut values = rest.split_whitespace();
    let value = values
        .next()
        .ok_or_else(|| format!("{directive} requires exactly one value"))?;
    if values.next().is_some() {
        return Err(format!("{directive} requires exactly one value"));
    }
    Ok(value)
}

fn valid_name(name: &str) -> bool {
    !name.is_empty()
        && name
            .chars()
            .all(|character| character.is_alphanumeric() || matches!(character, '_' | '-'))
}

fn split_word(input: &str) -> (&str, &str) {
    let input = input.trim_start();
    input
        .find(char::is_whitespace)
        .map_or((input, ""), |index| {
            let (word, rest) = input.split_at(index);
            (word, rest.trim())
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_portable_scenario() {
        let scenario = parse_scenario(
            "test.tpmc",
            "name demo\nprogram demo.tpl\nsteps 2\nassert 0 request(1)\n\
             invariant safe forbids violation(X)\n",
        )
        .unwrap();
        assert_eq!(scenario.name, "demo");
        assert_eq!(scenario.steps, 2);
        assert_eq!(scenario.assertions[&0].len(), 1);
        assert_eq!(scenario.invariants.len(), 1);
    }

    #[test]
    fn parses_independent_choice_groups() {
        let scenario = parse_scenario(
            "test.tpmc",
            "name demo\nprogram demo.tpl\nsteps 2\n\
             choose 1 p1 yes(p1)\nchoose 1 p1 no(p1)\n\
             choose 1 p2 yes(p2)\nchoose 1 p2 none\n",
        )
        .unwrap();
        assert_eq!(scenario.choices[&1].len(), 2);
        assert_eq!(scenario.choices[&1][0].alternatives.len(), 2);
    }

    #[test]
    fn rejects_out_of_horizon_assertion() {
        let error = parse_scenario(
            "test.tpmc",
            "name demo\nprogram demo.tpl\nsteps 1\nassert 1 request\n",
        )
        .unwrap_err();
        assert!(error.contains("outside"));
    }
}
