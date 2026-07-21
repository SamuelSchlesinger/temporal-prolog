use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use temporal_prolog::{compile, parse_scenario, run_model_check};

struct Options {
    scenario: PathBuf,
    dot: Option<PathBuf>,
    counterexamples: usize,
    include_internal: bool,
}

fn main() {
    match run() {
        Ok(code) => std::process::exit(code),
        Err(error) => {
            eprintln!("error: {error}");
            std::process::exit(1);
        }
    }
}

fn run() -> Result<i32, String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    if arguments
        .iter()
        .any(|argument| matches!(argument.as_str(), "-h" | "--help"))
    {
        print_help();
        return Ok(0);
    }
    let options = parse_options(arguments)?;
    let scenario_source = read_text(&options.scenario)?;
    let scenario_name = options.scenario.display().to_string();
    let scenario = parse_scenario(&scenario_name, &scenario_source)?;
    let configured_program = Path::new(&scenario.program);
    let program_path = if configured_program.is_absolute() {
        configured_program.to_path_buf()
    } else {
        options
            .scenario
            .canonicalize()
            .map_err(|error| format!("cannot resolve {}: {error}", options.scenario.display()))?
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .join(configured_program)
    };
    let program = compile(&read_text(&program_path)?)?;
    let result = run_model_check(&scenario, program)?;
    print!(
        "{}",
        result.render_summary(options.counterexamples, options.include_internal)
    );
    if let Some(path) = options.dot {
        fs::write(&path, result.render_dot(options.include_internal))
            .map_err(|error| format!("cannot write {}: {error}", path.display()))?;
        println!("dot={}", path.display());
    }
    Ok(if result.passed() { 0 } else { 2 })
}

fn parse_options(arguments: Vec<String>) -> Result<Options, String> {
    let mut scenario = None;
    let mut dot = None;
    let mut counterexamples = 3;
    let mut include_internal = false;
    let mut index = 0;
    while index < arguments.len() {
        match arguments[index].as_str() {
            "--dot" => {
                index += 1;
                let value = arguments.get(index).ok_or("--dot requires a path")?;
                dot = Some(PathBuf::from(value));
            }
            "--counterexamples" => {
                index += 1;
                let value = arguments
                    .get(index)
                    .ok_or("--counterexamples requires an integer")?;
                counterexamples = value
                    .parse()
                    .map_err(|_| "--counterexamples requires a non-negative integer")?;
            }
            "--include-internal" => include_internal = true,
            argument if argument.starts_with('-') => {
                return Err(format!("unknown option {argument:?}"));
            }
            argument => {
                if scenario.replace(PathBuf::from(argument)).is_some() {
                    return Err("only one scenario file may be supplied".into());
                }
            }
        }
        index += 1;
    }
    Ok(Options {
        scenario: scenario
            .ok_or_else(|| "usage: temporal-prolog-check-rs SCENARIO [OPTIONS]".to_string())?,
        dot,
        counterexamples,
        include_internal,
    })
}

fn read_text(path: &Path) -> Result<String, String> {
    fs::read_to_string(path).map_err(|error| format!("cannot read {}: {error}", path.display()))
}

fn print_help() {
    println!("Temporal Prolog bounded protocol model checker");
    println!("usage: temporal-prolog-check-rs SCENARIO [OPTIONS]");
    println!();
    println!("  --dot PATH             write the explored tree as Graphviz DOT");
    println!("  --counterexamples N    print at most N traces (default: 3)");
    println!("  --include-internal     include normalizer-generated facts");
    println!("  -h, --help             show this help");
}
