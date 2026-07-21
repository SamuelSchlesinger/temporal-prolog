use std::collections::BTreeMap;
use std::env;
use std::fs;
use temporal_prolog::{compile, parse_atom, render_batch, run_batch, BatchOptions};

fn main() {
    if let Err(error) = run() {
        eprintln!("error: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut args = env::args().skip(1);
    let Some(filename) = args.next() else {
        print_help();
        return Ok(());
    };
    if filename == "--help" || filename == "-h" {
        print_help();
        return Ok(());
    }
    let mut steps = 1usize;
    let mut assertions: BTreeMap<usize, Vec<temporal_prolog::Atom>> = BTreeMap::new();
    let mut include_internal = false;
    while let Some(option) = args.next() {
        match option.as_str() {
            "--steps" => {
                steps = args
                    .next()
                    .ok_or("--steps requires an integer")?
                    .parse()
                    .map_err(|_| "invalid --steps value")?;
            }
            "--assert" => {
                let value = args.next().ok_or("--assert requires STEP:ATOM")?;
                let (step, atom) = value.split_once(':').ok_or("assertion must be STEP:ATOM")?;
                let step: usize = step.parse().map_err(|_| "invalid assertion step")?;
                assertions.entry(step).or_default().push(parse_atom(atom)?);
            }
            "--include-internal" => include_internal = true,
            unknown => return Err(format!("unknown option {unknown:?}")),
        }
    }

    let source = fs::read_to_string(&filename)
        .map_err(|error| format!("cannot read {filename}: {error}"))?;
    let program = compile(&source)?;
    let result = run_batch(
        BatchOptions {
            steps,
            assertions,
            include_internal,
        },
        program,
    )?;
    print!("{}", render_batch(&result));
    Ok(())
}

fn print_help() {
    println!("Temporal Prolog batch runner");
    println!("usage: temporal-prolog-rs PROGRAM [--steps N] [--assert STEP:ATOM]...");
    println!("                          [--include-internal]");
    println!("all minimal branches and their complete world histories are printed");
}
