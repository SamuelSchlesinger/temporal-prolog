use std::collections::BTreeMap;
use std::env;
use std::fs;
use temporal_prolog::{compile, parse_atom, semantic_digest, Interpreter};

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
            unknown => return Err(format!("unknown option {unknown:?}")),
        }
    }

    let source = fs::read_to_string(&filename)
        .map_err(|error| format!("cannot read {filename}: {error}"))?;
    let program = compile(&source)?;
    let mut branches = vec![Interpreter::new(program)];
    for step in 0..steps {
        let mut next = Vec::new();
        for mut branch in branches {
            for atom in assertions.get(&step).into_iter().flatten() {
                branch.assert(atom.clone())?;
            }
            next.extend(branch.step_all()?);
        }
        branches = next;
    }
    println!("branches={}", branches.len());
    for (index, branch) in branches.iter().enumerate() {
        println!("branch {index}:");
        if let Some(world) = branch.world() {
            for atom in world.iter().filter(|atom| {
                atom.name != "at" && atom.name != "true" && !atom.name.contains("_aux")
            }) {
                println!("  {atom}");
            }
        }
        println!("  digest={}", semantic_digest(&branch.worlds));
    }
    Ok(())
}

fn print_help() {
    println!("Temporal Prolog Rust batch runner");
    println!("usage: temporal-prolog-rs PROGRAM [--steps N] [--assert STEP:ATOM]...");
    println!("all minimal branches are printed; assertions are zero-indexed by world");
}
