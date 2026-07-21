use std::env;
use std::time::Instant;
use temporal_prolog::{compile, parse_atom, Atom, Interpreter};

fn main() -> Result<(), String> {
    let args: Vec<_> = env::args().skip(1).collect();
    let chain_length = argument(&args, 0, 50);
    let item_count = argument(&args, 1, 20);
    let iterations = argument(&args, 2, 100);
    let program = compile(&chain_source(chain_length))?;
    let expected = execute(&program, item_count, 0)?;
    let summary = semantic_summary(chain_length, item_count, &expected);
    let digest = fnv1a(&summary);

    let start = Instant::now();
    let mut guard = 0usize;
    for iteration in 1..=iterations {
        guard ^= execute(&program, item_count, iteration)?
            .world()
            .map_or(0, |world| world.len());
    }
    std::hint::black_box(guard);
    let elapsed_ms = start.elapsed().as_secs_f64() * 1000.0;
    println!(
        "implementation=rust workload=chain parameters=length:{chain_length},items:{item_count} \
         iterations={iterations} elapsed_ms={elapsed_ms} digest={digest}"
    );
    Ok(())
}

fn argument(args: &[String], index: usize, fallback: usize) -> usize {
    args.get(index)
        .and_then(|value| value.parse().ok())
        .unwrap_or(fallback)
}

fn chain_source(length: usize) -> String {
    let mut source = "seed(X) => p0(X).\n".to_string();
    for index in 1..=length {
        source.push_str(&format!("p{}(X) => p{index}(X).\n", index - 1));
    }
    source
}

fn execute(
    program: &temporal_prolog::NormalizedProgram,
    item_count: usize,
    salt: usize,
) -> Result<Interpreter, String> {
    let mut interpreter = Interpreter::new(program.clone());
    for index in 0..item_count {
        interpreter.assert(parse_atom(&format!("seed(item{salt}_{index})"))?)?;
    }
    interpreter.step()?;
    Ok(interpreter)
}

fn semantic_summary(length: usize, item_count: usize, interpreter: &Interpreter) -> String {
    let world = interpreter.world().expect("one benchmark world");
    let user_count = world
        .iter()
        .filter(|atom| atom.name != "at" && atom.name != "true")
        .count();
    let terminal = Atom::new(
        format!("p{length}"),
        vec![temporal_prolog::Term::Fun(
            format!("item0_{}", item_count - 1),
            vec![],
        )],
    );
    format!(
        "chain:{length}:{item_count}:{user_count}:{}",
        world.contains(&terminal)
    )
}

fn fnv1a(input: &str) -> String {
    let mut hash = 0xcbf29ce484222325u64;
    for byte in input.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    format!("{hash:016x}")
}
