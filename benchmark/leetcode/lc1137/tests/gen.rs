use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn tribo_spec(n: nat) -> nat
        decreases n
    {
        if n <= 0 {
            0
        } else if n == 1 {
            1
        } else if n == 2 {
            1
        } else {
            Self::tribo_spec((n - 3) as nat) + Self::tribo_spec((n - 2) as nat) + Self::tribo_spec((n - 1) as nat)
        }
    }
}

proof fn tribo_bound_lemma(n: nat)
    requires n <= 37,
    ensures Solution::tribo_spec(n) <= i32::MAX as nat,
    decreases n,
{
    reveal_with_fuel(Solution::tribo_spec, 15);
    if n > 15 {
        tribo_bound_lemma((n - 1) as nat);
        tribo_bound_lemma((n - 2) as nat);
        tribo_bound_lemma((n - 3) as nat);
    }
}

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        0i32 <= seed <= 37i32,
    ensures
        0 <= result <= 37,
        Solution::tribo_spec(result as nat) <= i32::MAX,
{
    let n: i32 = if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed < 37 {
        seed + 1
    } else if mutation_kind == 2 && seed > 0 {
        seed - 1
    } else if mutation_kind == 3 {
        0
    } else if mutation_kind == 4 {
        37
    } else if mutation_kind == 5 {
        seed / 2
    } else {
        seed
    };
    proof {
        tribo_bound_lemma(n as nat);
    }
    n
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

#[allow(non_snake_case)]
mod solution_mod {
    pub struct Solution;
    include!("../code.rs");
}
use solution_mod::Solution as SolutionExec;

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut generated = 0usize;

    let mut emit = |n: i32, out: &mut std::io::BufWriter<std::fs::File>| {
        let output = SolutionExec::tribonacci(n);
        writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
    };

    // Example inputs
    let examples: Vec<i32> = vec![4, 25];
    for &n in &examples {
        if generated >= count { break; }
        emit(n, &mut out);
        generated += 1;
    }

    // Cover every value 0..=37
    for n in 0..=37i32 {
        if generated >= count { break; }
        let n = generate_test_case(n, 0);
        emit(n, &mut out);
        generated += 1;
    }

    // Seed pool with diverse mutations
    let seeds: Vec<i32> = vec![0, 1, 2, 5, 10, 15, 18, 20, 25, 30, 35, 37];
    for &s in &seeds {
        for mk in 1..=8u8 {
            if generated >= count { break; }
            let n = generate_test_case(s, mk);
            emit(n, &mut out);
            generated += 1;
        }
        if generated >= count { break; }
    }

    // Fill remaining with random seeds + mutations
    let mut _attempts = 0usize;
    while generated < count {
        _attempts += 1; if _attempts > 10000 { break; }
        let s = rng.gen_range_usize(0, 37) as i32;
        let mk = rng.gen_u8() % 9;
        let n = generate_test_case(s, mk);
        emit(n, &mut out);
        generated += 1;
    }
}
