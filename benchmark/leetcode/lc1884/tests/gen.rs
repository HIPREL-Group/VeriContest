use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1i32 <= seed <= 1000i32,
    ensures
        1i32 <= result <= 1000i32,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 1000 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 && seed <= 500 {
        // double
        seed * 2
    } else if mutation_kind == 4 {
        // halve (towards middle)
        seed / 2 + 1
    } else if mutation_kind == 5 {
        // min boundary
        1
    } else if mutation_kind == 6 {
        // max boundary
        1000
    } else if mutation_kind == 7 {
        // complement: 1001 - seed
        1001 - seed
    } else if mutation_kind == 8 {
        // quarter point
        250
    } else if mutation_kind == 9 {
        // three-quarter point
        750
    } else {
        // fallback: identity
        seed
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut generated = 0usize;

    // Example inputs from description.md
    let example_seeds: Vec<i32> = vec![2, 100];

    // Interesting seed pool: boundaries, small values, examples
    let mut seed_pool: Vec<i32> = vec![
        1, 2, 3, 4, 5, 10, 14, 15, 50, 100, 200, 250, 500, 750, 999, 1000,
    ];
    seed_pool.extend_from_slice(&example_seeds);
    seed_pool.sort();
    seed_pool.dedup();

    let num_mutations: u8 = 10;

    // Phase 1: seed pool × all mutations
    for &s in &seed_pool {
        for mk in 0..num_mutations {
            if generated >= count { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::two_egg_drop(n);
                writeln!(out, "{}", json!({
                    "input": {"n": n},
                    "output": output
                })).unwrap();
                generated += 1;
            }
        }
        if generated >= count { break; }
    }

    // Phase 2: random seeds × random mutations
    while generated < count {
        let s = rng.gen_range_i64(1, 1000) as i32;
        let mk = rng.gen_u8() % num_mutations;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::two_egg_drop(n);
            writeln!(out, "{}", json!({
                "input": {"n": n},
                "output": output
            })).unwrap();
            generated += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
