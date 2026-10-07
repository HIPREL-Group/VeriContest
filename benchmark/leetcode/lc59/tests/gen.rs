use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    ensures
        1 <= result <= 20,
{
    let seed = if seed < 1 { 1 } else if seed > 20 { 20 } else { seed };
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 20 {
        (seed + 1) as i32                             // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        (seed - 1) as i32                             // nudge down
    } else if mutation_kind == 3 {
        if seed <= 10 {
            (seed * 2) as i32                         // double (clamped)
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        if seed >= 2 {
            (seed / 2 + if seed / 2 < 1 { 1i32 } else { 0i32 }) as i32  // halve (floor >= 1)
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        1                                             // min boundary
    } else if mutation_kind == 6 {
        20                                            // max boundary
    } else if mutation_kind == 7 {
        10                                            // midpoint
    } else if mutation_kind == 8 {
        21 - seed                                     // mirror around center
    } else {
        seed                                          // fallback
    }
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
    let mut emitted = 0usize;

    // Example inputs from description.md
    let examples: Vec<i32> = vec![3, 1];

    // Seed pool: all valid n values 1..=20 plus examples
    let mut seed_pool: Vec<i32> = (1..=20).collect();
    for &ex in &examples {
        if !seed_pool.contains(&ex) {
            seed_pool.push(ex);
        }
    }

    let num_mutations: u8 = 9;

    // First pass: seed pool × all mutations
    for &s in &seed_pool {
        for mk in 0..=num_mutations {
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let matrix = Solution::generate_matrix(n);
                writeln!(out, "{}", json!({
                    "input": {"n": n},
                    "output": matrix
                })).unwrap();
                emitted += 1;
            }
        }
    }

    // Second pass: random seeds + random mutations to reach count
    while emitted < count {
        let s = rng.gen_range_i64(1, 20) as i32;
        let mk = rng.gen_u8() % (num_mutations + 1);
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let matrix = Solution::generate_matrix(n);
            writeln!(out, "{}", json!({
                "input": {"n": n},
                "output": matrix
            })).unwrap();
            emitted += 1;
        }
        // Since n ∈ [1,20], we can have at most 20 unique values
        if seen.len() >= 20 {
            break;
        }
    }

    eprintln!("Generated {} test cases to {:?}", emitted, out_path);
}
