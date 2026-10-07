use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: usize, mutation_kind: u8) -> (result: usize)
    requires
        1 <= seed <= 100000,
    ensures
        1 <= result <= 100000,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 100000 {
        seed + 1                                      // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                      // nudge down
    } else if mutation_kind == 3 {
        if seed <= 50000 {
            seed * 2                                  // double (clamped)
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        let h = seed / 2;
        if h >= 1 { h } else { 1 }                   // halve
    } else if mutation_kind == 5 {
        1                                             // min boundary
    } else if mutation_kind == 6 {
        100000                                        // max boundary
    } else if mutation_kind == 7 {
        50000                                         // midpoint
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
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
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
    let mut written = 0usize;

    // Example inputs from description.md
    let example_seeds: Vec<usize> = vec![3, 4];

    // Interesting seed pool
    let seed_pool: Vec<usize> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        99, 100, 101, 999, 1000, 1001,
        49999, 50000, 50001,
        99999, 100000,
    ];

    // Write example cases first
    for &n in &example_seeds {
        if seen.insert(n) {
            let res = Solution::almost_equal(n);
            if res.is_empty() {
                writeln!(out, "{}", json!({"input": {"n": n}, "output": "NO"})).unwrap();
            } else {
                let parts: Vec<i64> = res;
                writeln!(out, "{}", json!({"input": {"n": n}, "output": parts})).unwrap();
            }
            written += 1;
        }
    }

    // Seed pool × mutations
    let num_mutations: u8 = 8;
    for &s in &seed_pool {
        for mk in 0..num_mutations {
            if written >= count { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let res = Solution::almost_equal(n);
                if res.is_empty() {
                    writeln!(out, "{}", json!({"input": {"n": n}, "output": "NO"})).unwrap();
                } else {
                    let parts: Vec<i64> = res;
                    writeln!(out, "{}", json!({"input": {"n": n}, "output": parts})).unwrap();
                }
                written += 1;
            }
        }
        if written >= count { break; }
    }

    // Fill remaining with random seeds and mutations
    let mut _attempts_0 = 0usize;
    while written < count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        // Size classes for diversity
        let n_seed: usize = match written % 5 {
            0 => rng.gen_range_usize(1, 5),           // tiny
            1 => rng.gen_range_usize(1, 50),          // small
            2 => rng.gen_range_usize(51, 1000),       // medium
            3 => rng.gen_range_usize(1001, 10000),    // large
            _ => rng.gen_range_usize(10001, 100000),  // max
        };
        let mk = rng.gen_u8();
        let n = generate_test_case(n_seed, mk);
        if seen.insert(n) {
            let res = Solution::almost_equal(n);
            if res.is_empty() {
                writeln!(out, "{}", json!({"input": {"n": n}, "output": "NO"})).unwrap();
            } else {
                let parts: Vec<i64> = res;
                writeln!(out, "{}", json!({"input": {"n": n}, "output": parts})).unwrap();
            }
            written += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", written, out_path);
}
