use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 10000,
    ensures
        1 <= result <= 10000,
{
    if mutation_kind == 0 {
        seed                                              // identity
    } else if mutation_kind == 1 && seed < 10000 {
        seed + 1                                          // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                          // nudge down
    } else if mutation_kind == 3 {
        if seed <= 5000 {
            seed * 2                                      // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        seed / 2 + 1                                      // halve (stay >= 1)
    } else if mutation_kind == 5 {
        1                                                 // min boundary
    } else if mutation_kind == 6 {
        10000                                             // max boundary
    } else if mutation_kind == 7 {
        if seed >= 1 && seed <= 10000 {
            10001 - seed                                  // mirror
        } else {
            seed
        }
    } else if mutation_kind == 8 {
        if seed <= 9999 && seed >= 2 {
            (seed + 1) / 2 + 1                            // shrink toward middle
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        5000                                              // midpoint
    } else {
        seed                                              // fallback
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
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Example inputs from description.md
    let example_seeds: Vec<i32> = vec![3, 6];
    for &n in &example_seeds {
        if count >= goal { break; }
        let result = generate_test_case(n, 0); // identity — use example directly
        if seen.insert(result) {
            let output = Solution::min_operations(result);
            writeln!(out, "{}", json!({"input": {"n": result}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Seed pool: boundary and interesting values
    let seed_pool: Vec<i32> = vec![
        1, 2, 3, 4, 5, 10, 50, 100, 500, 1000,
        5000, 9999, 10000, 7, 13, 42, 99, 101,
        2500, 7500, 333, 666, 1234, 4321, 8888,
    ];

    for &s in &seed_pool {
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::min_operations(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < goal {
        let s = rng.gen_range_i64(1, 10000) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::min_operations(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
