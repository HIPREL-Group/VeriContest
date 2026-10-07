use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 100_000,
    ensures
        1 <= result <= 100_000,
{
    if mutation_kind == 0 {
        seed                                              // identity
    } else if mutation_kind == 1 && seed < 100_000 {
        seed + 1                                          // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                          // nudge down
    } else if mutation_kind == 3 {
        if seed <= 50_000 {
            seed * 2                                      // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        seed / 2 + 1                                      // halve (stay >= 1)
    } else if mutation_kind == 5 {
        1                                                 // min boundary
    } else if mutation_kind == 6 {
        100_000                                           // max boundary
    } else if mutation_kind == 7 {
        if seed % 2 == 1 { seed } else if seed < 100_000 { seed + 1 } else { seed - 1 }
                                                          // force odd
    } else if mutation_kind == 8 {
        if seed % 2 == 0 { seed } else if seed < 100_000 { seed + 1 } else { seed - 1 }
                                                          // force even
    } else if mutation_kind == 9 {
        if 100_000 - seed + 1 >= 1 { 100_000 - seed + 1 } else { seed }
                                                          // mirror
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut generated = 0usize;

    // Example inputs from description.md
    let examples: Vec<i32> = vec![1, 2, 3, 4];

    // Interesting seed pool
    let seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10,           // small
        99, 100, 101, 999, 1000, 1001,             // medium boundaries
        49999, 50000, 50001,                        // midpoint
        99998, 99999, 100000,                       // max boundary
        11, 13, 15, 17, 19,                         // small odd
        12, 14, 16, 18, 20,                         // small even
    ];

    // First emit example inputs
    for &n in &examples {
        if generated >= count { break; }
        if seen.insert(n) {
            let output = Solution::matching_numbers(n);
            let output_json = match &output {
                None => json!(null),
                Some(v) => {
                    let pairs: Vec<Vec<i32>> = v.iter().map(|&(a, b)| vec![a, b]).collect();
                    json!(pairs)
                }
            };
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output_json})).unwrap();
            generated += 1;
        }
    }

    // Then seed pool × mutations
    for &s in &seeds {
        for mk in 0..=10u8 {
            if generated >= count { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::matching_numbers(n);
                let output_json = match &output {
                    None => json!(null),
                    Some(v) => {
                        let pairs: Vec<Vec<i32>> = v.iter().map(|&(a, b)| vec![a, b]).collect();
                        json!(pairs)
                    }
                };
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output_json})).unwrap();
                generated += 1;
            }
        }
        if generated >= count { break; }
    }

    // Fill remaining with random
    while generated < count {
        let s = rng.gen_range_i64(1, 100_000) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::matching_numbers(n);
            let output_json = match &output {
                None => json!(null),
                Some(v) => {
                    let pairs: Vec<Vec<i32>> = v.iter().map(|&(a, b)| vec![a, b]).collect();
                    json!(pairs)
                }
            };
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output_json})).unwrap();
            generated += 1;
        }
    }
}
