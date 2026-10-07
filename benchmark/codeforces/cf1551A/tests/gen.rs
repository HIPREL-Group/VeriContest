use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i64, mutation_kind: u8) -> (result: i64)
    requires
        1 <= seed <= 1_000_000_000,
    ensures
        1 <= result <= 1_000_000_000,
{
    if mutation_kind == 0 {
        seed                                              // identity
    } else if mutation_kind == 1 && seed <= 999_999_999 {
        seed + 1                                          // nudge up
    } else if mutation_kind == 2 && seed >= 2 {
        seed - 1                                          // nudge down
    } else if mutation_kind == 3 {
        1                                                 // min boundary
    } else if mutation_kind == 4 {
        1_000_000_000                                     // max boundary
    } else if mutation_kind == 5 && seed <= 500_000_000 {
        seed * 2                                          // double (in range)
    } else if mutation_kind == 6 {
        let h = seed / 2;
        if h >= 1 {
            h                                             // halve
        } else {
            seed
        }
    } else if mutation_kind == 7 {
        500_000_000                                       // middle value
    } else if mutation_kind == 8 {
        // complement: 1_000_000_001 - seed
        let c = 1_000_000_001 - seed;
        if c >= 1 && c <= 1_000_000_000 {
            c
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        3                                                 // small value (for mod-3 boundary)
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

    // Example inputs from the problem description
    let examples: Vec<i64> = vec![1000, 30, 1, 32, 1_000_000_000, 5];

    // Emit example inputs first
    for &n in &examples {
        if generated >= count { break; }
        let result = generate_test_case(n, 0);
        if seen.insert(result) {
            let (c1, c2) = Solution::polycarp_coins(result);
            writeln!(out, "{}", json!({"input": {"n": result}, "output": [c1, c2]})).unwrap();
            generated += 1;
        }
    }

    // Fixed interesting seeds across mutation kinds
    let fixed_seeds: Vec<i64> = vec![
        1, 2, 3, 4, 5, 6, 9, 10, 100, 333, 999,
        1000, 10_000, 100_000, 1_000_000, 10_000_000,
        100_000_000, 500_000_000, 999_999_999, 1_000_000_000,
    ];

    for &s in &fixed_seeds {
        for mk in 0..=10u8 {
            if generated >= count { break; }
            let result = generate_test_case(s, mk);
            if seen.insert(result) {
                let (c1, c2) = Solution::polycarp_coins(result);
                writeln!(out, "{}", json!({"input": {"n": result}, "output": [c1, c2]})).unwrap();
                generated += 1;
            }
        }
        if generated >= count { break; }
    }

    // Fill remaining with random seeds and mutations
    while generated < count {
        // Use size classes for diversity
        let s = match rng.gen_u8() % 5 {
            0 => rng.gen_range_i64(1, 10),                    // tiny
            1 => rng.gen_range_i64(1, 1000),                  // small
            2 => rng.gen_range_i64(1001, 1_000_000),          // medium
            3 => rng.gen_range_i64(1_000_001, 100_000_000),   // large
            _ => rng.gen_range_i64(100_000_001, 1_000_000_000), // max
        };
        let mk = rng.gen_u8() % 11;
        let result = generate_test_case(s, mk);
        if seen.insert(result) {
            let (c1, c2) = Solution::polycarp_coins(result);
            writeln!(out, "{}", json!({"input": {"n": result}, "output": [c1, c2]})).unwrap();
            generated += 1;
        }
    }
}
