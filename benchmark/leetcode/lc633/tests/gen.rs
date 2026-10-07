use vstd::arithmetic::power::{lemma_square_is_pow2, pow};
use vstd::prelude::*;

verus! {

pub open spec fn judge_square_sum_spec(c: int) -> bool {
    exists|a: nat, b: nat| pow(a as int, 2) + pow(b as int, 2) == c
}

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        0 <= seed,
    ensures
        0 <= result,
{
    if mutation_kind == 0 {
        seed                                              // identity
    } else if mutation_kind == 1 && seed < i32::MAX {
        seed + 1                                          // nudge up
    } else if mutation_kind == 2 && seed > 0 {
        seed - 1                                          // nudge down
    } else if mutation_kind == 3 {
        if seed >= -1_073_741_824 && seed <= 1_073_741_823 {
            seed * 2                                      // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        seed / 2                                          // halve
    } else if mutation_kind == 5 {
        0                                                 // zero
    } else if mutation_kind == 6 {
        i32::MAX                                          // max boundary
    } else if mutation_kind == 7 {
        1                                                 // one
    } else if mutation_kind == 8 {
        2                                                 // small prime
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
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
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

    // Seed pool: examples from description, perfect squares, sums of squares,
    // boundary values, and interesting values
    let seeds: Vec<i32> = vec![
        // Examples from description.md
        5, 3,
        // Boundary values
        0, 1, 2, i32::MAX,
        // Perfect squares
        4, 9, 16, 25, 36, 49, 64, 100, 10000, 1000000,
        // Sums of two squares
        8, 10, 13, 17, 20, 29, 34, 50, 65, 85, 125, 130,
        // Non-sums of two squares
        6, 7, 11, 12, 14, 15, 19, 21, 22, 23, 24, 27, 28, 30, 31,
        // Large values
        2_000_000_000, 1_999_999_999, 1_500_000_000, 1_000_000_000,
        // Near powers of 2
        1024, 1023, 1025, 2048, 2047, 4096,
    ];

    for &s in &seeds {
        for mk in 0..=9u8 {
            if count >= goal { break; }
            let c = generate_test_case(s, mk);
            if seen.insert(c) {
                let output = Solution::judge_square_sum(c);
                writeln!(out, "{}", json!({"input": {"c": c}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    while count < goal {
        // Mix size classes for diverse values
        let s = match count % 5 {
            0 => rng.gen_range_i64(0, 10) as i32,                   // tiny
            1 => rng.gen_range_i64(0, 1000) as i32,                 // small
            2 => rng.gen_range_i64(1000, 1_000_000) as i32,         // medium
            3 => rng.gen_range_i64(1_000_000, 1_000_000_000) as i32, // large
            _ => rng.gen_range_i64(0, i32::MAX as i64) as i32,      // full range
        };
        let mk = rng.gen_u8() % 10;
        let c = generate_test_case(s, mk);
        if seen.insert(c) {
            let output = Solution::judge_square_sum(c);
            writeln!(out, "{}", json!({"input": {"c": c}, "output": output})).unwrap();
            count += 1;
        }
    }
}
