use vstd::arithmetic::power::pow;
use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i64, mutation_kind: u8) -> (result: i64)
    requires
        1i64 <= seed <= 1_000_000_000_000_000i64,
    ensures
        1 <= result <= pow(10, 15),
{
    reveal(pow);
    assert(pow(10, 15) == 1_000_000_000_000_000) by {
        reveal(pow);
        assert(pow(10, 0) == 1);
        assert(pow(10, 1) == 10);
        assert(pow(10, 2) == 100);
        assert(pow(10, 3) == 1000);
        assert(pow(10, 4) == 10000);
        assert(pow(10, 5) == 100000);
        assert(pow(10, 6) == 1000000);
        assert(pow(10, 7) == 10000000);
        assert(pow(10, 8) == 100000000);
        assert(pow(10, 9) == 1000000000);
        assert(pow(10, 10) == 10000000000);
        assert(pow(10, 11) == 100000000000);
        assert(pow(10, 12) == 1000000000000);
        assert(pow(10, 13) == 10000000000000);
        assert(pow(10, 14) == 100000000000000);
        assert(pow(10, 15) == 1000000000000000);
    };
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 1_000_000_000_000_000 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 {
        // halve (clamped to >= 1)
        let h = seed / 2;
        if h < 1 { 1 } else { h }
    } else if mutation_kind == 4 {
        // double (clamped to max)
        if seed <= 500_000_000_000_000 {
            seed * 2
        } else {
            1_000_000_000_000_000
        }
    } else if mutation_kind == 5 {
        // min boundary
        1
    } else if mutation_kind == 6 {
        // max boundary
        1_000_000_000_000_000
    } else if mutation_kind == 7 {
        // small boundary
        2
    } else if mutation_kind == 8 {
        // near-max boundary
        999_999_999_999_999
    } else if mutation_kind == 9 {
        // square root region
        let s = 1_000_000_000i64;
        if seed <= s { seed } else { s }
    } else {
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    // Example inputs from description
    let example_seeds: Vec<i64> = vec![1, 4, 50];

    // Interesting seed pool
    let mut seeds: Vec<i64> = example_seeds.clone();
    // Small values
    seeds.extend_from_slice(&[2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 15, 20, 50, 100]);
    // Powers of 10
    let mut p: i64 = 1;
    while p <= 1_000_000_000_000_000 {
        seeds.push(p);
        if p > 1 {
            seeds.push(p - 1);
        }
        if p < 1_000_000_000_000_000 {
            seeds.push(p + 1);
        }
        p = p.saturating_mul(10);
    }
    // Powers of 2
    let mut p2: i64 = 1;
    while p2 <= 1_000_000_000_000_000 {
        seeds.push(p2);
        p2 = p2.saturating_mul(2);
    }
    // Boundaries
    seeds.push(1_000_000_000_000_000);
    seeds.push(999_999_999_999_999);

    // Iterate seed pool with all mutation kinds
    for &s in &seeds {
        for mk in 0..=10u8 {
            if total >= count { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::count_good_numbers(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                total += 1;
            }
        }
        if total >= count { break; }
    }

    // Fill remaining with random seeds + random mutations
    while total < count {
        // Use size classes for diverse coverage
        let s = match total % 5 {
            0 => rng.gen_range_i64(1, 10),                            // tiny
            1 => rng.gen_range_i64(1, 1000),                          // small
            2 => rng.gen_range_i64(1000, 1_000_000),                  // medium
            3 => rng.gen_range_i64(1_000_000, 1_000_000_000),         // large
            _ => rng.gen_range_i64(1_000_000_000, 1_000_000_000_000_000), // max
        };
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::count_good_numbers(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            total += 1;
        }
    }
}
