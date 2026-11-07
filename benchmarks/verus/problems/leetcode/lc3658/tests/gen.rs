use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 1_000i32,
    ensures
        1 <= result <= 1_000i32,
{
    if mutation_kind == 0 {
        seed                                              // identity
    } else if mutation_kind == 1 && seed < 1_000 {
        seed + 1                                          // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                          // nudge down
    } else if mutation_kind == 3 && seed <= 500 {
        seed * 2                                          // double
    } else if mutation_kind == 4 && seed >= 2 {
        let h = seed / 2;
        if h >= 1 { h } else { 1i32 }                    // halve
    } else if mutation_kind == 5 {
        1i32                                              // min boundary
    } else if mutation_kind == 6 {
        1_000i32                                          // max boundary
    } else if mutation_kind == 7 {
        500i32                                            // midpoint
    } else if mutation_kind == 8 && seed <= 333 {
        seed * 3                                          // triple
    } else if mutation_kind == 9 {
        if seed <= 100 {
            seed                                          // keep small
        } else if seed <= 500 {
            seed / 5 + 1                                  // compress to small range
        } else {
            seed                                          // keep large
        }
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
    let mut done = 0usize;

    // Seed pool: examples from description + boundary + interesting values
    let seeds: Vec<i32> = vec![
        4, 5,                                   // examples from description
        1, 2, 3,                                // small
        10, 50, 100, 250, 500, 750, 999, 1000,  // spread
        31, 32, 16, 64, 128, 256, 512,          // powers of 2
        7, 11, 13, 17, 19, 23, 29,              // primes
        6, 12, 24, 48, 96,                      // highly composite
    ];

    // Phase 1: seed pool × all mutation kinds
    for &s in &seeds {
        for mk in 0..=10u8 {
            if done >= count { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::gcd_of_odd_even_sums(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                done += 1;
            }
        }
        if done >= count { break; }
    }

    // Phase 2: random seeds + random mutations
    while done < count {
        let s = rng.gen_range_i64(1, 1000) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::gcd_of_odd_even_sums(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            done += 1;
        }
    }
}
