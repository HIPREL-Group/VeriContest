use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i64, mutation_kind: u8) -> (result: i64)
    requires
        1i64 <= seed <= 1_000_000_000_000_000i64,
    ensures
        1i64 <= result <= 1_000_000_000_000_000i64,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 1_000_000_000_000_000i64 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 1i64 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 {
        // double (clamped)
        if seed <= 500_000_000_000_000i64 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        // halve (clamped to min 1)
        let h = seed / 2;
        if h >= 1 {
            h
        } else {
            1i64
        }
    } else if mutation_kind == 5 {
        // min boundary
        1i64
    } else if mutation_kind == 6 {
        // max boundary
        1_000_000_000_000_000i64
    } else if mutation_kind == 7 {
        // square root region (small values)
        if seed <= 1000i64 {
            seed
        } else {
            1i64
        }
    } else if mutation_kind == 8 {
        // quarter
        let q = seed / 4;
        if q >= 1 {
            q
        } else {
            1i64
        }
    } else if mutation_kind == 9 {
        // triple (clamped)
        if seed <= 333_333_333_333_333i64 {
            seed * 3
        } else {
            seed
        }
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
    let count_goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Example inputs from description.md
    let example_seeds: Vec<i64> = vec![1, 13, 1_000_000_000];

    // Interesting seed pool: boundaries, powers, and varied magnitudes
    let mut seed_pool: Vec<i64> = vec![
        1, 2, 3, 4, 5, 10, 12, 13, 100, 1000,
        1_000_000_000,
        1_000_000_000_000_000,
        999_999_999_999_999,
        500_000_000_000_000,
        1_000_000,
        1_000_000_000_000,
    ];
    // Add example inputs
    for &e in &example_seeds {
        seed_pool.push(e);
    }
    // Powers of 10
    let mut p: i64 = 1;
    while p <= 1_000_000_000_000_000 {
        seed_pool.push(p);
        if p > 1 {
            seed_pool.push(p - 1);
        }
        if p < 1_000_000_000_000_000 {
            seed_pool.push(p + 1);
        }
        p *= 10;
    }
    // Powers of 2 within range
    let mut p2: i64 = 1;
    while p2 > 0 && p2 <= 1_000_000_000_000_000 {
        seed_pool.push(p2);
        p2 *= 2;
    }

    // Phase 1: deterministic seeds × all mutations
    for &s in &seed_pool {
        for mk in 0..=10u8 {
            if count >= count_goal { break; }
            let needed_apples = generate_test_case(s, mk);
            if seen.insert(needed_apples) {
                let output = Solution::minimum_perimeter(needed_apples);
                writeln!(out, "{}", json!({
                    "input": {"neededApples": needed_apples},
                    "output": output
                })).unwrap();
                count += 1;
            }
        }
        if count >= count_goal { break; }
    }

    // Phase 2: random seeds with random mutations
    while count < count_goal {
        // Use size classes for diversity
        let s = match count % 5 {
            0 => rng.gen_range_i64(1, 10),                          // tiny
            1 => rng.gen_range_i64(1, 1_000),                       // small
            2 => rng.gen_range_i64(1_000, 1_000_000),               // medium
            3 => rng.gen_range_i64(1_000_000, 1_000_000_000_000),   // large
            _ => rng.gen_range_i64(1_000_000_000_000, 1_000_000_000_000_000), // max
        };
        let mk = rng.gen_u8() % 11;
        let needed_apples = generate_test_case(s, mk);
        if seen.insert(needed_apples) {
            let output = Solution::minimum_perimeter(needed_apples);
            writeln!(out, "{}", json!({
                "input": {"neededApples": needed_apples},
                "output": output
            })).unwrap();
            count += 1;
        }
    }
}
