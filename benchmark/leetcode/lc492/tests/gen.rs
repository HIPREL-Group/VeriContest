use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 10_000_000i32,
    ensures
        1 <= result <= 10_000_000,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 10_000_000 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 {
        // halve (stays >= 1)
        let h = seed / 2;
        if h >= 1 { h } else { 1 }
    } else if mutation_kind == 4 {
        // double (if in range)
        if seed <= 5_000_000 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        // min boundary
        1
    } else if mutation_kind == 6 {
        // max boundary
        10_000_000
    } else if mutation_kind == 7 {
        // min boundary
        1
    } else if mutation_kind == 8 {
        // clamp to small range (primes, small composites)
        if seed <= 100 { seed } else { (seed % 100) + 1 }
    } else if mutation_kind == 9 {
        // map to mid-range value
        (seed % 1000) + 5000
    } else {
        // fallback
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
    let count_goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Seed pool: example inputs and interesting values for rectangle factoring
    let seeds: Vec<i32> = vec![
        // Examples from description
        4, 37, 122122,
        // Boundary values
        1, 2, 10_000_000,
        // Perfect squares
        9, 16, 25, 36, 49, 64, 100, 144, 256, 1024, 10000, 1000000,
        // Primes (only one factoring: n × 1)
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 97, 9999991,
        // Near-perfect-squares
        3, 8, 15, 24, 35, 48, 63, 99,
        // Powers of 2
        2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192,
        // Highly composite numbers
        6, 12, 24, 60, 120, 360, 720, 1260, 2520, 5040,
        // Large values
        9_999_999, 9_999_998, 5_000_000, 7_654_321,
    ];

    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= count_goal { break; }
            let area = generate_test_case(s, mk);
            if seen.insert(area) {
                let output = Solution::construct_rectangle(area);
                writeln!(out, "{}", json!({
                    "input": {"area": area},
                    "output": output
                })).unwrap();
                count += 1;
            }
        }
        if count >= count_goal { break; }
    }

    // Fill remaining with random values + random mutations
    while count < count_goal {
        // Diverse size classes
        let s = match count % 5 {
            0 => rng.gen_range_i64(1, 10) as i32,              // tiny
            1 => rng.gen_range_i64(1, 1000) as i32,            // small
            2 => rng.gen_range_i64(1000, 100_000) as i32,      // medium
            3 => rng.gen_range_i64(100_000, 1_000_000) as i32, // large
            _ => rng.gen_range_i64(1_000_000, 10_000_000) as i32, // max
        };
        let mk = rng.gen_u8() % 11;
        let area = generate_test_case(s, mk);
        if seen.insert(area) {
            let output = Solution::construct_rectangle(area);
            writeln!(out, "{}", json!({
                "input": {"area": area},
                "output": output
            })).unwrap();
            count += 1;
        }
    }
}
