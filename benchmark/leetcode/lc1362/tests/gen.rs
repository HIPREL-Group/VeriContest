use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 1_000_000_000i32,
    ensures
        1 <= result <= 1_000_000_000i32,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 1_000_000_000i32 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 {
        // double (if in range)
        if seed <= 500_000_000 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        // halve (at least 1)
        let h = seed / 2;
        if h >= 1 { h } else { 1 }
    } else if mutation_kind == 5 {
        // min boundary
        1
    } else if mutation_kind == 6 {
        // max boundary
        1_000_000_000i32
    } else if mutation_kind == 7 {
        // square root region: clamp to [1, 31623] (sqrt of 10^9 ~ 31622)
        if seed <= 31623 {
            seed
        } else {
            31623
        }
    } else if mutation_kind == 8 {
        // near max
        if seed > 999_999_000 {
            seed
        } else {
            999_999_001
        }
    } else if mutation_kind == 9 {
        // triple (if in range)
        if seed <= 333_333_333 {
            seed * 3
        } else {
            seed
        }
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
    let examples: Vec<i32> = vec![8, 123, 999];

    // Seed pool: interesting values for divisor problems
    let mut seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        100, 123, 999, 1000, 9999, 10000,
        999_999_999, 1_000_000_000,
        999_999_998, 999_999_000,
        500_000_000, 250_000_000,
        // Perfect squares minus 1 or 2 (interesting for divisor closeness)
        24, 35, 48, 99, 120, 168, 224, 288, 360,
        // Primes minus 1 or 2 (num+1 or num+2 is prime => only 1*p)
        3, 5, 11, 29, 97, 997, 9973,
    ];

    // Add example inputs
    for &e in &examples {
        if !seeds.contains(&e) {
            seeds.push(e);
        }
    }

    // Generate from seed pool × mutation kinds
    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let num = generate_test_case(s, mk);
            if seen.insert(num) {
                let output = Solution::closest_divisors(num);
                writeln!(out, "{}", json!({
                    "input": {"num": num},
                    "output": output
                })).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < goal {
        let s = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let mk = rng.gen_u8() % 11;
        let num = generate_test_case(s, mk);
        if seen.insert(num) {
            let output = Solution::closest_divisors(num);
            writeln!(out, "{}", json!({
                "input": {"num": num},
                "output": output
            })).unwrap();
            count += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
