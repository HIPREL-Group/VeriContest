use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1i32 <= seed <= 1_000_000_000i32,
    ensures
        1i32 <= result <= 1_000_000_000i32,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 1_000_000_000 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 {
        // halve (clamped to at least 1)
        let h = seed / 2;
        if h < 1 { 1 } else { h }
    } else if mutation_kind == 4 {
        // double (clamped to max)
        if seed <= 500_000_000 {
            seed * 2
        } else {
            1_000_000_000
        }
    } else if mutation_kind == 5 {
        // min boundary
        1
    } else if mutation_kind == 6 {
        // max boundary
        1_000_000_000
    } else if mutation_kind == 7 {
        // near-min boundary
        2
    } else if mutation_kind == 8 {
        // near-max boundary
        999_999_999
    } else if mutation_kind == 9 {
        // mod-3 neighbor: round down to multiple of 3, clamp
        let r = seed % 3;
        let v = seed - r;
        if v < 1 { 1 } else { v }
    } else if mutation_kind == 10 {
        // mod-3 neighbor: round up to next multiple of 3, clamp
        let r = seed % 3;
        if r == 0 {
            seed
        } else {
            let v = seed + (3 - r);
            if v > 1_000_000_000 { seed } else { v }
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    // Example inputs from description.md
    let example_seeds: Vec<i32> = vec![5, 8];

    // Interesting seed pool
    let mut seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        12, 15, 18, 21, 24, 27, 30,
        100, 333, 999, 1000,
        999_999_999, 1_000_000_000,
        999_999_998, 999_999_997,
        500_000_000,
    ];
    seeds.extend_from_slice(&example_seeds);

    // Powers of 3
    let mut p: i64 = 3;
    while p <= 1_000_000_000 {
        seeds.push(p as i32);
        if p > 1 {
            seeds.push((p - 1).max(1) as i32);
            seeds.push((p + 1).min(1_000_000_000) as i32);
        }
        p *= 3;
    }

    // Iterate seed pool × mutations
    for &s in &seeds {
        for mk in 0..=11u8 {
            if total >= count { break; }
            let pf = generate_test_case(s, mk);
            if seen.insert(pf) {
                let output = Solution::max_nice_divisors(pf);
                writeln!(out, "{}", json!({
                    "input": {"primeFactors": pf},
                    "output": output
                })).unwrap();
                total += 1;
            }
        }
        if total >= count { break; }
    }

    // Fill remaining with random seeds
    while total < count {
        // Mix of size classes
        let s = match total % 5 {
            0 => rng.gen_range_i64(1, 10) as i32,
            1 => rng.gen_range_i64(1, 1000) as i32,
            2 => rng.gen_range_i64(1000, 1_000_000) as i32,
            3 => rng.gen_range_i64(1_000_000, 1_000_000_000) as i32,
            _ => rng.gen_range_i64(1, 1_000_000_000) as i32,
        };
        let mk = rng.gen_u8() % 12;
        let pf = generate_test_case(s, mk);
        if seen.insert(pf) {
            let output = Solution::max_nice_divisors(pf);
            writeln!(out, "{}", json!({
                "input": {"primeFactors": pf},
                "output": output
            })).unwrap();
            total += 1;
        }
    }
}
