use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1i32 <= seed <= 1_000_000_000i32,
    ensures
        1i32 <= result <= 1_000_000_000i32,
{
    if mutation_kind == 0 {
        seed                                              // identity
    } else if mutation_kind == 1 && seed < 1_000_000_000 {
        seed + 1                                          // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                          // nudge down
    } else if mutation_kind == 3 {
        if seed >= 1 && seed <= 500_000_000 {
            seed * 2                                      // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        if seed >= 2 {
            seed / 2                                      // halve
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        1                                                 // min boundary
    } else if mutation_kind == 6 {
        1_000_000_000                                     // max boundary
    } else if mutation_kind == 7 {
        if seed >= 1 && seed <= 999_999_999 {
            seed / 2 + 1                                  // halve rounded up
        } else {
            seed
        }
    } else if mutation_kind == 8 {
        if seed >= 3 {
            seed - 2                                      // nudge down by 2
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        if seed <= 999_999_998 {
            seed + 2                                      // nudge up by 2
        } else {
            seed
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
    let count_goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Example inputs from description.md
    let examples: Vec<i32> = vec![9, 1];

    // Seed pool: powers of 2, boundaries, and interesting values
    let mut seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        15, 16, 17, 31, 32, 33, 63, 64, 65,
        100, 127, 128, 255, 256, 500, 512, 1000, 1024,
        10_000, 100_000, 1_000_000, 10_000_000,
        100_000_000, 500_000_000, 999_999_999, 1_000_000_000,
    ];
    // Powers of 2 up to 10^9
    let mut p: i64 = 1;
    while p <= 1_000_000_000 {
        if !seeds.contains(&(p as i32)) {
            seeds.push(p as i32);
        }
        if p > 1 && !seeds.contains(&((p - 1) as i32)) {
            seeds.push((p - 1) as i32);
        }
        if p + 1 <= 1_000_000_000 && !seeds.contains(&((p + 1) as i32)) {
            seeds.push((p + 1) as i32);
        }
        p *= 2;
    }

    // First emit the example inputs
    for &n in &examples {
        if count >= count_goal { break; }
        if seen.insert(n) {
            let output = Solution::last_remaining(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Then iterate seed pool × mutation_kinds
    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= count_goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::last_remaining(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= count_goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < count_goal {
        let s = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::last_remaining(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
