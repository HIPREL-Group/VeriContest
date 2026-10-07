use vstd::prelude::*;

verus! {

/// Copied from spec.rs — minimum steps to reduce n to 1.
pub open spec fn steps_to_one(n: int) -> int
    decreases n,
{
    if n <= 3 {
        if n <= 1 { 0 } else { n - 1 }
    } else if n % 2 == 0 {
        1 + steps_to_one(n / 2)
    } else {
        let t1 = (n + 1) / 2;
        let t2 = (n - 1) / 2;

        if t1 % 2 == 0 && t2 % 2 == 0 {
            2 + steps_to_one(if t1 <= t2 { t1 } else { t2 })
        } else if t1 % 2 == 0 {
            2 + steps_to_one(t1)
        } else {
            2 + steps_to_one(t2)
        }
    }
}

/// Proof that steps_to_one is non-negative for all n >= 1.
proof fn lemma_steps_to_one_nonneg(n: int)
    requires
        n >= 1,
    ensures
        steps_to_one(n) >= 0,
    decreases n,
{
    if n <= 3 {
        // base cases: steps_to_one returns 0 or n-1 >= 0
    } else if n % 2 == 0 {
        lemma_steps_to_one_nonneg(n / 2);
    } else {
        let t1 = (n + 1) / 2;
        let t2 = (n - 1) / 2;
        if t1 % 2 == 0 && t2 % 2 == 0 {
            if t1 <= t2 {
                lemma_steps_to_one_nonneg(t1);
            } else {
                lemma_steps_to_one_nonneg(t2);
            }
        } else if t1 % 2 == 0 {
            lemma_steps_to_one_nonneg(t1);
        } else {
            lemma_steps_to_one_nonneg(t2);
        }
    }
}

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= i32::MAX,
        0 <= steps_to_one(seed as int) < i32::MAX - 2,
    ensures
        1 <= result <= i32::MAX,
        0 <= steps_to_one(result as int) < i32::MAX - 2,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 {
        // boundary: smallest valid input
        1i32
    } else if mutation_kind == 2 {
        // small even
        2i32
    } else if mutation_kind == 3 {
        // small odd
        3i32
    } else if mutation_kind == 4 && seed % 2 == 0 && seed >= 4 {
        // halve: steps_to_one(seed) = 1 + steps_to_one(seed/2) when seed > 3 and even
        proof {
            let n = seed as int;
            assert(n > 3 && n % 2 == 0);
            // Verus unfolds: steps_to_one(n) == 1 + steps_to_one(n / 2)
            // So steps_to_one(n / 2) == steps_to_one(n) - 1 < i32::MAX - 2
            lemma_steps_to_one_nonneg(n / 2);
        }
        seed / 2
    } else {
        // fallback to identity
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
    use std::collections::HashSet;
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    // Seed pool: example inputs, powers of 2, boundary values, interesting odds
    let mut seeds: Vec<i32> = vec![
        // Example inputs from description
        8, 7, 4,
        // Base cases and small values
        1, 2, 3, 5, 6, 9, 10, 11, 12, 15, 16, 17,
        // Boundary
        i32::MAX, i32::MAX - 1, i32::MAX - 2,
        // Medium values
        100, 255, 256, 1000, 1023, 1024, 1025,
        // Large powers of 2
        65536, 1048576, 16777216, 1073741824,
    ];
    // Powers of 2: 1, 2, 4, ..., 2^30
    let mut p: i64 = 1;
    while p <= i32::MAX as i64 {
        seeds.push(p as i32);
        if p > 1 {
            seeds.push((p - 1) as i32);
            seeds.push((p + 1).min(i32::MAX as i64) as i32);
        }
        p *= 2;
    }

    // Deterministic pass: iterate seed pool × mutation kinds
    for &s in &seeds {
        for mk in 0..=4u8 {
            if emitted >= count {
                break;
            }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::integer_replacement(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                emitted += 1;
            }
        }
        if emitted >= count {
            break;
        }
    }

    // Random pass: fill remaining with random seeds + random mutations
    while emitted < count {
        // Mix of size classes
        let s = match rng.gen_u8() % 5 {
            0 => rng.gen_range_i64(1, 10) as i32,            // tiny
            1 => rng.gen_range_i64(1, 1000) as i32,          // small
            2 => rng.gen_range_i64(1, 1_000_000) as i32,     // medium
            3 => rng.gen_range_i64(1, 1_000_000_000) as i32, // large
            _ => rng.gen_range_i64(1, i32::MAX as i64) as i32, // full range
        };
        let mk = rng.gen_u8() % 5;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::integer_replacement(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            emitted += 1;
        }
    }
}
