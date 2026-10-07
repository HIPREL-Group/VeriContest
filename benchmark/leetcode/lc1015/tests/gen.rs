use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 100_000i32,
    ensures
        1 <= result <= 100_000i32,
{
    if mutation_kind == 0 {
        seed  // identity
    } else if mutation_kind == 1 && seed < 100_000 {
        seed + 1  // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1  // nudge down
    } else if mutation_kind == 3 && seed <= 50_000 {
        seed * 2  // double
    } else if mutation_kind == 4 {
        // halve, clamp to >= 1
        let h = seed / 2;
        if h >= 1 { h } else { 1 }
    } else if mutation_kind == 5 {
        1  // minimum
    } else if mutation_kind == 6 {
        100_000  // maximum
    } else if mutation_kind == 7 {
        // square root region
        let s = seed / 100;
        if s >= 1 { s } else { 1 }
    } else if mutation_kind == 8 {
        // mod 10 region: interesting for repunit divisibility
        let m = seed % 1000;
        if m >= 1 { m } else { 1 }
    } else {
        seed  // fallback
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
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let num_mutations: u8 = 9;

    // Example inputs from description
    let examples: Vec<i32> = vec![1, 2, 3];

    for &k in &examples {
        if count >= target_count { break; }
        if seen.insert(k) {
            let output = Solution::smallest_repunit_div_by_k(k);
            writeln!(out, "{}", json!({"input": {"k": k}, "output": output})).unwrap();
            count += 1;
        }
    }

    let seeds: Vec<i32> = vec![
        // Small values
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        // Multiples of 2 and 5 (should return -1 since repunits are odd and not divisible by 5)
        2, 4, 5, 6, 8, 10, 12, 14, 15, 16, 18, 20, 25, 50, 100,
        // Odd numbers not divisible by 5 (should have solutions)
        1, 3, 7, 9, 11, 13, 17, 19, 21, 23, 27, 29, 31, 33, 37, 39,
        // Powers of various bases
        3, 9, 27, 81, 243, 729, 2187,
        7, 49, 343, 2401, 16807,
        11, 121, 1331, 14641,
        // Boundaries
        1, 100_000, 99_999, 99_998, 99_997,
        // Round numbers
        100, 1000, 10000, 50000,
        // Primes
        41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
        // Repunit-related: 111 = 3*37, 1111 = 11*101
        37, 101, 111, 1111, 239, 4649,
    ];

    // Seed pool × mutation_kind
    for &s in &seeds {
        for mk in 0..num_mutations {
            if count >= target_count { break; }
            let k = generate_test_case(s, mk);
            if seen.insert(k) {
                let output = Solution::smallest_repunit_div_by_k(k);
                writeln!(out, "{}", json!({"input": {"k": k}, "output": output})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target_count {
        let s = match rng.next_u64() % 5 {
            0 => rng.gen_range_i64(1, 10) as i32,         // tiny
            1 => rng.gen_range_i64(1, 100) as i32,        // small
            2 => rng.gen_range_i64(1, 1000) as i32,       // medium
            3 => rng.gen_range_i64(1, 10000) as i32,      // large
            _ => rng.gen_range_i64(1, 100_000) as i32,    // full range
        };
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let k = generate_test_case(s, mk);
        if seen.insert(k) {
            let output = Solution::smallest_repunit_div_by_k(k);
            writeln!(out, "{}", json!({"input": {"k": k}, "output": output})).unwrap();
            count += 1;
        }
    }
}
