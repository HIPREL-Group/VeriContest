use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_low: i32, seed_high: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        10 <= seed_low,
        seed_low <= seed_high,
        seed_high <= 1000000000i32,
    ensures
        10 <= res.0 <= res.1 <= 1000000000i32,
{
    if mutation_kind == 0 {
        (seed_low, seed_high)
    } else if mutation_kind == 1 && seed_low < seed_high {
        (seed_low + 1, seed_high)
    } else if mutation_kind == 2 && seed_low > 10 {
        (seed_low - 1, seed_high)
    } else if mutation_kind == 3 && seed_high < 1000000000 {
        (seed_low, seed_high + 1)
    } else if mutation_kind == 4 && seed_high > seed_low {
        (seed_low, seed_high - 1)
    } else if mutation_kind == 5 {
        (seed_low, seed_low)
    } else if mutation_kind == 6 {
        (10, seed_high)
    } else if mutation_kind == 7 {
        (seed_low, 1000000000)
    } else if mutation_kind == 8 {
        (10, 1000000000)
    } else if mutation_kind == 9 {
        let mid = seed_low + (seed_high - seed_low) / 2;
        (seed_low, mid)
    } else if mutation_kind == 10 {
        let mid = seed_low + (seed_high - seed_low) / 2;
        (mid, seed_high)
    } else if mutation_kind == 11 {
        (seed_high, seed_high)
    } else {
        (seed_low, seed_high)
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
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 12;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (100, 300),
        (1000, 13000),
    ];
    for &(lo, hi) in &examples {
        if count >= goal { break; }
        if seen.insert((lo as i64, hi as i64)) {
            let result = Solution::sequential_digits(lo, hi);
            writeln!(out, "{}", json!({"input": {"low": lo, "high": hi}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool: interesting boundary ranges
    let seeds: Vec<(i32, i32)> = vec![
        (10, 100),
        (10, 1000000000),
        (12, 12),
        (89, 89),
        (123456789, 123456789),
        (10, 10),
        (999999999, 1000000000),
        (10, 89),
        (12, 23456789),
        (100, 1000),
        (1000, 10000),
        (10000, 100000),
        (100000, 1000000),
        (1000000, 10000000),
        (10000000, 100000000),
        (100000000, 1000000000),
        (12, 89),
        (123, 789),
        (1234, 6789),
        (12345, 56789),
        (123456, 456789),
        (1234567, 3456789),
        (12345678, 23456789),
        (56, 67),
        (45, 456),
        (78, 789),
        (34, 345),
    ];

    // Seed pool × mutation_kind
    for &(sl, sh) in &seeds {
        for mk in 0..num_mutations {
            if count >= goal { break; }
            let (low, high) = generate_test_case(sl, sh, mk);
            if seen.insert((low as i64, high as i64)) {
                let result = Solution::sequential_digits(low, high);
                writeln!(out, "{}", json!({"input": {"low": low, "high": high}, "output": result})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < goal {
        let lo = rng.gen_range_i64(10, 999999999) as i32;
        let hi = rng.gen_range_i64(lo as i64, 1000000000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (low, high) = generate_test_case(lo, hi, mk);
        if seen.insert((low as i64, high as i64)) {
            let result = Solution::sequential_digits(low, high);
            writeln!(out, "{}", json!({"input": {"low": low, "high": high}, "output": result})).unwrap();
            count += 1;
        }
    }
}
