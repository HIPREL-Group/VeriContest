use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_low: i32, seed_high: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        0 <= seed_low <= seed_high <= 1_000_000_000i32,
    ensures
        0 <= res.0 <= res.1 <= 1_000_000_000i32,
{
    let low = seed_low;
    let high = seed_high;

    if mutation_kind == 0 {
        (low, high)
    } else if mutation_kind == 1 && low < high {
        (low + 1, high)
    } else if mutation_kind == 2 && high < 1_000_000_000 {
        (low, high + 1)
    } else if mutation_kind == 3 && low > 0 {
        (low - 1, high)
    } else if mutation_kind == 4 && high > low {
        (low, high - 1)
    } else if mutation_kind == 5 {
        (low, low)
    } else if mutation_kind == 6 {
        (high, high)
    } else if mutation_kind == 7 {
        (0, high)
    } else if mutation_kind == 8 {
        (low, 1_000_000_000)
    } else if mutation_kind == 9 {
        (0, 1_000_000_000)
    } else if mutation_kind == 10 {
        let mid = low + (high - low) / 2;
        (low, mid)
    } else if mutation_kind == 11 {
        let mid = low + (high - low) / 2;
        (mid, high)
    } else if mutation_kind == 12 {
        (0, 0)
    } else {
        (low, high)
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
    let num_mutations: u8 = 13;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (3, 7),
        (8, 10),
    ];

    for &(lo, hi) in &examples {
        if count >= target_count { break; }
        let result = Solution::count_odds(lo, hi);
        if seen.insert((lo as i64, hi as i64)) {
            writeln!(out, "{}", json!({"input": {"low": lo, "high": hi}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool with interesting values
    let seeds: Vec<(i32, i32)> = vec![
        (0, 0), (0, 1), (1, 1), (0, 2), (1, 2), (2, 2),
        (0, 1_000_000_000), (1, 1_000_000_000),
        (999_999_999, 1_000_000_000), (1_000_000_000, 1_000_000_000),
        (0, 999_999_999), (0, 100), (100, 200),
        (500_000_000, 500_000_001), (500_000_000, 500_000_000),
        (1, 3), (2, 4), (0, 10), (10, 20),
        (99, 100), (100, 101), (999, 1000),
        (0, 1000), (0, 10000), (0, 100000),
        (123456, 789012), (1, 999_999_999),
    ];

    // Seed pool x mutation_kind
    for &(sl, sh) in &seeds {
        for mk in 0..num_mutations {
            if count >= target_count { break; }
            let (lo, hi) = generate_test_case(sl, sh, mk);
            if seen.insert((lo as i64, hi as i64)) {
                let result = Solution::count_odds(lo, hi);
                writeln!(out, "{}", json!({"input": {"low": lo, "high": hi}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target_count {
        let lo = rng.gen_range_i64(0, 1_000_000_000) as i32;
        let hi = rng.gen_range_i64(lo as i64, 1_000_000_000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (low, high) = generate_test_case(lo, hi, mk);
        if seen.insert((low as i64, high as i64)) {
            let result = Solution::count_odds(low, high);
            writeln!(out, "{}", json!({"input": {"low": low, "high": high}, "output": result})).unwrap();
            count += 1;
        }
    }
}
