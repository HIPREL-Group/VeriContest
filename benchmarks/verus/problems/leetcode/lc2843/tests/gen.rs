use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_low: i32, seed_high: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_low <= seed_high <= 10_000i32,
    ensures
        1 <= res.0 <= res.1 <= 10_000i32,
{
    let low = seed_low;
    let high = seed_high;

    if mutation_kind == 0 {
        // identity
        (low, high)
    } else if mutation_kind == 1 && low < high {
        // nudge low up
        (low + 1, high)
    } else if mutation_kind == 2 && high > low {
        // nudge high down
        (low, high - 1)
    } else if mutation_kind == 3 && low > 1 {
        // nudge low down
        (low - 1, high)
    } else if mutation_kind == 4 && high < 10_000 {
        // nudge high up
        (low, high + 1)
    } else if mutation_kind == 5 {
        // collapse to single element (low == high)
        (low, low)
    } else if mutation_kind == 6 {
        // collapse to single element (high == high)
        (high, high)
    } else if mutation_kind == 7 {
        // set low to 1
        (1, high)
    } else if mutation_kind == 8 {
        // set high to 10_000
        (low, 10_000)
    } else if mutation_kind == 9 {
        // full range
        (1, 10_000)
    } else if mutation_kind == 10 {
        // midpoint collapse
        let mid = low + (high - low) / 2;
        (mid, mid)
    } else if mutation_kind == 11 && low > 1 && high < 10_000 {
        // expand both directions
        (low - 1, high + 1)
    } else {
        // fallback: identity
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
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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
        (1, 100),
        (1200, 1230),
    ];

    for &(lo, hi) in &examples {
        if count >= goal { break; }
        if seen.insert((lo, hi)) {
            let result = Solution::count_symmetric_integers(lo, hi);
            writeln!(out, "{}", json!({"input": {"low": lo, "high": hi}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool: interesting (low, high) pairs
    let seeds: Vec<(i32, i32)> = vec![
        (1, 1), (1, 10_000), (10_000, 10_000),
        (1, 9), (10, 99), (100, 999), (1000, 9999),
        (10, 10), (99, 99), (1000, 1000), (9999, 9999),
        (11, 11), (22, 22), (55, 55),
        (1, 99), (10, 99), (1000, 9999),
        (1, 1000), (100, 10_000), (50, 5000),
        (1203, 1230), (1111, 1111), (5050, 5050),
        (9990, 10_000), (1, 2), (9999, 10_000),
    ];

    // Seed pool × mutation_kind
    for &(sl, sh) in &seeds {
        for mk in 0..num_mutations {
            if count >= goal { break; }
            let (low, high) = generate_test_case(sl, sh, mk);
            if seen.insert((low, high)) {
                let result = Solution::count_symmetric_integers(low, high);
                writeln!(out, "{}", json!({"input": {"low": low, "high": high}, "output": result})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < goal {
        let lo = rng.gen_range_i64(1, 10_000) as i32;
        let hi = rng.gen_range_i64(lo as i64, 10_000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (low, high) = generate_test_case(lo, hi, mk);
        if seen.insert((low, high)) {
            let result = Solution::count_symmetric_integers(low, high);
            writeln!(out, "{}", json!({"input": {"low": low, "high": high}, "output": result})).unwrap();
            count += 1;
        }
    }
}
