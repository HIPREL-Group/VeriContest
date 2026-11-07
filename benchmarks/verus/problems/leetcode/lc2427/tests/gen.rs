use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: i32, seed_b: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_a <= 1000,
        1 <= seed_b <= 1000,
    ensures
        1 <= res.0 <= 1000,
        1 <= res.1 <= 1000,
{
    let a = if mutation_kind == 0 {
        // Identity
        seed_a
    } else if mutation_kind == 1 && seed_a < 1000 {
        // Nudge +1
        seed_a + 1
    } else if mutation_kind == 2 && seed_a > 1 {
        // Nudge -1
        seed_a - 1
    } else if mutation_kind == 3 && seed_a <= 500 {
        // Double
        seed_a * 2
    } else if mutation_kind == 4 {
        // Halve (at least 1)
        let h = seed_a / 2;
        if h < 1 { 1 } else { h }
    } else if mutation_kind == 5 {
        // Min boundary
        1
    } else if mutation_kind == 6 {
        // Max boundary
        1000
    } else {
        seed_a
    };

    let b = if mutation_kind == 7 {
        // Identity for b, vary a
        seed_b
    } else if mutation_kind == 8 && seed_b < 1000 {
        // Nudge b +1
        seed_b + 1
    } else if mutation_kind == 9 && seed_b > 1 {
        // Nudge b -1
        seed_b - 1
    } else if mutation_kind == 10 {
        // b = a (same value)
        a
    } else if mutation_kind == 11 {
        // Min boundary for b
        1
    } else if mutation_kind == 12 {
        // Max boundary for b
        1000
    } else {
        seed_b
    };

    (a, b)
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
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let num_mutations: u8 = 13;

    // Example inputs from description + boundary seeds
    let seeds: Vec<(i32, i32)> = vec![
        (12, 6),    // example 1
        (25, 30),   // example 2
        (1, 1),     // min-min
        (1000, 1000), // max-max
        (1, 1000),  // min-max
        (1000, 1),  // max-min
        (1, 2),
        (2, 1),
        (500, 500),
        (100, 200),
        (6, 12),
        (30, 25),
        (720, 360), // highly composite
        (997, 991), // primes
        (512, 256), // powers of 2
        (999, 1000),
        (2, 1000),
        (1000, 2),
        (7, 49),
        (100, 1),
    ];

    // Seed pool × mutation_kind
    for &(sa, sb) in &seeds {
        for mk in 0..num_mutations {
            if count >= target { break; }
            let (a, b) = generate_test_case(sa, sb, mk);
            if seen.insert((a, b)) {
                let result = Solution::common_factors(a, b);
                writeln!(out, "{}", json!({"input": {"a": a, "b": b}, "output": result})).unwrap();
                count += 1;
            }
        }
        if count >= target { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < target {
        let sa = rng.gen_range_i64(1, 1000) as i32;
        let sb = rng.gen_range_i64(1, 1000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (a, b) = generate_test_case(sa, sb, mk);
        if seen.insert((a, b)) {
            let result = Solution::common_factors(a, b);
            writeln!(out, "{}", json!({"input": {"a": a, "b": b}, "output": result})).unwrap();
            count += 1;
        }
    }
}
